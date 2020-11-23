package compression

import (
	"bytes"
	"crypto/sha256"
	"encoding/base64"
	"encoding/binary"
	"encoding/json"
	"fmt"
	"io"
	"time"

	"github.com/klauspost/compress/zstd"
	"github.com/vbatts/tar-split/archive/tar"
)

type chunkedZstdWriter struct {
	tarSplitOut *io.PipeWriter
	tarSplitErr chan error
}

func (w chunkedZstdWriter) Close() error {
	err := <-w.tarSplitErr
	if err != nil {
		w.tarSplitOut.Close()
		return err
	}
	return w.tarSplitOut.Close()
}

func (w chunkedZstdWriter) Write(p []byte) (int, error) {
	select {
	case err := <-w.tarSplitErr:
		w.tarSplitOut.Close()
		return 0, err
	default:
		return w.tarSplitOut.Write(p)
	}
}

type FileMetadata struct {
	Type        string            `json:"type"`
	Name        string            `json:"name"`
	Linkname    string            `json:"linkName,omitempty"`
	Mode        int64             `json:"mode,omitempty"`
	Size        int64             `json:"size"`
	Uid         int               `json:"uid"`
	Gid         int               `json:"gid"`
	ModTime     time.Time         `json:"modTime"`
	AccessTime  time.Time         `json:"accessTime"`
	ChangeTime  time.Time         `json:"changeTime"`
	Devmajor    int64             `json:"devMajor"`
	Devminor    int64             `json:"devMinor"`
	Xattrs      map[string]string `json:"xattrs,omitempty"`
	Checksum    string            `json:"checksum,omitempty"`
	StartOffset int64             `json:"startOffset,omitempty"`
	EndOffset   int64             `json:"endOffset,omitempty"`
}

func getType(t byte) (string, error) {
	switch t {
	case tar.TypeReg, tar.TypeRegA:
		return "REG", nil
	case tar.TypeLink:
		return "LINK", nil
	case tar.TypeChar:
		return "CHAR", nil
	case tar.TypeBlock:
		return "BLOCK", nil
	case tar.TypeDir:
		return "DIR", nil
	case tar.TypeFifo:
		return "FIFO", nil
	case tar.TypeSymlink:
		return "SYMLINK", nil
	}
	return "", fmt.Errorf("unknown tarball type: %v", t)
}

func TypeToTarType(t string) (byte, error) {
	switch t {
	case "REG":
		return tar.TypeReg, nil
	case "LINK":
		return tar.TypeLink, nil
	case "CHAR":
		return tar.TypeChar, nil
	case "BLOCK":
		return tar.TypeBlock, nil
	case "DIR":
		return tar.TypeDir, nil
	case "FIFO":
		return tar.TypeFifo, nil
	case "SYMLINK":
		return tar.TypeSymlink, nil
	}
	return 0, fmt.Errorf("unknown type: %v", t)
}

// sizeCounter is an io.Writer which only counts the total size of its input.
type sizeCounter struct{ size int64 }

func (c *sizeCounter) Write(p []byte) (int, error) {
	c.size += int64(len(p))
	return len(p), nil
}

var (
	// when the zstd decoder encounters a skippable frame + 1 byte for the size, it
	// will ignore it.
	// https://tools.ietf.org/html/rfc8478#section-3.1.2
	skippableFrameMagic = []byte{0x50, 0x2a, 0x4d, 0x18}
)

func isZstdSkippableFrameMagic(data []byte) bool {
	if len(data) < 4 {
		return false
	}
	return bytes.Equal(skippableFrameMagic, data[:4])
}

func ReadChunkedZstdManifest(blobStream io.ReaderAt, blobSize int64) ([]byte, error) {
	footerSize := int64(32)
	if blobSize <= footerSize {
		return nil, fmt.Errorf("blob too small")
	}

	footer := make([]byte, footerSize)
	_, err := blobStream.ReadAt(footer, blobSize-footerSize)
	if err != nil && err != io.EOF {
		return nil, err
	}

	frameLen := binary.LittleEndian.Uint32(footer[4:8])
	offset := binary.LittleEndian.Uint64(footer[8:16])
	length := binary.LittleEndian.Uint64(footer[16:24])
	lengthUncompressed := binary.LittleEndian.Uint64(footer[24:32])

	if !isZstdSkippableFrameMagic(footer) || frameLen != 24 {
		return nil, fmt.Errorf("unknown chunked zstd footer")
	}

	// set a reasonable limit
	if length > (1<<20)*50 {
		return nil, fmt.Errorf("manifest too big")
	}
	if lengthUncompressed > (1<<20)*50 {
		return nil, fmt.Errorf("manifest too big")
	}

	manifest := make([]byte, length)
	_, err = blobStream.ReadAt(manifest, int64(offset))
	if err != nil && err != io.EOF {
		return nil, err
	}

	decoder, err := zstd.NewReader(nil)
	if err != nil {
		return nil, err
	}
	defer decoder.Close()

	b := make([]byte, 0, lengthUncompressed)
	if decoded, err := decoder.DecodeAll(manifest, b); err == nil {
		return decoded, nil
	}

	return manifest, nil
}

func appendZstdSkippableFrame(dest io.Writer, data []byte) error {
	if _, err := dest.Write(skippableFrameMagic); err != nil {
		return err
	}

	var size []byte = make([]byte, 4)
	binary.LittleEndian.PutUint32(size, uint32(len(data)))
	if _, err := dest.Write(size); err != nil {
		return err
	}
	if _, err := dest.Write(data); err != nil {
		return err
	}

	return nil
}

func writeZstdChunkedManifest(dest io.Writer, offset *sizeCounter, metadata []FileMetadata, level int) error {
	// 8 is the size of the zstd skippable frame header + the frame size
	manifestOffset := uint64(offset.size) + 8

	// Generate the manifest
	manifest, err := json.Marshal(metadata)
	if err != nil {
		return err
	}

	var compressedBuffer bytes.Buffer
	zstdWriter, err := zstdWriterWithLevel(&compressedBuffer, level)
	if err != nil {
		return err
	}
	if _, err := zstdWriter.Write(manifest); err != nil {
		zstdWriter.Close()
		return err
	}
	if err := zstdWriter.Close(); err != nil {
		return err
	}

	compressedManifest := compressedBuffer.Bytes()

	if err := appendZstdSkippableFrame(dest, compressedManifest); err != nil {
		return err
	}

	// Store the offset to the manifest and its size in LE order
	var manifestDataLE []byte = make([]byte, 24)
	binary.LittleEndian.PutUint64(manifestDataLE, manifestOffset)
	binary.LittleEndian.PutUint64(manifestDataLE[8:], uint64(len(compressedManifest)))
	binary.LittleEndian.PutUint64(manifestDataLE[16:], uint64(len(manifest)))

	return appendZstdSkippableFrame(dest, manifestDataLE)
}

func writeZstdChunkedStream(destFile io.Writer, r *io.PipeReader, level int) error {
	// total written so far.  Used to retrieve partial offsets in the file
	sizeCounter := &sizeCounter{}

	dest := io.MultiWriter(destFile, sizeCounter)

	tr := tar.NewReader(r)
	tr.RawAccounting = true

	buf := make([]byte, 4096)

	zstdWriter, err := zstdWriterWithLevel(dest, level)
	if err != nil {
		return err
	}
	defer func() {
		if zstdWriter != nil {
			zstdWriter.Close()
			zstdWriter.Flush()
		}
	}()

	restartCompression := func() (int64, error) {
		var offset int64
		if zstdWriter != nil {
			if err := zstdWriter.Close(); err != nil {
				return 0, err
			}
			if err := zstdWriter.Flush(); err != nil {
				return 0, err
			}
			offset = sizeCounter.size
			zstdWriter.Reset(dest)
		}
		return offset, nil
	}

	var metadata []FileMetadata
	for {
		hdr, err := tr.Next()
		if err != nil {
			if err == io.EOF {
				break
			}
			return err
		}

		if _, err := zstdWriter.Write(tr.RawBytes()); err != nil {
			return err
		}

		payloadChecksum := sha256.New()
		payloadDest := io.MultiWriter(payloadChecksum, zstdWriter)

		// Now handle the payload, if any
		var startOffset, endOffset int64
		var checksum []byte
		for {
			read, errRead := tr.Read(buf)
			if errRead != nil && errRead != io.EOF {
				return err
			}

			// restart the compression only if there is
			// a payload.
			if read > 0 {
				if startOffset == 0 {
					startOffset, err = restartCompression()
					if err != nil {
						return err
					}
				}
				_, err := payloadDest.Write(buf[:read])
				if err != nil {
					return err
				}
			}
			if errRead == io.EOF {
				if startOffset > 0 {
					endOffset, err = restartCompression()
					if err != nil {
						return err
					}
					checksum = payloadChecksum.Sum(nil)
				}
				break
			}
		}

		typ, err := getType(hdr.Typeflag)
		if err != nil {
			return err
		}
		xattrs := make(map[string]string)
		for k, v := range hdr.Xattrs {
			xattrs[k] = base64.StdEncoding.EncodeToString([]byte(v))
		}
		m := FileMetadata{
			Type:        typ,
			Name:        hdr.Name,
			Linkname:    hdr.Linkname,
			Mode:        hdr.Mode,
			Size:        hdr.Size,
			Uid:         hdr.Uid,
			Gid:         hdr.Gid,
			ModTime:     hdr.ModTime,
			AccessTime:  hdr.AccessTime,
			ChangeTime:  hdr.ChangeTime,
			Devmajor:    hdr.Devmajor,
			Devminor:    hdr.Devminor,
			Xattrs:      xattrs,
			Checksum:    fmt.Sprintf("%x", checksum),
			StartOffset: startOffset,
			EndOffset:   endOffset,
		}
		metadata = append(metadata, m)
	}

	if err := zstdWriter.Close(); err != nil {
		return err
	}
	if err := zstdWriter.Flush(); err != nil {
		return err
	}
	zstdWriter = nil

	return writeZstdChunkedManifest(dest, sizeCounter, metadata, level)
}

// chunkedZstdWriterWithLevel writes a zstd compressed tarball where each file is
// compressed separately so it can be addressed separately.  Idea based on CRFS:
// https://github.com/google/crfs
// The difference with CRFS is that the zstd compression is used instead of gzip.
// The reason for it is that zstd supports embedding metadata ignored by the decoder
// as part of the compressed stream.
// A manifest json file with all the metadata is appended at the end of the tarball
// stream, using zstd skippable frames.
// The final file will look like:
// [FILE_1][FILE_2]..[FILE_N][SKIPPABLE FRAME 1][SKIPPABLE FRAME 2]
// Where:
// [FILE_N]: [ZSTD HEADER][TAR HEADER][PAYLOAD FILE_N][ZSTD FOOTER]
// [SKIPPABLE FRAME 1]: [ZSTD SKIPPABLE FRAME, SIZE=MANIFEST LENGTH][MANIFEST]
// [SKIPPABLE FRAME 2]: [ZSTD SKIPPABLE FRAME, SIZE=16][MANIFEST_OFFSET][MANIFEST_LENGTH][MANIFEST_LENGTH_UNCOMPRESSED]
// MANIFEST_OFFSET, MANIFEST_LENGTH and MANIFEST_LENGTH_UNCOMPRESSED are 64 bits unsigned in little endian format.
func chunkedZstdWriterWithLevel(out io.Writer, level int) (io.WriteCloser, error) {
	ch := make(chan error, 1)
	r, w := io.Pipe()

	go func() {
		defer close(ch)
		ch <- writeZstdChunkedStream(out, r, level)
	}()

	return chunkedZstdWriter{
		tarSplitOut: w,
		tarSplitErr: ch,
	}, nil
}

// chunkedZstdCompressor is a CompressorFunc for the zstd compression algorithm.
func chunkedZstdCompressor(r io.Writer, level *int) (io.WriteCloser, error) {
	if level == nil {
		l := 3
		level = &l
	}
	return chunkedZstdWriterWithLevel(r, *level)
}
