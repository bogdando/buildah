// +build !containers_image_storage_stub

package storage

import (
	archivetar "archive/tar"
	"bufio"
	"context"
	"crypto/sha256"
	"encoding/base64"
	"encoding/json"
	"fmt"
	"io"
	"mime"
	"mime/multipart"
	"os"
	"path/filepath"
	"strings"
	"syscall"
	"time"

	"github.com/containers/image/v5/docker"
	"github.com/containers/image/v5/pkg/compression"
	"github.com/containers/image/v5/types"
	"github.com/containers/storage/drivers"
	"github.com/containers/storage/drivers/copy"
	"github.com/containers/storage/pkg/archive"
	"github.com/containers/storage/pkg/idtools"
	"github.com/containers/storage/pkg/system"
	securejoin "github.com/cyphar/filepath-securejoin"
	"github.com/klauspost/compress/zstd"
	"github.com/pkg/errors"
	"github.com/sirupsen/logrus"
	"github.com/vbatts/tar-split/archive/tar"
)

type DirectDiffInput struct {
	stream         types.ImageSourceSeekable
	store          *storageImageDestination
	manifest       []byte
	ctx            context.Context
	srcInfo        types.BlobInfo
	layersMetadata map[string][]compression.FileMetadata
	layersTarget   map[string]string
}

func timeToTimespec(time time.Time) (ts syscall.Timespec) {
	if time.IsZero() {
		// Return UTIME_OMIT special value
		ts.Sec = 0
		ts.Nsec = ((1 << 30) - 2)
		return
	}
	return syscall.NsecToTimespec(time.UnixNano())
}

type fileModeWrapper struct {
	st   os.FileInfo
	mode os.FileMode
}

func (f *fileModeWrapper) Name() string {
	return f.st.Name()
}

func (f *fileModeWrapper) Size() int64 {
	return f.st.Size()
}

func (f *fileModeWrapper) Mode() os.FileMode {
	return f.mode
}

func (f *fileModeWrapper) ModTime() time.Time {
	return f.st.ModTime()
}

func (f *fileModeWrapper) IsDir() bool {
	return f.st.IsDir()
}

func (f *fileModeWrapper) Sys() interface{} {
	return f.st.Sys()
}

func copyFileContent(src, dest string, missingDirsMode, mode os.FileMode) (int64, error) {
	parent := filepath.Dir(dest)
	if _, err := os.Stat(parent); err != nil && os.IsNotExist(err) {
		if err := os.MkdirAll(parent, missingDirsMode); err != nil {
			return -1, err
		}
	}

	st, err := os.Stat(src)
	if err != nil {
		return -1, err
	}

	copyWithFileRange, copyWithFileClone := true, true

	stWrapped := fileModeWrapper{
		st:   st,
		mode: mode,
	}

	err = copy.CopyRegular(src, dest, &stWrapped, &copyWithFileRange, &copyWithFileClone)
	return st.Size(), err
}

func prepareOtherLayersCache(layersMetadata map[string][]compression.FileMetadata) map[string]map[string]*compression.FileMetadata {
	maps := make(map[string]map[string]*compression.FileMetadata)

	for layerID, v := range layersMetadata {
		r := make(map[string]*compression.FileMetadata)
		for i := range v {
			r[v[i].Checksum] = &v[i]
		}
		maps[layerID] = r
	}
	return maps
}

func findFileInOtherLayers(file compression.FileMetadata, layersMetadata map[string]map[string]*compression.FileMetadata, layersTarget map[string]string, target string, missingDirsMode, mode os.FileMode) (bool, int64, error) {
	// this is ugly, needs to be indexed
	for layerID, checksums := range layersMetadata {
		m, found := checksums[file.Checksum]
		if !found {
			continue
		}

		source, ok := layersTarget[layerID]
		if !ok {
			continue
		}

		sourceFile, err := securejoin.SecureJoin(source, m.Name)
		if err != nil {
			continue
		}

		written, err := copyFileContent(sourceFile, target, missingDirsMode, mode)
		if err != nil {
			continue
		}
		return true, written, nil
	}
	return false, 0, nil
}

func findHostFile(file compression.FileMetadata, target string, missingDirsMode, mode os.FileMode) (bool, int64, error) {
	hostContentChecksum := sha256.New()

	sourceFile := filepath.Join("/", file.Name)

	f, err := os.Open(sourceFile)
	if err != nil {
		return false, 0, nil
	}
	defer f.Close()

	if _, err := io.Copy(hostContentChecksum, f); err != nil {
		return false, 0, nil
	}

	checksum := fmt.Sprintf("%x", hostContentChecksum.Sum(nil))

	if checksum != file.Checksum {
		return false, 0, nil
	}

	written, err := copyFileContent(sourceFile, target, missingDirsMode, mode)
	if err != nil {
		return false, 0, nil
	}

	return true, written, nil
}

func maybeDoIDRemap(manifest []compression.FileMetadata, options *archive.TarOptions) error {
	if options.ChownOpts == nil && len(options.UIDMaps) == 0 || len(options.GIDMaps) == 0 {
		return nil
	}

	idMappings := idtools.NewIDMappingsFromMaps(options.UIDMaps, options.GIDMaps)

	for i := range manifest {
		if options.ChownOpts != nil {
			manifest[i].Uid = options.ChownOpts.UID
			manifest[i].Gid = options.ChownOpts.GID
		} else {
			pair := idtools.IDPair{
				UID: manifest[i].Uid,
				GID: manifest[i].Gid,
			}
			var err error
			manifest[i].Uid, manifest[i].Gid, err = idMappings.ToContainer(pair)
			if err != nil {
				return err
			}
		}
	}
	return nil
}

func createFileFromZstdStream(path string, reader io.Reader, missingDirsMode os.FileMode, copyBuffer []byte) (err error) {
	parent := filepath.Dir(path)
	if _, err := os.Stat(parent); err != nil && os.IsNotExist(err) {
		if err := os.MkdirAll(parent, missingDirsMode); err != nil {
			return err
		}
	}
	file, err := os.OpenFile(path, os.O_CREATE|os.O_TRUNC|os.O_WRONLY|os.O_EXCL, 0600)
	if err != nil {
		return err
	}
	defer func() {
		err2 := file.Close()
		if err == nil {
			err = err2
		}
	}()

	z, err := zstd.NewReader(reader)
	if err != nil {
		return err
	}
	defer z.Close()

	_, err = io.CopyBuffer(file, z, copyBuffer)
	return
}

func storeMissingFiles(stream io.ReadCloser, contentType string, dest string, missingFiles []compression.FileMetadata, missingChunks []types.ImageSourceChunk, missingDirsMode os.FileMode, copyFileBuffer []byte) error {
	mediaType, params, err := mime.ParseMediaType(contentType)
	if err != nil {
		return err
	}
	if !strings.HasPrefix(mediaType, "multipart/") {
		if len(missingFiles) != 1 {
			return errors.Errorf("invalid response, no multipart for multiple files")
		}
		cleanedPath, err := securejoin.SecureJoin(dest, missingFiles[0].Name)
		if err != nil {
			return err
		}

		if err := createFileFromZstdStream(cleanedPath, stream, missingDirsMode, copyFileBuffer); err != nil {
			return err
		}
	} else {
		boundary, found := params["boundary"]
		if !found {
			return errors.Errorf("boundary param not found")
		}

		mr := multipart.NewReader(bufio.NewReaderSize(stream, 1<<20), boundary)
		mf := 0
		for {
			p, err := mr.NextPart()
			if err == io.EOF {
				break
			}
			if err != nil {
				return err
			}

			if mf == len(missingFiles) {
				return errors.Errorf("too many chunks returned")
			}
			missingFile := missingFiles[mf]
			mf++

			cleanedPath, err := securejoin.SecureJoin(dest, missingFile.Name)
			if err != nil {
				p.Close()
				return err
			}

			if err := createFileFromZstdStream(cleanedPath, p, missingDirsMode, copyFileBuffer); err != nil {
				p.Close()
				return err
			}
			p.Close()
		}
	}
	return nil
}

func retrieveMissingFiles(input *DirectDiffInput, dest string, missingFiles []compression.FileMetadata, missingChunks []types.ImageSourceChunk, missingDirsMode os.FileMode) error {
	// Avoid creating multiple buffers with io.Copy and use a sane size.
	copyFileBuffer := make([]byte, 1<<20)

	// Arbitrary limit to avoid invalid http range requests
	toRequest := 8192

	// There are some missing files.  Prepare a multirange request for the missing chunks.
	for len(missingChunks) > 0 {
		var stream io.ReadCloser
		var contentType string
		var err error

		if len(missingChunks) < toRequest {
			toRequest = len(missingChunks)
		}

		for stream == nil {
			stream, contentType, err = input.stream.GetBlobAt(input.ctx, input.srcInfo, missingChunks[:toRequest])
			if err != nil {
				if _, ok := err.(docker.ErrBadRequest); ok {
					// If the server cannot handle at least 1024 chunks in a single request, just give up.
					if toRequest < 1024 {
						return err
					}

					// Try shortening the number of requested ranges
					toRequest = toRequest / 2
					continue
				}
				return err
			}
		}

		if err := storeMissingFiles(stream, contentType, dest, missingFiles[:toRequest], missingChunks[:toRequest], missingDirsMode, copyFileBuffer); err != nil {
			stream.Close()
			return err
		}
		if err := stream.Close(); err != nil {
			return err
		}

		missingChunks = missingChunks[toRequest:]
		missingFiles = missingFiles[toRequest:]
	}

	return nil
}

func chunkedZstdDiffer(data interface{}, dest string, options *archive.TarOptions) (graphdriver.DriverWithDifferOutput, error) {
	output := graphdriver.DriverWithDifferOutput{}

	input, ok := data.(*DirectDiffInput)
	if !ok {
		return output, errors.Errorf("internal error")
	}

	// Generate the manifest
	var manifest []compression.FileMetadata
	if err := json.Unmarshal(input.manifest, &manifest); err != nil {
		return output, err
	}

	whiteoutConverter := archive.GetWhiteoutConverter(options.WhiteoutFormat, options.WhiteoutData)

	var missingFiles []compression.FileMetadata
	var missingChunks []types.ImageSourceChunk
	cleanedPaths := make(map[*compression.FileMetadata]string)

	if err := maybeDoIDRemap(manifest, options); err != nil {
		return output, err
	}

	otherLayersCache := prepareOtherLayersCache(input.layersMetadata)

	missingDirsMode := os.FileMode(0700)

	missingChunksSize, totalChunksSize := int64(0), int64(0)
	for i, r := range manifest {
		mode := os.FileMode(r.Mode)

		t, err := compression.TypeToTarType(r.Type)
		if err != nil {
			return output, err
		}

		cleanedPath, err := securejoin.SecureJoin(dest, r.Name)
		if err != nil {
			return output, err
		}

		if whiteoutConverter != nil {
			hdr := archivetar.Header{
				Typeflag: t,
				Name:     r.Name,
				Linkname: r.Linkname,
				Size:     r.Size,
				Mode:     r.Mode,
				Uid:      r.Uid,
				Gid:      r.Gid,
			}
			writeFile, err := whiteoutConverter.ConvertRead(&hdr, cleanedPath)
			if err != nil {
				return output, err
			}
			if !writeFile {
				continue
			}
		}

		cleanedPaths[&manifest[i]] = cleanedPath

		if r.Size == 0 {
			if t == tar.TypeReg {
				parent := filepath.Dir(cleanedPath)
				if _, err := os.Stat(parent); err != nil && os.IsNotExist(err) {
					if err := os.MkdirAll(parent, missingDirsMode); err != nil {
						return output, err
					}
				}

				file, err := os.OpenFile(cleanedPath, os.O_CREATE|os.O_TRUNC|os.O_WRONLY|os.O_EXCL, mode)
				if err != nil {
					return output, err
				}
				file.Close()
			}

			continue
		}

		totalChunksSize += r.Size

		found, _, err := findFileInOtherLayers(r, otherLayersCache, input.layersTarget, cleanedPath, missingDirsMode, mode)
		if err != nil {
			return output, err
		}
		if found {
			continue
		}

		found, _, err = findHostFile(r, cleanedPath, missingDirsMode, mode)
		if err != nil {
			return output, err
		}
		if found {
			continue
		}

		missingChunksSize += r.Size
		if t == tar.TypeReg {
			missingFiles = append(missingFiles, r)
			missingChunks = append(missingChunks, types.ImageSourceChunk{
				Offset: uint64(r.StartOffset),
				Length: uint64(r.EndOffset - r.StartOffset),
			})
		}
	}

	// There are some missing files.  Prepare a multirange request for the missing chunks.
	if err := retrieveMissingFiles(input, dest, missingFiles, missingChunks, missingDirsMode); err != nil {
		return output, err
	}

	if totalChunksSize > 0 {
		logrus.Debugf("Missing %d bytes out of %d (%.2f %%)", missingChunksSize, totalChunksSize, float32(missingChunksSize*100.0)/float32(totalChunksSize))
	}
	for i, r := range manifest {
		mode := os.FileMode(r.Mode)

		cleanedPath, found := cleanedPaths[&manifest[i]]
		if !found {
			continue
		}
		t, err := compression.TypeToTarType(r.Type)
		if err != nil {
			return output, err
		}
		switch t {
		case tar.TypeReg:
			// must be already created
		case tar.TypeDir:
			if err := os.MkdirAll(cleanedPath, mode); err != nil {
				return output, err
			}
		case tar.TypeLink:
			targetPath, err := securejoin.SecureJoin(dest, r.Linkname)
			if err != nil {
				return output, err
			}
			if err := os.Link(targetPath, cleanedPath); err != nil {
				return output, err
			}
		case tar.TypeSymlink:
			if err := os.Symlink(r.Linkname, cleanedPath); err != nil {
				return output, err
			}
		case tar.TypeChar:
			fallthrough
		case tar.TypeBlock:
			fallthrough
		case tar.TypeFifo:
			continue
		}

		if t != tar.TypeSymlink {
			if err := os.Lchown(cleanedPath, r.Uid, r.Gid); err != nil {
				if !options.IgnoreChownErrors {
					return output, err
				}
			}
			for k, v := range r.Xattrs {
				data, err := base64.StdEncoding.DecodeString(v)
				if err != nil {
					return output, err
				}
				if err := system.Lsetxattr(cleanedPath, k, data, 0); err != nil {
					return output, err
				}

			}
			ts := []syscall.Timespec{timeToTimespec(r.AccessTime), timeToTimespec(r.ModTime)}
			if err := system.LUtimesNano(cleanedPath, ts); err != nil && err != system.ErrNotSupportedPlatform {
				return output, err
			}
			// File/dirs must be already created with the correct mode, but we must make sure the setuid/setgid
			// is set.
			if mode&(os.ModeSetuid|os.ModeSetgid) != 0 {
				if err := os.Chmod(cleanedPath, mode); err != nil {
					return output, err
				}
			}
		}
	}
	return output, nil
}
