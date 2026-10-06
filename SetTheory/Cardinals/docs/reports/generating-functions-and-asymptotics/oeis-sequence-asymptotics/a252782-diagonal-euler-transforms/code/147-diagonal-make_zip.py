#!/usr/bin/env python3
"""Create the fixed Report147 source archive; never recurse or overwrite."""
import argparse
import hashlib
import os
from pathlib import Path
import stat
import sys
import zipfile

FILES = (
    'README.md', 'Report147.pdf', 'Report147.tex', 'build_pdf.py', 'make_zip.py',
    'companion/README.md', 'companion/certificate.json', 'companion/certificate.py',
    'companion/crossover.py', 'companion/diagonal_euler.py', 'companion/fixtures.py',
    'companion/tests/test_exact.py', 'companion/tests/test_crossover.py',
)
STAMP = (2026, 10, 3, 0, 0, 0)


def new_output_path(raw):
    path = Path(raw)
    if '..' in path.parts:
        raise ValueError('parent traversal in output is refused')
    path = Path(os.path.abspath(path))
    for part in [path] + list(path.parents):
        if part.is_symlink():
            raise ValueError('symlink output paths are refused')
    if path.exists():
        raise FileExistsError('output file already exists')
    if not path.parent.is_dir():
        raise FileNotFoundError('output parent must already exist')
    return path


def payloads(root):
    result = {}
    for name in sorted(FILES):
        path = root / name
        for part in [path] + list(path.parents):
            if part == root.parent:
                break
            if part.is_symlink():
                raise ValueError('symlink package input is refused: ' + name)
        if not path.is_file() or not stat.S_ISREG(path.stat().st_mode):
            raise ValueError('missing regular package input: ' + name)
        result[name] = path.read_bytes()
    lines = [hashlib.sha256(data).hexdigest() + '  ' + name
             for name, data in sorted(result.items())]
    result['SHA256SUMS'] = ('\n'.join(lines) + '\n').encode('ascii')
    return result


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', required=True, help='new ZIP file; parent must exist')
    args = parser.parse_args(argv)
    output = new_output_path(args.output)
    data = payloads(Path(__file__).resolve().parent)
    # Exclusive creation prevents overwriting even if a competing process acts.
    with output.open('xb') as raw:
        with zipfile.ZipFile(raw, 'w', compression=zipfile.ZIP_STORED) as archive:
            for name, content in sorted(data.items()):
                info = zipfile.ZipInfo(name, STAMP)
                info.create_system = 3
                info.external_attr = (stat.S_IFREG | 0o644) << 16
                info.compress_type = zipfile.ZIP_STORED
                info.extra = b''
                info.comment = b''
                archive.writestr(info, content)
    with zipfile.ZipFile(output) as archive:
        if archive.namelist() != sorted(data) or archive.testzip() is not None:
            raise RuntimeError('archive structure or CRC verification failed')
        for name, content in data.items():
            if archive.read(name) != content:
                raise RuntimeError('archive content verification failed: ' + name)
    digest = hashlib.sha256(output.read_bytes()).hexdigest()
    print(digest + '  ' + output.name)


if __name__ == '__main__':
    try:
        main()
    except (OSError, ValueError, RuntimeError, zipfile.BadZipFile) as exc:
        print('Archive creation failed: ' + str(exc), file=sys.stderr)
        sys.exit(1)
