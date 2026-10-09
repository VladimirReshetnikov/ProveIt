#!/usr/bin/env python3
"""Create the complete research ZIP, excluding compiler and TeX scratch files."""
from pathlib import Path
import argparse
import hashlib
import json
import zipfile

ROOT = Path(__file__).resolve().parents[1]
SKIP_DIRECTORIES = {"__pycache__", "build", "bin"}
TEX_SCRATCH = {f"a275672.{s}" for s in (
    "aux", "log", "fls", "fdb_latexmk", "out", "toc", "synctex.gz")}


def included(path):
    relative = path.relative_to(ROOT)
    return (path.is_file() and not path.is_symlink()
            and not any(p in SKIP_DIRECTORIES for p in relative.parts[:-1])
            and not (relative.parent == Path('.') and path.name in TEX_SCRATCH)
            and path.suffix != ".pyc" and path.name != "SHA256SUMS")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path,
                        default=ROOT.parent/"A275672_Research.zip")
    args = parser.parse_args()
    output = args.output.resolve()
    if output.is_relative_to(ROOT):
        parser.error("Write the ZIP outside the source folder.")
    assert (ROOT/"a275672.pdf").is_file()
    # Preserve nested, independently produced checksum manifests as data.
    files = sorted(p for p in ROOT.rglob('*') if included(p))
    files += sorted(p for p in ROOT.rglob('SHA256SUMS')
                    if p.parent != ROOT and not any(
                        part in SKIP_DIRECTORIES
                        for part in p.relative_to(ROOT).parts[:-1]))
    files = sorted(set(files))
    manifest = ROOT/"SHA256SUMS"
    manifest.write_text(''.join(
        hashlib.sha256(p.read_bytes()).hexdigest() + '  ' +
        p.relative_to(ROOT).as_posix() + '\n' for p in files))
    files.append(manifest)
    output.parent.mkdir(parents=True, exist_ok=True)
    with zipfile.ZipFile(output, 'w', compression=zipfile.ZIP_DEFLATED,
                         compresslevel=9) as archive:
        for p in files:
            archive.write(p, 'a275672_research/' + p.relative_to(ROOT).as_posix())
    with zipfile.ZipFile(output) as archive:
        assert archive.testzip() is None
        for line in manifest.read_text().splitlines():
            digest, name = line.split('  ', 1)
            assert hashlib.sha256(archive.read('a275672_research/' + name)).hexdigest() == digest
    print(json.dumps({"zip":str(output), "files":len(files),
                      "bytes":output.stat().st_size,
                      "sha256":hashlib.sha256(output.read_bytes()).hexdigest(),
                      "archive_crc_and_all_file_hashes":"PASS"}, indent=2))


if __name__ == '__main__':
    main()
