"""Create a clean research archive and verify every archived member's hash."""

from hashlib import sha256
from pathlib import Path
import argparse
import zipfile


ROOT = Path(__file__).resolve().parents[1]


def release_files():
    files = [ROOT / name for name in
             ("README.txt", "requirements.txt", "build.py", "source_manifest.json")]
    files.extend(ROOT / "article" / f"marginal_bose_crossover.{suffix}"
                 for suffix in ("tex", "pdf"))
    for folder, suffixes in (("code", {".py"}), ("tests", {".py"}),
                             ("data", {".json"}), ("figures", {".pdf", ".png"})):
        files.extend(p for p in sorted((ROOT / folder).iterdir())
                     if p.is_file() and p.suffix in suffixes)
    return files


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path,
                        default=ROOT.parent / "marginal_bose_research.zip")
    args = parser.parse_args()
    files = release_files()
    missing = [str(p) for p in files if not p.is_file()]
    if missing:
        raise FileNotFoundError(missing)
    hashes = {p.relative_to(ROOT).as_posix(): sha256(p.read_bytes()).hexdigest()
              for p in files}
    hash_file = ROOT / "SHA256SUMS.txt"
    hash_file.write_text("".join(f"{digest}  {name}\n"
                                for name, digest in sorted(hashes.items())))
    files.append(hash_file)
    with zipfile.ZipFile(args.output, "w", compression=zipfile.ZIP_DEFLATED,
                         compresslevel=9) as archive:
        for path in files:
            archive.write(path, (Path(ROOT.name) / path.relative_to(ROOT)).as_posix())
    with zipfile.ZipFile(args.output) as archive:
        if archive.testzip() is not None:
            raise AssertionError("Archive CRC verification failed")
        for name, digest in hashes.items():
            if sha256(archive.read(f"{ROOT.name}/{name}")).hexdigest() != digest:
                raise AssertionError(f"Archive content hash mismatch: {name}")
    print(f"Created {args.output.resolve()}")
    print(f"Verified {len(files)} archive members; {args.output.stat().st_size:,} bytes")


if __name__ == "__main__":
    main()
