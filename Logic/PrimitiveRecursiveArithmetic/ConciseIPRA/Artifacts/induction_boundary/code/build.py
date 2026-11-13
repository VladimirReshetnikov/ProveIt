#!/usr/bin/env python3
"""Build with installed TeX, generating a private format when necessary."""
from pathlib import Path
import tempfile
from tex_build import build

ROOT = Path(__file__).resolve().parents[1]


def main():
    with tempfile.TemporaryDirectory(prefix="ipra_report_") as temp:
        transcript = Path(temp) / "build.log"
        try:
            build(ROOT / "report.tex", ROOT / "report.pdf", transcript)
        except Exception:
            if transcript.is_file():
                print(transcript.read_text(errors="replace")[-7000:])
            raise
        log = (ROOT / "report.log").read_text(errors="replace")
        warnings = [line for line in log.splitlines()
                    if "Overfull" in line or "Warning" in line]
        (ROOT / "evidence/build_warnings.txt").write_text("\n".join(warnings) + ("\n" if warnings else ""))
        (ROOT / "report.log").unlink()
        print("Built report.pdf")
        if warnings:
            print("\n".join(warnings))


if __name__ == "__main__":
    main()
