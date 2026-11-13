"""Expand standalone TeX, create a payload manifest, and build the ZIP."""
import hashlib
import json
from pathlib import Path
import re
import shutil
import zipfile

ROOT = Path(__file__).resolve().parent
STEM = "ipra_checker_and_barriers_2026-11-10"
SKIP_SUFFIXES = {".aux", ".log", ".out", ".toc", ".fls", ".fdb_latexmk", ".pyc"}


def expand(source):
    source = re.sub(r"\\input\{([^}]+)\}",
                    lambda match: expand((ROOT / match[1]).read_text()), source)
    return re.sub(r"\\lstinputlisting\[([^]]+)\]\{([^}]+)\}",
                  lambda match: "\\begin{lstlisting}[" + match[1] + "]\n"
                  + (ROOT / match[2]).read_text() + "\\end{lstlisting}", source)


def payload():
    return sorted(path for path in ROOT.rglob("*") if path.is_file()
                  and "__pycache__" not in path.parts
                  and path.suffix not in SKIP_SUFFIXES
                  and path.name not in {"MANIFEST.json", "report_standalone.pdf"})


if __name__ == "__main__":
    (ROOT / "report_standalone.tex").write_text(expand((ROOT / "report.tex").read_text()))
    files = payload()
    if not (ROOT / "report.pdf").exists():
        raise SystemExit("Build and inspect report.pdf before packaging.")
    rows = [{"path": str(path.relative_to(ROOT)), "bytes": path.stat().st_size,
             "sha256": hashlib.sha256(path.read_bytes()).hexdigest()} for path in files]
    (ROOT / "MANIFEST.json").write_text(json.dumps({"files": rows}, indent=2) + "\n")
    destination = ROOT.parent / (STEM + ".zip")
    with zipfile.ZipFile(destination, "w", zipfile.ZIP_DEFLATED, compresslevel=9) as archive:
        for path in files + [ROOT / "MANIFEST.json"]:
            info = zipfile.ZipInfo(STEM + "/" + str(path.relative_to(ROOT)),
                                   (2026, 11, 10, 12, 0, 0))
            info.compress_type = zipfile.ZIP_DEFLATED
            info.external_attr = 0o100644 << 16
            archive.writestr(info, path.read_bytes(), compresslevel=9)
    shutil.copyfile(ROOT / "report.pdf", ROOT.parent / (STEM + ".pdf"))
    shutil.copyfile(ROOT / "report_standalone.tex", ROOT.parent / (STEM + ".tex"))
    print(json.dumps({"archive": str(destination), "files": len(files) + 1,
                      "bytes": destination.stat().st_size,
                      "sha256": hashlib.sha256(destination.read_bytes()).hexdigest()}, indent=2))
