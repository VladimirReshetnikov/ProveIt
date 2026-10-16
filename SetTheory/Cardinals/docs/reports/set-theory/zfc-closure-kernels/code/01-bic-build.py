"""Build the standalone research article with pdfLaTeX, without stale outputs."""
from __future__ import annotations
import shutil
import subprocess
import tempfile
from pathlib import Path


def main() -> None:
    root = Path(__file__).resolve().parent
    executable = shutil.which("pdflatex")
    if executable is None:
        raise SystemExit("pdflatex was not found. Install a TeX distribution and add it to PATH.")
    source = root / "article" / "zfc_closure_kernel.tex"
    if not source.is_file():
        raise SystemExit(f"Missing source: {source}")
    result_dir = root / "results"
    result_dir.mkdir(exist_ok=True)
    with tempfile.TemporaryDirectory(prefix="zfc-bic-build-") as directory:
        work = Path(directory)
        shutil.copy2(source, work / source.name)
        logs = []
        for number in range(1, 4):
            run = subprocess.run(
                [executable, "-interaction=nonstopmode", "-halt-on-error", source.name],
                cwd=work, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                text=True, encoding="utf-8", errors="replace", check=False,
            )
            logs.append(f"=== Pass {number} ===\n{run.stdout}")
            if run.returncode:
                path = result_dir / "build_failure.log"
                path.write_text("\n".join(logs), encoding="utf-8")
                raise SystemExit(f"pdfLaTeX failed on pass {number}. See {path}")
        log = (work / source.with_suffix(".log").name).read_text(encoding="utf-8", errors="replace")
        for marker in ["There were undefined references", "Rerun to get cross-references right"]:
            if marker in log:
                raise SystemExit(f"Unresolved references after three passes: {marker}")
        target = source.with_suffix(".pdf")
        shutil.copy2(work / target.name, target)
        (result_dir / "build_log.txt").write_text(log, encoding="utf-8")
    print(f"Built {target}")


if __name__ == "__main__":
    main()
