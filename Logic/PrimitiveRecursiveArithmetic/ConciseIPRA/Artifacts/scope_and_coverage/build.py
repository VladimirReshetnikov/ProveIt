"""Expand the complete LaTeX source and compile it without shell escape."""
import json
import re
import shutil
import subprocess
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent
STEM = "ipra_scope_and_coverage"


def expand(text):
    def include(match):
        path = (ROOT / match.group(1)).resolve()
        if not path.is_relative_to(ROOT):
            raise ValueError("LaTeX input leaves the package")
        return expand(path.read_text())

    text = re.sub(r"\\input\{([^}]+)\}", include, text)

    def listing(match):
        options, name = match.group(1) or "", match.group(2)
        path = (ROOT / name).resolve()
        if not path.is_relative_to(ROOT):
            raise ValueError("Listing leaves the package")
        return "\\begin{lstlisting}" + options + "\n" + path.read_text() + "\\end{lstlisting}"

    return re.sub(r"\\lstinputlisting(\[[^\]]*\])?\{([^}]+)\}", listing, text)


def main():
    standalone = ROOT / (STEM + ".tex")
    standalone.write_text(expand((ROOT / "report_main.tex").read_text()))
    with tempfile.TemporaryDirectory() as directory:
        build = Path(directory)
        shutil.copy2(standalone, build / standalone.name)
        logs = []
        for _ in range(3):
            result = subprocess.run(
                ["pdflatex", "-no-shell-escape", "-interaction=nonstopmode", "-halt-on-error", standalone.name],
                cwd=build, text=True, capture_output=True,
            )
            logs.append(result.stdout + result.stderr)
            if result.returncode:
                (ROOT / "evidence/build_failed.log").write_text(logs[-1])
                raise RuntimeError("PDFLaTeX failed; see evidence/build_failed.log")
        log = (build / (STEM + ".log")).read_text()
        (ROOT / "evidence/build.log").write_text(log)
        shutil.copy2(build / (STEM + ".pdf"), ROOT / (STEM + ".pdf"))
        warnings = [line for line in log.splitlines()
                    if "Warning" in line or "Overfull" in line or "Underfull" in line]
        (ROOT / "evidence/build.json").write_text(json.dumps({
            "status": "compiled", "passes": 3, "shell_escape": False,
            "warnings": warnings,
        }, indent=2) + "\n")
    print(ROOT / (STEM + ".pdf"))


if __name__ == "__main__":
    main()
