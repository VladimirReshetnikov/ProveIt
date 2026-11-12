"""Build the self-contained LaTeX source and PDF without network or shell escape."""
from pathlib import Path
import json
import os
import re
import shutil
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parent


def expand(path, active=()):
    path = path.resolve()
    if path in active or not path.is_relative_to(ROOT):
        raise ValueError("Invalid or cyclic LaTeX input: " + str(path))
    text = path.read_text()
    def include(match):
        source = ROOT / match[1]
        if not source.suffix:
            source = source.with_suffix(".tex")
        return ("\n% Begin included source: " + str(source.relative_to(ROOT)) +
                "\n" + expand(source, active + (path,)) +
                "\n% End included source\n")
    text = re.sub(r"\\input\{([^}]+)\}", include, text)
    def listing(match):
        source = (ROOT / match[2]).resolve()
        if not source.is_relative_to(ROOT):
            raise ValueError("Listing outside package")
        options = match[1] or ""
        return (r"\begin{lstlisting}" + options + "\n" +
                source.read_text().rstrip("\n") + "\n" + r"\end{lstlisting}")
    return re.sub(r"\\lstinputlisting(\[[^]]*\])?\{([^}]+)\}", listing, text)


def build():
    if not shutil.which("pdflatex"):
        raise RuntimeError("PDFLaTeX is required to rebuild the PDF")
    standalone = ROOT / "report_standalone.tex"
    standalone.write_text(expand(ROOT / "report.tex"))
    environment = dict(os.environ)
    environment["SOURCE_DATE_EPOCH"] = "1794336951"
    environment["FORCE_SOURCE_DATE"] = "1"
    with tempfile.TemporaryDirectory(prefix="ipra-paper-build-") as temporary:
        command = ["pdflatex", "-interaction=nonstopmode", "-halt-on-error",
                   "-file-line-error", "-no-shell-escape",
                   "-output-directory=" + temporary, str(standalone)]
        for _ in range(3):
            run = subprocess.run(command, cwd=ROOT, env=environment,
                                 text=True, capture_output=True)
            if run.returncode:
                print(run.stdout[-12000:])
                raise RuntimeError("PDFLaTeX failed")
        log = (Path(temporary) / "report_standalone.log").read_text()
        shutil.copyfile(Path(temporary) / "report_standalone.pdf", ROOT / "report.pdf")
        (ROOT / "evidence/latex_build.log").write_text(log)
    warnings = [line for line in log.splitlines()
                if "Overfull" in line or "undefined" in line.lower()
                or "multiply defined" in line.lower()]
    receipt = {"engine": "pdflatex", "passes": 3, "shell_escape": False,
               "source_date_epoch": environment["SOURCE_DATE_EPOCH"],
               "standalone_bytes": standalone.stat().st_size,
               "pdf_bytes": (ROOT / "report.pdf").stat().st_size,
               "layout_or_reference_warnings": warnings}
    (ROOT / "evidence/build.json").write_text(json.dumps(receipt, indent=2) + "\n")
    print(json.dumps(receipt, indent=2))
    return receipt


if __name__ == "__main__":
    build()
