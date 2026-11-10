"""Generate a standalone LaTeX source and compile the report twice."""
import datetime
import os
from pathlib import Path
import re
import shutil
import subprocess

ROOT = Path(__file__).resolve().parent
NAME = "ipra_prevalidated_elimination"


def expand(text):
    def include(match):
        name = match.group(1)
        path = ROOT / (name if name.endswith(".tex") else name + ".tex")
        return expand(path.read_text())
    text = re.sub(r"\\input\{([^}]+)\}", include, text)
    def listing(match):
        options, name = match.groups()
        return "\\begin{lstlisting}" + (options or "") + "\n" + (ROOT / name).read_text() + "\\end{lstlisting}"
    return re.sub(r"\\lstinputlisting(\[[^\]]*\])?\{([^}]+)\}", listing, text)


def main():
    source = ROOT / (NAME + ".tex")
    source.write_text(expand((ROOT / "report.tex").read_text()))
    out = ROOT / "build"
    out.mkdir(exist_ok=True)
    env = dict(os.environ)
    env["SOURCE_DATE_EPOCH"] = str(int(datetime.datetime(2026, 11, 10, 20, tzinfo=datetime.timezone.utc).timestamp()))
    env["FORCE_SOURCE_DATE"] = "1"
    logs = []
    for iteration in (1, 2):
        proc = subprocess.run(["pdflatex", "-interaction=nonstopmode", "-halt-on-error",
                               "-output-directory=" + str(out), source.name],
                              cwd=ROOT, env=env, text=True, capture_output=True)
        logs.append("PASS " + str(iteration) + "\n" + proc.stdout + proc.stderr)
        if proc.returncode:
            (ROOT / "evidence/latex_build.log").write_text("\n".join(logs))
            raise SystemExit(proc.stdout[-8000:] + proc.stderr)
    shutil.copyfile(out / (NAME + ".pdf"), ROOT / (NAME + ".pdf"))
    (ROOT / "evidence/latex_build.log").write_text("\n".join(logs))
    print(str(ROOT / (NAME + ".pdf")))


if __name__ == "__main__":
    main()
