"""Flatten the modular report and code listings into one standalone TeX file."""
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parent

def expand(name, active=()):
    path = (ROOT / name).resolve()
    if ROOT not in path.parents or path in active:
        raise ValueError("Invalid or cyclic report input: " + str(path))
    text = path.read_text()
    text = re.sub(r"\\input\{([^}]+)\}",
                  lambda m: expand(m.group(1), active + (path,)), text)
    def listing(match):
        options = match.group(1)
        source = (ROOT / match.group(2)).read_text()
        return (r"\begin{lstlisting}" + ("[" + options + "]" if options else "")
                + "\n" + source.rstrip() + "\n" + r"\end{lstlisting}")
    return re.sub(r"\\lstinputlisting(?:\[([^]]*)\])?\{([^}]+)\}",
                  listing, text)

if __name__ == "__main__":
    destination = ROOT / "ipra_checked_reductions.tex"
    destination.write_text(expand("paper_template.tex"))
    print("Assembled", destination.name)

