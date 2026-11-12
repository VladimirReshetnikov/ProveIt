"""Expand the report to one standalone LaTeX file; does not invoke TeX."""
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parent
text = (ROOT / "report.tex").read_text()
text = re.sub(r"\\input\{([^}]+)\}",
              lambda match: "\n% BEGIN inherited fragment: " + match[1] + "\n"
              + (ROOT / match[1]).read_text() + "\n% END inherited fragment\n", text)
text = re.sub(r"\\lstinputlisting\[language=Python\]\{([^}]+)\}",
              lambda match: "\\begin{lstlisting}[language=Python]\n"
              + (ROOT / match[1]).read_text() + "\\end{lstlisting}", text)
(ROOT / "ipra_direct_closure.tex").write_text(text)
print("Expanded standalone LaTeX source written.")
