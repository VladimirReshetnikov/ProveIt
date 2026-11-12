"""Reassemble report.tex from the included editable sections and checker."""
from pathlib import Path

root = Path(__file__).resolve().parent
parts = ["preamble.tex", "variable_substitution_proof.tex",
         "latest_variable_translation.tex", "normalization_bridge.tex",
         "implementation_conclusion.tex"]
text = "\n".join((root / "paper" / name).read_text() for name in parts)
text += "\n\\begin{lstlisting}\n"
text += (root / "code" / "native_goal_latest.py").read_text()
text += "\n\\end{lstlisting}\n\\end{document}\n"
(root / "report.tex").write_text(text)
print("Assembled standalone report.tex")
