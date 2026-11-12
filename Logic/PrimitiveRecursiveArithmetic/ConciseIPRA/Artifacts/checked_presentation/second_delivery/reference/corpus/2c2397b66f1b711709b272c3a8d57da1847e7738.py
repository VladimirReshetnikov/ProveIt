"""Assemble a standalone LaTeX paper from the included reviewable sections."""
from pathlib import Path

ROOT = Path(__file__).resolve().parent

front = (ROOT / 'frontmatter.tex').read_text()
listing = ('\\begin{lstlisting}\n'
           + (ROOT / 'code/checker_bytes.py').read_text()
           + '\\end{lstlisting}\n')
front = front.replace('% BYTE_LISTING_INSERTION', listing)
parts = [front]
for name in ('mixed_closure.tex', 'zero_start_obstruction.tex'):
    parts.append((ROOT / 'theory' / name).read_text())
parts.append(r'''
\clearpage
\appendix
\section*{Attribution and dependency boundary for the appendices}
\addcontentsline{toc}{section}{Attribution and dependency boundary}
The following five sections are reproduced from the pinned repository's
\file{Research/certified_zero/reference/} directory, with its MIT-0 license.
They supply the existing native logical basis and scalar arithmetic bridge.
They are not new contributions of this note. In particular, the phrase
``new'' in an inherited section refers to its own original comparison,
not to the present work. The first appendix uses conditional context
clauses; the main text uses the equivalent explicit $Q$ notation.
Their original labels and mathematical content have been retained, while
citations are resolved to the specific pinned source files below.
''')
for name in ('inherited_choice_basis.tex', 'inherited_ordinary_bridge.tex',
             'scalar_predecessor.tex', 'equality_reflection.tex',
             'primitive_recursion.tex'):
    parts.append((ROOT / 'reference' / name).read_text())
parts.append(r'''
\clearpage
\begin{thebibliography}{9}
\raggedright
\bibitem{current}
Vladimir Reshetnikov, \emph{Concise presentations of intuitionistic primitive
recursive arithmetic}, ProveIt repository, pinned commit
\texttt{8662bc0a00f4e77e482f7d141d7a4f919f70f9aa}.
\href{https://github.com/VladimirReshetnikov/ProveIt/blob/8662bc0a00f4e77e482f7d141d7a4f919f70f9aa/Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/README.md}{Project README and proposal inventory}.
Accessed for this note on 10 November 2026 (America/Los\_Angeles).

\bibitem{scope}
ProveIt, \emph{Neutral scope}, same snapshot.
\href{https://github.com/VladimirReshetnikov/ProveIt/tree/8662bc0a00f4e77e482f7d141d7a4f919f70f9aa/Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/Research/neutral_scope}{Research package};
in particular \file{code/checker.py}, \file{report.tex}, and the public
certificate protocol and scope-invariant analysis.

\bibitem{coverage}
ProveIt, \emph{Coverage and kernel}, same snapshot.
\href{https://github.com/VladimirReshetnikov/ProveIt/tree/8662bc0a00f4e77e482f7d141d7a4f919f70f9aa/Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/Research/coverage_and_kernel}{Research package};
in particular \file{code/checker_ast.py}, \file{theory/kernel.tex}, and the
inherited certificate/control collection.

\bibitem{prevalidate}
ProveIt, \emph{Prevalidated elimination}, same snapshot.
\href{https://github.com/VladimirReshetnikov/ProveIt/tree/8662bc0a00f4e77e482f7d141d7a4f919f70f9aa/Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/Research/prevalidated_elimination}{Research package};
the antecedent idea of pure template validation before checking the major
premise is credited to this package.

\bibitem{erasure}
ProveIt, \emph{Internal scalar predecessor bootstrap}, frozen reference
\file{certified_zero/reference/scalar_predecessor.tex}, same snapshot.
\href{https://github.com/VladimirReshetnikov/ProveIt/blob/8662bc0a00f4e77e482f7d141d7a4f919f70f9aa/Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/Research/certified_zero/reference/scalar_predecessor.tex}{Pinned source}; reproduced in this note with its existing attribution.

\bibitem{forward}
ProveIt, \emph{Equality reflection}, frozen reference
\file{certified_zero/reference/equality_reflection.tex}, same snapshot.
\href{https://github.com/VladimirReshetnikov/ProveIt/blob/8662bc0a00f4e77e482f7d141d7a4f919f70f9aa/Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/Research/certified_zero/reference/equality_reflection.tex}{Pinned source}; reproduced in this note with its existing attribution.

\bibitem{progress}
ProveIt, \emph{Pairing, primitive recursion, and internal numerical composites},
frozen reference \file{certified_zero/reference/primitive_recursion.tex},
same snapshot.
\href{https://github.com/VladimirReshetnikov/ProveIt/blob/8662bc0a00f4e77e482f7d141d7a4f919f70f9aa/Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/Research/certified_zero/reference/primitive_recursion.tex}{Pinned source}; reproduced in this note with its existing attribution.
\end{thebibliography}
\end{document}
''')
(ROOT / 'report.tex').write_text('\n\n'.join(parts))
print('Assembled report.tex')
