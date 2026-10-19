#!/usr/bin/env python3
"""Render actual verification statistics and the full canonical table as TeX."""
from pathlib import Path
import json,sys
sys.path.insert(0,str(Path(__file__).resolve().parent))
from construct import load
ROOT=Path(__file__).resolve().parents[1]

def main():
    ev=ROOT/'evidence'
    expanded=json.loads((ev/'expanded-runtime.json').read_text())
    literal=json.loads((ev/'literal-regression.json').read_text())
    blank=json.loads((ev/'blank.json').read_text())
    assert expanded['status']=='PASS_UNIVERSAL_EXPANDED_RUNTIME'
    assert expanded['counts']['cases']==literal['cases']==8390
    assert expanded['literal_rows_covered']==literal['covered_rows']==484
    text=r'''\section{Executed verification and initialization}
\label{sec:evidence}

The baseline was first independently reproduced from the exact reference
bundle. Its quick checks passed all 8,390 affine cases and literal fixtures,
with the stated 407,967-transition blank prefix. The new table was then
checked by the independent local proof, two independent literal tape
representations, the inherited affine engine, a full literal source-case
regression, and the expanded symbolic engine against the actual changed
table. The expanded replay was executed completely, not inferred from a
predecessor's record.

\begin{center}
\begin{tabularx}{\linewidth}{@{}lX@{}}
\toprule
Check & Observed result and scope\\
\midrule
Independent local proof & Five complete local identities and all 478 ordinary boundary rows pass; arbitrary exterior tape.\\
Blank initialization & @BOOT@ actual transitions; sparse and dense executions agree, including both numberings and every one-cell.\\
Affine runtime & All 8,390 cases pass, with the unchanged reference box contracts.\\
Literal runtime fixtures & All 8,390 cases pass in @LITERAL@ transitions; all 484 rows are exercised.\\
Expanded runtime & All 8,390 cases pass using @RULES@ symbolic rules; all 484 rows are covered and no row is unused.\\
\bottomrule
\end{tabularx}
\end{center}

The expanded execution took @SECONDS@ seconds in this environment. Runtime
figures are observations, not portable performance guarantees. Its contracts
quantify over all nine natural primary registers, a nonnegative additional
gap above frame padding 64, and every nonempty finite spare suffix. The
underlying list and block induction rules are unchanged; their bindings and
the candidate's table and source hashes are recorded in the evidence.
The finite literal fixtures do not replace those universal contracts.

The exact new blank endpoint has inherited dispatcher 96 (canonical 86),
head $-5$, marker $-6$, header 176, and span 181. Its logical primary values
are $(3,0,0,0,3,0,0,0,0)$, followed by 167 spare blocks of value one. The
whole tape contains 351 ones and is zero elsewhere. All coordinates are
recorded in \path{evidence/blank.json}; only six slow comparison blocks
occur in the old prefix, explaining the twelve extra transitions. The new
prefix was actually executed at the resulting time before whole-tape equality
was accepted.

Two independently written finite-context checkers agree on the new local
proof. The selected checker is \path{code/verify_local.py}; the discovery
agent's separate checker and its records are retained under \path{research/}.
Neither is a proof-assistant kernel. The ordinary proof in the preceding
section establishes how their finite obligations imply global equivalence.
The archived verification driver also checks the identities of all 291
selected inherited reference inputs and verifies that bound inputs remain
unchanged across its quick replay. It labels a newly executed expanded stage
separately from validation of a preexisting expanded output.
'''
    text=text.replace('@BOOT@',f"{blank['candidate_ticks']:,}").replace('@LITERAL@',f"{literal['literal_steps']:,}").replace('@RULES@',f"{expanded['counts']['symbolic_rules']:,}").replace('@SECONDS@',f"{expanded['seconds']:.3f}")
    (ROOT/'sections/evidence.tex').write_text(text)
    table,start=load(ROOT/'machine/zfc_context242.tm')
    assert start==0 and {q for q,b in table}==set(range(242))
    parts=[]
    for page,first in enumerate((0,123)):
        parts.append(r'\clearpage')
        parts.append(r'\section{Full canonical transition table}' if page==0 else r'\subsection*{Canonical transition table, continued}')
        parts.append(r'Each action is \path{write/direction/next}, with slashes omitted. Start state 0; blank symbol 0; halt 242. The halt state has no working rows.')
        parts.append(r'\begin{center}\small\ttfamily')
        parts.append(r'\begin{tabular}{rll@{\qquad}rll@{\qquad}rll}\toprule')
        parts.append(r'$q$ & read 0 & read 1 & $q$ & read 0 & read 1 & $q$ & read 0 & read 1\\\midrule')
        for i in range(41):
            fields=[]
            for panel in range(3):
                q=first+41*panel+i
                if q>=242:fields.extend(['','',''])
                else:fields.extend([str(q),*[''.join(map(str,table[q,b])) for b in (0,1)]])
            parts.append(' & '.join(fields)+r'\\')
        parts.extend([r'\bottomrule\end{tabular}',r'\end{center}'])
    (ROOT/'sections/table.tex').write_text('\n'.join(parts)+'\n')
    print('Wrote evidence.tex and complete 484-row canonical table.')

if __name__=='__main__':main()
