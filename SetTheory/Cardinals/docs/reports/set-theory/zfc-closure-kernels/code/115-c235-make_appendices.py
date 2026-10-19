#!/usr/bin/env python3
"""Generate the exact literal-table and E663-bit appendices from delivered data."""
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parent


def main():
    table_path = ROOT/'machines/zfc235.tm'
    assert hashlib.sha256(table_path.read_bytes()).hexdigest() == '4a2c6b05e347522236dc6faf0bde5f71480aa6c6795faa6f20a11f1a1601895f'
    table = {}
    for line in table_path.read_text().splitlines():
        if line and not line.startswith('#'):
            q, b, w, d, target = line.split()
            table[int(q), int(b)] = (w, d, target)
    assert set(table) == {(q, b) for q in range(235) for b in (0, 1)}
    reached, pending = set(), [0]
    while pending:
        q = pending.pop()
        if q in reached or q == 235:
            continue
        reached.add(q)
        pending.extend(int(table[q, b][2]) for b in (0, 1))
    assert reached == set(range(235))
    text = r'''\section{Complete canonical transition table}
\label{app:machine}
The working states are $0,\ldots,234$, the initial state is 0, and the
separate halt outcome is 235. The initial head coordinate is 0 and the
entire tape is zero. An entry such as $1L42$ means: write 1, move one cell
left, and enter state 42. Outcome 235 has no outgoing rows. Each state
appears exactly once below, with both binary read cases.

The plain-text table has rows \texttt{state read write direction target}
and a \texttt{\#! start 0} header. The supplied renumbering is a literal
bijection from the inherited working states, followed by the separate
halt label. All 235 working states are reachable in the directed
transition graph; this graph fact does not assert that every state is
visited by the blank run.

\begingroup\small
\setlength{\tabcolsep}{7pt}
\begin{longtable}{rll@{\qquad}rll@{\qquad}rll}
\toprule
State & Read 0 & Read 1 & State & Read 0 & Read 1 & State & Read 0 & Read 1\\
\midrule
\endfirsthead
\multicolumn{9}{c}{\emph{Canonical transition table, continued}}\\
\toprule
State & Read 0 & Read 1 & State & Read 0 & Read 1 & State & Read 0 & Read 1\\
\midrule
\endhead
\midrule\multicolumn{9}{r}{\emph{Continued on next page}}\\
\endfoot
\bottomrule
\endlastfoot
'''
    shown = []
    for row in range(79):
        cells = []
        for q in [row, row+79, row+158]:
            if q < 235:
                shown.append(q)
                cells.append(str(q))
                cells += [r'\texttt{'+''.join(table[q, b])+'}' for b in (0, 1)]
            else:
                cells += ['', '', '']
        text += ' & '.join(cells)+r'\\'+'\n'
    assert sorted(shown) == list(range(235))
    text += '\\end{longtable}\n\\endgroup\n'
    (ROOT/'sections/machine_table.tex').write_text(text)
    bits = (ROOT/'formalisms/e663/generated/E663.bits').read_text().strip()
    assert len(bits) == 663 and set(bits) == {'0', '1'}
    assert hashlib.sha256(bits.encode()).hexdigest() == '6c3b72c39c81aa5bbf028e654c8056e7e86376cdeecdd56943e5c3e23de1a215'
    assert bits[-12:] == '100101000100'
    appendix = r'''\section{The literal E663 packet}
The following lines concatenate to the complete 663-bit packet. The
typographical line breaks are not data. The packed file has 83 bytes,
with one final zero padding bit excluded from the logical length.
\begin{lstlisting}[basicstyle=\footnotesize\ttfamily]
'''
    appendix += '\n'.join(bits[i:i+80] for i in range(0, len(bits), 80))+'\n'
    appendix += r'''\end{lstlisting}
The logical-bit SHA-256, excluding a text-file newline, is
\begin{center}\small\ttfamily
6c3b72c39c81aa5bbf028e654c8056e7e86376cdeecdd56943e5c3e23de1a215.
\end{center}
The header declares nine symbols, their three-bit arities, and a
four-variable local capacity. Every term node has a four-bit opcode.
Variables use codes 0--3; the ordered operation codes are:
\begin{center}
\begin{tabular}{rcl@{\qquad}rcl}
\toprule
Code & Arity & Symbol & Code & Arity & Symbol\\
\midrule
4&0&$d$ & 9&1&$Q$\\
5&2&$N$ &10&2&$W$\\
6&2&$V$ &11&2&$p_E$\\
7&2&$P$ &12&2&$p_\varepsilon$\\
8&2&$A$ &&&\\
\bottomrule
\end{tabular}
\end{center}
Each equation begins with marker 1 and contains its two prefix-encoded
terms. Marker 0 ends the equation list. Two ground terms follow. The
last 12 bits, \texttt{1001 0100 0100}, encode $Q(d)$ and $d$.
The AST and independent decoder provide the machine-readable definition;
the displayed accounting includes the complete signature, arities,
equation list, and both endpoints. Unused opcodes and nonground endpoints
are rejected. This packet defines a consistency problem, not a 663-state
or 663-step machine.
'''
    (ROOT/'sections/packet_bits.tex').write_text(appendix)
    (ROOT/'evidence/appendix_audit.json').write_text(json.dumps({
        'status': 'PASS_EXACT_LITERAL_APPENDICES', 'machine_states': 235,
        'machine_rows': 470, 'all_working_states_graph_reachable': True,
        'each_canonical_state_printed_once': True, 'E663_bits': 663,
        'table_sha256': hashlib.sha256(table_path.read_bytes()).hexdigest(),
        'logical_bit_sha256': hashlib.sha256(bits.encode()).hexdigest(),
    }, indent=2)+'\n')


if __name__ == '__main__':
    main()
