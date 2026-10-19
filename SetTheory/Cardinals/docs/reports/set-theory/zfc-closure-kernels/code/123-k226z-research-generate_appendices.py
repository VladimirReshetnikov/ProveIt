#!/usr/bin/env python3
"""Regenerate the paper's literal table, complete delta, and prefix-bit appendix."""
from pathlib import Path
import hashlib
import json

ROOT = Path(__file__).resolve().parents[1]


def read_table(path):
    rows = {}
    for line in path.read_text().splitlines():
        if not line or line.startswith('#'):
            continue
        q, b, w, d, z = line.split()
        key = int(q), int(b)
        assert key not in rows and d in ('L', 'R')
        rows[key] = int(w), d, int(z)
    return rows


def code(row):
    return r'\texttt{' + ''.join(map(str, row)) + '}'


def main():
    selected = ROOT / 'machines/k226.tm'
    assert hashlib.sha256(selected.read_bytes()).hexdigest() == 'b58279b8b2e2cf029dd94e084d47cd6097772d7bce2a62653767895123d29599'
    rows = read_table(selected)
    assert set(rows) == {(q, b) for q in range(226) for b in (0, 1)}
    lines = [r'\section{The complete 226-state transition table}',
             r'\label{app:table}',
             'This is the selected dense table, with start state 0, dispatcher 82,',
             'and separate halt label 226. A row entry such as '+r'\texttt{1R92}',
             'means write 1, move right, and enter state 92. The two groups of',
             'columns list distinct states; together they give all 452 binary',
             'transitions. The head starts at coordinate zero on the all-zero tape.',
             r'\begin{longtable}{@{}rll@{\qquad\qquad}rll@{}}',
             r'\toprule State & Read 0 & Read 1 & State & Read 0 & Read 1\\\midrule',
             r'\endfirsthead',
             r'\toprule State & Read 0 & Read 1 & State & Read 0 & Read 1\\\midrule',
             r'\endhead', r'\bottomrule\endfoot']
    for q in range(113):
        r = q + 113
        lines.append(f'{q} & {code(rows[q, 0])} & {code(rows[q, 1])} & '
                     f'{r} & {code(rows[r, 0])} & {code(rows[r, 1])}'+r'\\')
    lines.append(r'\end{longtable}')
    (ROOT / 'sections/transition_table.tex').write_text('\n'.join(lines) + '\n')

    old = read_table(ROOT / 'machines/k230.tm')
    new = read_table(ROOT / 'machines/k226_k230labels.tm')
    changed = [(key, old[key], new[key]) for key in sorted(new) if old[key] != new[key]]
    removed = [(key, old[key]) for key in sorted(old) if key not in new]
    assert len(changed) == 52 and len(removed) == 8
    assert {q for (q, b), row in removed} == {65, 79, 140, 175}
    lines = [r'\section{Every surviving-row change from K230}',
             r'\label{app:delta}',
             'All state numbers in this appendix are the original K230 labels.',
             'The original halt label is 230. Dense renumbering is applied only',
             'after these changes and the four state deletions.',
             r'\begin{longtable}{@{}rrll@{}}',
             r'\toprule State & Read & Original K230 & Final K226, original labels\\\midrule',
             r'\endfirsthead',
             r'\toprule State & Read & Original K230 & Final K226, original labels\\\midrule',
             r'\endhead', r'\bottomrule\endfoot']
    for (q, b), a, z in changed:
        lines.append(f'{q} & {b} & {code(a)} & {code(z)}'+r'\\')
    lines += [r'\end{longtable}', 'The following eight rows are deleted:',
              r'\begin{center}\begin{tabular}{@{}rrl@{}}',
              r'\toprule State & Read & Original row\\\midrule']
    for (q, b), a in removed:
        lines.append(f'{q} & {b} & {code(a)}'+r'\\')
    lines += [r'\bottomrule\end{tabular}\end{center}',
              'The complete dense renumbering is also explicit. For every retained',
              'working state $q$ in the original numbering, put',
              r'\[\nu(q)=q-\bigl|\{d\in\{65,79,140,175\}:d<q\}\bigr|.',
              r'\]',
              'Set $'+r'\nu(230)=226'+'$ for halt. Thus the start remains 0 and',
              'the original dispatcher 84 becomes 82. This is a bijection on',
              'working states and preserves every write, move, and transition target.']
    (ROOT / 'sections/transition_delta.tex').write_text('\n'.join(lines) + '\n')
    delta = {'state_numbering': 'original K230',
             'changed_surviving_rows': [{'state': q, 'read': b, 'old': a, 'new': z}
                                        for (q, b), a, z in changed],
             'deleted_rows': [{'state': q, 'read': b, 'old': a} for (q, b), a in removed]}
    (ROOT / 'machines/delta230_226.json').write_text(json.dumps(delta, indent=2) + '\n')

    bits = (ROOT / 'formalisms/prefix663/prefix.bits').read_text().strip()
    assert len(bits) == 574 and set(bits) == {'0', '1'}
    assert hashlib.sha256(bits.encode()).hexdigest() == 'c6414e72e7682442c170ef20c3f0376ee5ee82368854ec231bc500c565ae6313'
    lines = [r'\section{The complete 574-bit equational packet}',
             'Concatenate the following lines without whitespace. Every codebook',
             'bit, axiom bit, delimiter and query bit is included. Line breaks',
             'are for display only; there is no omitted signature or external',
             'symbol palette. The fixed decoder grammar is given in',
             r'Section~\ref{sec:encodings}.', r'\begin{lstlisting}']
    lines += [bits[i:i+64] for i in range(0, len(bits), 64)]
    lines += [r'\end{lstlisting}',
              'This is a presentation encoding. The complete 226-state machine',
              'does not contain or interpret this packet. Its Turing-machine',
              'parser, proof enumerator and blank writer have not been implemented.']
    (ROOT / 'sections/prefix_packet.tex').write_text('\n'.join(lines) + '\n')

    # Display the complete inherited equational presentation without adding
    # operation symbols. Each abbreviation is mechanically expanded and
    # compared with the exact JSON tree before being printed.
    data = json.loads((ROOT / 'formalisms/E663.json').read_text())
    abbreviations = {
        '@m': ['V', 'b', ['d']], '@t': ['P', 'b', 'z'], '@u': ['Q', 'b'],
        '@e': ['p_eps', ['P', '@t', ['P', '@u', 'b']], '@m'],
        '@f': ['N', ['p_E', ['A', 'b', 'z'], '@t'],
                    ['N', ['d'], ['p_E', ['A', 'b', 'z'], 'z']]],
        '@g': ['N', ['d'], ['p_E', 'y', '@u']],
        '@h': ['p_eps', ['P', 'y', ['P', 'x', 'b']], '@m'],
        '@j': ['N', ['p_E', ['W', 'x', ['d']], 'x'],
                    ['N', ['d'], ['p_E', 'x', '@u']]],
        '@k': ['N', ['p_E', 'y', '@u'],
                    ['p_eps', ['P', 'y', ['P', ['P', 'b', 'y'], 'b']], '@m']],
        '@l': ['N', ['N', '@g', ['N', '@h', '@j']], '@k']}
    final = [['d'], ['N', ['N', '@e', ['N', ['d'], '@f']], ['N', ['d'], '@l']]]

    def expand_term(term):
        if isinstance(term, str):
            return expand_term(abbreviations[term]) if term.startswith('@') else term
        return [term[0], *(expand_term(x) for x in term[1:])]

    assert [expand_term(t) for t in final] == data['equations'][6]
    names = {'p_E': r'p_E', 'p_eps': r'p_\varepsilon'}

    def latex(term):
        if isinstance(term, str):
            return term[1:] if term.startswith('@') else term
        name = names.get(term[0], term[0])
        return name if len(term) == 1 else name + '(' + ','.join(latex(x) for x in term[1:]) + ')'

    lines = [r'\section{The seven equations encoded by the E663 packet}',
             'All variables in each equation are universally quantified independently.',
             'The only operation symbols are the nine in the declared signature.',
             'The first six equations are:', r'\begin{align*}']
    for i, (a, b) in enumerate(data['equations'][:6], 1):
        lines.append(latex(a) + ' &= ' + latex(b) + r'\qquad\text{(E' + str(i) + r')}\\')
    lines[-1] = lines[-1][:-2]
    lines += [r'\end{align*}',
              'For the seventh equation, use the following term abbreviations.',
              'They are purely typographical and introduce no extra operation',
              'symbols or axioms:', r'\begin{align*}']
    for label, term in abbreviations.items():
        lines.append(label[1:] + ' &:= ' + latex(term) + r'\\')
    lines[-1] = lines[-1][:-2]
    lines += [r'\end{align*}', 'The last equation is',
              r'\[d=N(N(e,N(d,f)),N(d,l)).\tag{E7}\]',
              'The ground query is $Q(d)=d$. The appendix generator expands every',
              'abbreviation and checks exact equality with the seventh JSON term',
              'tree, so the displayed presentation matches the encoded packet.',
              'The inherited calibration and the reasons for the noncollapse query',
              'are retained in the pinned 235-state archive.']
    (ROOT / 'sections/equations663.tex').write_text('\n'.join(lines) + '\n')
    print('PASS: 452 literal rows; 52 changed and 8 deleted K230 rows; 574 packet bits; exact seven-equation display.')


if __name__ == '__main__':
    if not __debug__:
        raise RuntimeError('Run with assertions enabled')
    main()
