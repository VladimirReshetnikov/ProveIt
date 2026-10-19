#!/usr/bin/env python3
"""Generate or verify the report appendix from the exact canonical TM table."""
from pathlib import Path
import argparse
import hashlib
import json

ROOT = Path(__file__).resolve().parents[1]
EXPECTED = '909f29c493e0ccc5d6a481fd7a20a9a82eb934ab2aa7df17b5ec3789255a8c08'


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def render():
    raw = (ROOT / 'machines/zfc238.tm').read_bytes()
    require(hashlib.sha256(raw).hexdigest() == EXPECTED, 'Canonical table identity mismatch')
    rows = {}
    for line in raw.decode().splitlines():
        if not line or line.startswith('#'):
            continue
        q, b, w, direction, r = line.split()
        key = int(q), int(b)
        require(key not in rows, 'Duplicate transition')
        rows[key] = int(w), direction, int(r)
    require(set(rows) == {(q, b) for q in range(238) for b in range(2)},
            'Table must contain exactly 238 complete working states')
    lines = [
        r'\section{Complete canonical transition table}',
        r'\label{sec:full-table}',
        r'The working states are $0,\ldots,237$, start is $0$, and $H=238$',
        r'is the separate halt outcome. The initial tape is all zero and the',
        r'initial head coordinate is zero. In an entry $wDr$, write $w$, move',
        r'one cell in direction $D$, and enter $r$. Both actions for every',
        r'working state are listed. This appendix is generated from',
        r'\file{machines/zfc238.tm}; its generator also supports byte verification.',
        r'\begingroup\footnotesize',
        r'\setlength{\tabcolsep}{8pt}',
        r'\renewcommand{\arraystretch}{1.04}',
        r'\begin{longtable}{rll@{\hspace{14pt}}rll@{\hspace{14pt}}rll}',
        r'\toprule',
        r'$q$ & Read $0$ & Read $1$ & $q$ & Read $0$ & Read $1$ & $q$ & Read $0$ & Read $1$\\',
        r'\midrule\endfirsthead',
        r'\multicolumn{9}{l}{\emph{Complete canonical table, continued}}\\',
        r'\toprule',
        r'$q$ & Read $0$ & Read $1$ & $q$ & Read $0$ & Read $1$ & $q$ & Read $0$ & Read $1$\\',
        r'\midrule\endhead',
        r'\midrule\multicolumn{9}{r}{\emph{Continued on the next page}}\\\endfoot',
        r'\bottomrule\endlastfoot',
    ]
    included = []
    for i in range(80):
        groups = []
        for q in (i, i + 80, i + 160):
            if q >= 238:
                groups.extend(['', '', ''])
                continue
            included.append(q)
            actions = []
            for b in (0, 1):
                w, direction, r = rows[q, b]
                target = 'H' if r == 238 else str(r)
                actions.append(r'$' + str(w) + r'\mathrm{' + direction + '}' + target + '$')
            groups.extend([str(q), *actions])
        lines.append(' & '.join(groups) + r'\\')
    require(sorted(included) == list(range(238)), 'Appendix coverage mismatch')
    lines.extend([r'\end{longtable}', r'\endgroup', ''])
    return '\n'.join(lines)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    path = ROOT / 'sections/transition_table.tex'
    expected = render()
    if args.check:
        require(path.read_text() == expected, 'Appendix differs from exact machine table')
    else:
        path.write_text(expected)
    print(json.dumps({'status': 'EXACT_TRANSITION_APPENDIX_PASS',
                      'working_states': 238, 'transition_rows': 476,
                      'canonical_sha256': EXPECTED,
                      'mode': 'check' if args.check else 'write'}, indent=2))


if __name__ == '__main__':
    main()
