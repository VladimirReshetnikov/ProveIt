"""Turn proof blocks `:= by` + a single `exact e` into the term `:= e`.

usage: python -X utf8 micro_byexact.py MODULE [MODULE ...]
Candidate: a line ending in `:= by` inside a theorem/lemma/example (including its `have`s and `calc`
steps) whose block is exactly one line `exact e` (single-line `e`).  Rewritten to `... := e` when it
fits in 100 columns, else to `... :=` followed by `e` on the next line.  Verified with the error-
attribution engine of micro_simplify2.py (apply all, elaborate, restore failing declarations,
re-elaborate, bisect as fallback).
"""
import re
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
src = (HERE / 'micro_simplify2.py').read_text(encoding='utf8').replace('\nmain()\n', '\n')
m2 = {'__name__': 'm2', '__file__': str(HERE / 'micro_simplify2.py')}
exec(compile(src, 'micro_simplify2.py', 'exec'), m2)
DECL = re.compile(r'^(?:@\[[^\]]*\]\s*)?(?:private |protected )?(?:noncomputable )?(theorem|lemma|def|abbrev|instance|example|structure)\b')


def candidates(lines):
    out, kind = [], None
    for i in range(len(lines) - 1):
        d = DECL.match(lines[i])
        if d:
            kind = d.group(1)
        a, b = lines[i], lines[i + 1]
        if kind not in ('theorem', 'lemma', 'example') or not a.rstrip().endswith(':= by'):
            continue
        mb = re.match(r'(\s*)exact\s+(\S.*?)\s*$', b)
        if not mb:
            continue
        ia, ib = len(a) - len(a.lstrip()), len(mb.group(1))
        nxt = lines[i + 2] if i + 2 < len(lines) else ''
        if ib <= ia or (nxt.strip() and len(nxt) - len(nxt.lstrip()) > ia):
            continue
        term = mb.group(2)
        if '--' in term:
            continue
        head = a.rstrip()[:-len('by')].rstrip()          # ends with `:=`
        one = f'{head} {term}'
        rep = [one] if len(one) <= 100 else [head, ' ' * (ia + 4 if head.lstrip().startswith(('theorem', 'lemma', 'private', 'example')) else ia + 2) + term]
        out.append(('rep', i, i + 2, tuple(rep)))
    return out


def apply(lines, cands):
    out = list(lines)
    for kind, a, b, rep in sorted(cands, key=lambda c: -c[1]):
        out[a:b] = list(rep)
    return '\n'.join(out)


m2['candidates'] = candidates
m2['apply'] = apply
m2['main'].__globals__['candidates'] = candidates
m2['main'].__globals__['apply'] = apply


def saved(kept):
    return sum((b - a) - len(rep) for _, a, b, rep in kept)


if __name__ == '__main__':
    m2['main']()
