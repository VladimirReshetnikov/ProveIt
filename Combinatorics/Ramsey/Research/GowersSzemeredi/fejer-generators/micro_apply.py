"""Two more redundant-tactic rewrites, verified by elaboration.

usage: python -X utf8 micro_apply.py MODULE [MODULE ...]
  * `apply f` followed by a single-line `exact h` that closes the block  ->  `exact f h`
    (skipped for `apply ... at`, `<;>`, `;`, comments, and lines that would pass 100 characters);
  * `... := by` followed by a lone `rfl` that is the whole block  ->  `... := rfl`.
Only inside theorem/lemma/example proofs.  Engine: micro_simplify2.py (apply all, elaborate, restore
declarations that report errors, re-elaborate, bisect as fallback).
"""
import re
from pathlib import Path

HERE = Path(__file__).resolve().parent
src = (HERE / 'micro_simplify2.py').read_text(encoding='utf8').replace('\nmain()\n', '\n')
m2 = {'__name__': 'm2', '__file__': str(HERE / 'micro_simplify2.py')}
exec(compile(src, 'micro_simplify2.py', 'exec'), m2)
DECL = re.compile(r'^(?:@\[[^\]]*\]\s*)?(?:private |protected )?(?:noncomputable )?(theorem|lemma|def|abbrev|instance|example|structure)\b')


def dind(l):
    return len(l) - len(l.lstrip())


def one_group(t):
    """t is a single parenthesised group `( ... )`."""
    if not (t.startswith('(') and t.endswith(')')):
        return False
    depth = 0
    for k, ch in enumerate(t):
        if ch in '([{⟨':
            depth += 1
        elif ch in ')]}⟩':
            depth -= 1
            if depth == 0 and k != len(t) - 1:
                return False
    return True


def candidates(lines):
    out, kind = [], None
    for i in range(len(lines) - 1):
        d = DECL.match(lines[i])
        if d:
            kind = d.group(1)
        if kind not in ('theorem', 'lemma', 'example'):
            continue
        a, b = lines[i], lines[i + 1]
        n2 = lines[i + 2] if i + 2 < len(lines) else ''
        ma = re.match(r'(\s*)apply (\S.*?)\s*$', a)
        mb = re.match(r'(\s*)exact (\S.*?)\s*$', b)
        if ma and mb and len(ma.group(1)) == len(mb.group(1)) and (not n2.strip() or dind(n2) < len(ma.group(1))):
            f, h = ma.group(2), mb.group(2)
            if not re.search(r'\bat\b|<;>|;|--|\busing\b|\bwith\b', f + ' ' + h):
                hh = h if re.fullmatch(r"[\w'.₀-₉]+", h) or one_group(h) else f'({h})'
                rep = f'{ma.group(1)}exact {f} {hh}'
                if len(rep) <= 100:
                    out.append(('rep', i, i + 2, (rep,)))
            continue
        if a.rstrip().endswith(':= by') and b.strip() == 'rfl' and (not n2.strip() or dind(n2) <= dind(a)):
            rep = a.rstrip()[:-len('by')].rstrip() + ' rfl'
            if len(rep) <= 100:
                out.append(('rep', i, i + 2, (rep,)))
    return out


def apply(lines, cands):
    out = list(lines)
    for kind, a, b, rep in sorted(cands, key=lambda c: -c[1]):
        out[a:b] = list(rep)
    return '\n'.join(out)


m2['candidates'] = candidates
m2['apply'] = apply

if __name__ == '__main__':
    m2['main']()
