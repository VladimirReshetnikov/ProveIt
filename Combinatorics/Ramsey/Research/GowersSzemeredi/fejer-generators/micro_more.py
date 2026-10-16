"""Three more two-line tactic patterns folded into one, verified by elaboration.

usage: python -X utf8 micro_more.py MODULE [MODULE ...]
In theorem/lemma/example proofs, when the second line closes the block:
  * `intro x` + `exact e`            ->  `exact fun x => e`
  * `refine F` (one `?_`) + `exact h` ->  `exact F[?_ := h]`
  * `have h := e` + `simpa using h`   ->  `simpa using e`
Skipped when the result passes 100 characters or a line holds a comment, `<;>` or `;`.
Engine: micro_simplify2.py (apply all, elaborate, restore failing declarations, re-elaborate).
"""
import re
from pathlib import Path

HERE = Path(__file__).resolve().parent
src = (HERE / 'micro_simplify2.py').read_text(encoding='utf8').replace('\nmain()\n', '\n')
m2 = {'__name__': 'm2', '__file__': str(HERE / 'micro_simplify2.py')}
exec(compile(src, 'micro_simplify2.py', 'exec'), m2)
DECL = re.compile(r'^(?:@\[[^\]]*\]\s*)?(?:private |protected )?(?:noncomputable )?(theorem|lemma|def|abbrev|instance|example|structure)\b')
BAD = re.compile(r'--|<;>|;')


def dind(l):
    return len(l) - len(l.lstrip())


def one_group(t):
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
        if dind(a) != dind(b) or not (not n2.strip() or dind(n2) < dind(a)) or BAD.search(a + b):
            continue
        ind = ' ' * dind(a)
        rep = None
        mi = re.match(r'\s*intro (\S+)\s*$', a)
        mb = re.match(r'\s*exact (\S.*?)\s*$', b)
        if mi and mb:
            rep = f'{ind}exact fun {mi.group(1)} => {mb.group(1)}'
        mr = re.match(r'\s*refine (\S.*?)\s*$', a)
        if rep is None and mr and mb and mr.group(1).count('?_') == 1:
            h = mb.group(1)
            hh = h if re.fullmatch(r"[\w'.₀-₉]+", h) or one_group(h) else f'({h})'
            rep = f"{ind}exact {mr.group(1).replace('?_', hh)}"
        mh = re.match(r'\s*have (\S+) := (\S.*?)\s*$', a)
        if rep is None and mh and b.strip() == f'simpa using {mh.group(1)}':
            rep = f'{ind}simpa using {mh.group(2)}'
        if rep and len(rep) <= 100:
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
