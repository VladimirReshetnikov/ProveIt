"""Declarations on the final route that are copies of each other up to renaming module-local names.

usage: python -X utf8 alpha_dups.py [MINLINES]
Each declaration's text (comments stripped) is tokenised; identifiers declared in the same module
are replaced by placeholders numbered by first occurrence (the declaration's own name by SELF).
Declarations with equal normalised token sequences and >= MINLINES lines are grouped. Groups are
summarised per module pair with the duplicated line count (all copies but one).
"""
import collections
import re
import sys
from pathlib import Path

GS = Path(r'C:\ProveIt\.claude\worktrees\q-fabius-deformations-merge-9bc27b\Combinatorics\Ramsey\Lean\GowersSzemeredi')
MIN = int(sys.argv[1]) if len(sys.argv) > 1 else 4
HD = re.compile(r"^(?:@\[[^\]]*\]\s*)?(private |protected )?(?:noncomputable )?"
                r"(theorem|lemma|def|abbrev|structure|instance|inductive|class)\s+([^\s(:{\[]+)", re.M)
TOP = re.compile(r"^(?:/--|@\[|(?:private |protected )?(?:noncomputable )?"
                 r"(?:theorem|lemma|def|abbrev|instance|structure|inductive|class|attribute|alias)\b"
                 r"|end |namespace |section|open |variable|/-!|set_option)", re.M)
TOK = re.compile(r"[A-Za-z_\u0370-\u03ff\u1d00-\u1dbf\u2070-\u209f][\w'.\u2080-\u2089\u0370-\u03ff]*|\S")


def imports(m):
    return re.findall(r'^import GowersSzemeredi\.(\S+)', (GS / f'{m}.lean').read_text(encoding='utf8'), re.M)


seen, st = {'Proofs18Final'}, ['Proofs18Final']
while st:
    x = st.pop()
    for d in imports(x):
        if d not in seen:
            seen.add(d)
            st.append(d)

groups = collections.defaultdict(list)
for m in sorted(seen):
    s = (GS / f'{m}.lean').read_text(encoding='utf8')
    s = re.sub(r'/-.*?-/', lambda t: '\n' * t.group(0).count('\n'), s, flags=re.S)
    s = re.sub(r'--[^\n]*', '', s)
    hs = list(HD.finditer(s))
    local = {h.group(3).split('.')[-1] for h in hs}
    tops = sorted({t.start() for t in TOP.finditer(s)})
    for h in hs:
        nxt = [t for t in tops if t > h.end()]
        e = nxt[0] if nxt else len(s)
        body = s[h.end():e]
        lines = [l for l in body.split('\n') if l.strip()]
        if len(lines) + 1 < MIN:
            continue
        names, out = {}, []
        for t in TOK.findall(body):
            base = t.split('.')[-1] if '.' in t else t
            if base == h.group(3).split('.')[-1]:
                out.append('SELF')
            elif t in local or base in local and t.endswith(base):
                key = t
                if key not in names:
                    names[key] = f'L{len(names)}'
                out.append(names[key])
            else:
                out.append(t)
        groups[(h.group(2), tuple(out))].append((m, h.group(3), len(lines) + 1, bool(h.group(1))))

pairs = collections.Counter()
detail = collections.defaultdict(list)
for key, mem in groups.items():
    if len(mem) < 2:
        continue
    mods = sorted({x[0] for x in mem})
    size = mem[0][2]
    dup = size * (len(mem) - 1)
    k = ' ~ '.join(mods) if len(mods) > 1 else mods[0] + ' (within)'
    pairs[k] += dup
    detail[k].append((size, [f"{x[1]}{'(p)' if x[3] else ''}" for x in mem]))
tot = 0
for k, v in pairs.most_common():
    tot += v
    print(f'{v:5}  {k}')
    for size, names in sorted(detail[k], reverse=True)[:6]:
        print(f'         {size:4}  ' + ' | '.join(names)[:160])
print('total duplicated lines:', tot)
