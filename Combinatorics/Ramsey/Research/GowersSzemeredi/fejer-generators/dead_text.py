"""Unused declarations on the final route, by text (no dependency dump needed).

usage: python -X utf8 dead_text.py
A declaration of a final-route module is reported when its short name occurs in no .lean file of the
corpus apart from its own header (comments stripped; dot-notation uses count). Instances, declarations
with attributes, and paper-named results are skipped. Each candidate is listed with its line count
and the non-Lean files (outside verification/ and the generator scripts) that mention it.
"""
import os
import re
import subprocess
from pathlib import Path

ROOT = Path(r'C:\ProveIt\.claude\worktrees\q-fabius-deformations-merge-9bc27b')
GS = ROOT / 'Combinatorics/Ramsey/Lean/GowersSzemeredi'
PAPER = re.compile(r"^(lemma|theorem|corollary|proposition|prop|cor)_?\d|_holds$")
HD = re.compile(r"^(@\[[^\]]*\]\s*)?(private |protected )?(noncomputable )?(theorem|lemma|def|abbrev|structure|instance)\s+([^\s(:{\[]+)", re.M)


def imports(m):
    return re.findall(r'^import GowersSzemeredi\.(\S+)', (GS / f'{m}.lean').read_text(encoding='utf8'), re.M)


final, st = {'Proofs18Final'}, ['Proofs18Final']
while st:
    x = st.pop()
    for d in imports(x):
        if d not in final:
            final.add(d)
            st.append(d)

texts = {}
for p in list(GS.glob('*.lean')) + list((ROOT / 'Combinatorics/Ramsey/Lean').glob('*.lean')):
    t = p.read_text(encoding='utf8')
    texts[p] = re.sub(r'--[^\n]*', ' ', re.sub(r'/-.*?-/', lambda m: ' ' * len(m.group(0)), t, flags=re.S))
counts = {}
for t in texts.values():
    for w in re.findall(r"[A-Za-z_][\w'.₀-₉?!]*", t):
        for part in w.split('.'):
            counts[part] = counts.get(part, 0) + 1

cands = []
for m in sorted(final):
    s = (GS / f'{m}.lean').read_text(encoding='utf8')
    hs = list(HD.finditer(s))
    for k, h in enumerate(hs):
        if h.group(1) or h.group(4) in ('instance', 'structure'):
            continue
        name = h.group(5).split('.')[-1]
        if PAPER.search(name) or len(name) < 4:
            continue
        if counts.get(name, 0) <= 1:
            e = hs[k + 1].start() if k + 1 < len(hs) else len(s)
            cands.append((m, h.group(5), s[h.start():e].count('\n'), bool(h.group(2))))
print(len(cands), 'candidates')
for m, n, lines, priv in cands:
    short = n.split('.')[-1]
    r = subprocess.run(['git', '-C', str(ROOT), 'grep', '-l', '-w', short, '--', 'Combinatorics/Ramsey',
                        ':!*.lean', ':!**/verification/**', ':!**/fejer-generators/**'],
                       capture_output=True, text=True)
    docs = ' '.join(os.path.basename(x) for x in r.stdout.split())
    print(f'{lines:4} {"P" if priv else " "} {m}.{n}  [{docs}]')
