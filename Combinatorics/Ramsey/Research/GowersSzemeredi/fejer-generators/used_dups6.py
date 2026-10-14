"""Near-duplicate pairs among declarations the final theorems use (both sides used, module-qualified).

usage: python -X utf8 used_dups6.py USED_RANGES MIN_LINES
Prints every pair with similarity >= 0.90, then the module pairs ranked by total duplicated lines.
"""
import collections
import difflib
import os
import re
import sys

GS = r'C:\ProveIt\.claude\worktrees\q-fabius-deformations-merge-9bc27b\Combinatorics\Ramsey\Lean\GowersSzemeredi'
min_lines = int(sys.argv[2])
used = collections.defaultdict(set)
for l in open(sys.argv[1], encoding='utf8'):
    m, n, a, b = l.split()
    used[m.split('.', 1)[1]].add(n.split('.')[-1])
bodies = []
for f in os.listdir(GS):
    if not f.endswith('.lean') or 'Audit' in f:
        continue
    mod = f[:-5]
    s = open(os.path.join(GS, f), encoding='utf8').read()
    for p in re.split(r'\n(?=(?:theorem|lemma|def|private lemma|private theorem) )', s):
        m = re.match(r'(?:private )?(?:theorem|lemma|def) (\S+)', p)
        if m and m.group(1).split('.')[-1] in used.get(mod, ()) and p.count('\n') >= min_lines:
            bodies.append((mod, m.group(1), p))
print(len(bodies), f'used decls >= {min_lines} lines', flush=True)
KEEP = {'have', 'obtain', 'exact', 'refine', 'rw', 'by', 'fun', 'calc', 'simp', 'omega', 'linarith'}
norm = lambda t: re.sub(r"[A-Za-z_][\w']*", lambda m: m.group(0) if m.group(0) in KEEP else 'X', t)
nb = sorted(((f, n, norm(b), b.count('\n')) for f, n, b in bodies), key=lambda x: len(x[2]))
res = []
for i in range(len(nb)):
    fi, ni, bi, li = nb[i]
    for j in range(i + 1, len(nb)):
        fj, nj, bj, lj = nb[j]
        if len(bj) > 1.2 * len(bi):
            break
        if fi == fj and ni == nj:
            continue
        sm = difflib.SequenceMatcher(None, bi, bj, autojunk=False)
        if sm.real_quick_ratio() < 0.9 or sm.quick_ratio() < 0.9:
            continue
        r = sm.ratio()
        if r >= 0.9:
            res.append((r, li, lj, fi, ni, fj, nj))
res.sort(reverse=True)
for r, li, lj, fi, ni, fj, nj in res:
    print(f'{r:.2f} {li:3}/{lj:3} {fi}.{ni}  ~  {fj}.{nj}', flush=True)
print(len(res), 'pairs >= 0.90')
groups = collections.Counter()
for r, li, lj, fi, ni, fj, nj in res:
    groups[tuple(sorted((fi, fj)))] += min(li, lj)
print('module pairs by duplicated lines:')
for (a, b), n in groups.most_common(25):
    print(f'{n:5} {a} ~ {b}')
