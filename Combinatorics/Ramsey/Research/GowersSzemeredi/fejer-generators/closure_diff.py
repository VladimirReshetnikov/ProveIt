"""Import closure of a root module at a git revision vs the working tree.
usage: closure_diff.py REV ROOT_MODULE"""
import os
import re
import subprocess
import sys

ROOT = r'C:\ProveIt\.claude\worktrees\q-fabius-deformations-merge-9bc27b'
REL = 'Combinatorics/Ramsey/Lean/'


def imports(rev, mod):
    path = REL + mod.replace('.', '/') + '.lean'
    if rev == 'WT':
        p = os.path.join(ROOT, path)
        t = open(p, encoding='utf8').read() if os.path.exists(p) else ''
    else:
        t = subprocess.run(['git', '-C', ROOT, 'show', f'{rev}:{path}'], capture_output=True, encoding='utf8').stdout
    return [m for m in re.findall(r'^import (\S+)', t, re.M) if not m.startswith(('Mathlib', 'Lean', 'Std', 'Batteries'))]


def closure(rev, root):
    seen, st = set(), [root]
    while st:
        m = st.pop()
        for d in imports(rev, m):
            if d not in seen:
                seen.add(d)
                st.append(d)
    return seen


a, b = closure(sys.argv[1], sys.argv[2]), closure('WT', sys.argv[2])
print(len(a), '->', len(b))
print('added:', sorted(b - a))
print('removed:', sorted(a - b))
