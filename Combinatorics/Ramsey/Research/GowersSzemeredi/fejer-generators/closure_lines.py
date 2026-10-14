"""Total source lines of the GowersSzemeredi import closure of a root module at given revisions.
usage: closure_lines.py ROOT_MODULE REV [REV ...]"""
import re
import subprocess
import sys

ROOT = r'C:\ProveIt\.claude\worktrees\q-fabius-deformations-merge-9bc27b'
REL = 'Combinatorics/Ramsey/Lean/'


def show(rev, mod):
    return subprocess.run(['git', '-C', ROOT, 'show', f'{rev}:{REL}{mod.replace(".", "/")}.lean'],
                          capture_output=True, encoding='utf8').stdout


for rev in sys.argv[2:]:
    seen, st, total = set(), [sys.argv[1]], 0
    while st:
        m = st.pop()
        t = show(rev, m)
        total += t.count('\n')
        for d in re.findall(r'^import (GowersSzemeredi\.\S+)', t, re.M):
            if d not in seen:
                seen.add(d)
                st.append(d)
    print(rev, len(seen) + 1, 'modules', total, 'lines')
