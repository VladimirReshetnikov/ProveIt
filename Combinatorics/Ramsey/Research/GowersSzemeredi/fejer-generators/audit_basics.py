"""Every member removed by apply_basics must state (at BASE) what its Proofs00Basics copy states
(in the working tree).  usage: python -X utf8 audit_basics.py BASE basics_plan.json"""
import json
import os
import re
import subprocess
import sys

import stmtx

ROOT = r'C:\ProveIt\.claude\worktrees\q-fabius-deformations-merge-9bc27b'
REL = 'Combinatorics/Ramsey/Lean/GowersSzemeredi/'
base = sys.argv[1]
hosted = open(os.path.join(ROOT, REL, 'Proofs00Basics.lean'), encoding='utf8').read()


def stmt(s, n):
    mm = re.search(r"^(?:@\[[^\]]*\]\s*)?(?:private )?(?:theorem|lemma) " + re.escape(n) + r"(?![\w'])", s, re.M)
    return None if not mm else stmtx.normalise(stmtx.statement(s, mm.end()))


ok = bad = 0
for p in json.load(open(sys.argv[2], encoding='utf8')):
    h = stmt(hosted, p['name'])
    if h is None:
        continue  # family skipped
    for m in p['members']:
        s = subprocess.run(['git', '-C', ROOT, 'show', f"{base}:{REL}{m['mod']}.lean"], capture_output=True,
                           encoding='utf8').stdout
        if stmt(s, m['name']) == h:
            ok += 1
        else:
            bad += 1
            print('DIFFER', p['name'], '<-', m['mod'] + '.' + m['name'])
print(ok, 'equal,', bad, 'different')
