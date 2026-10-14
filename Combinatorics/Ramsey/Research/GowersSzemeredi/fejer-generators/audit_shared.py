"""Audit committed share batches: did every removed copy state the same thing as its host?

usage: python -X utf8 audit_shared.py BASE_COMMIT json [json ...]
Statements are read at BASE_COMMIT with the depth/let-aware extractor and compared after
whitespace and binder-name normalisation.  Only groups whose removed copy is gone at HEAD count.
"""
import json
import os
import re
import subprocess
import sys

import stmtx
normalise = stmtx.normalise

ROOT = r'C:\ProveIt\.claude\worktrees\q-fabius-deformations-merge-9bc27b'
REL = 'Combinatorics/Ramsey/Lean/GowersSzemeredi/'
BINDER = re.compile(r'[({\[⦃]\s*([^:(){}\[\]⦃⦄]+?)\s*:')
TOKEN = re.compile(r"[A-Za-z_\u0370-\u03ff][\w'\u0370-\u03ff]*")
base = sys.argv[1]
cache = {}


def at(rev, m):
    k = (rev, m)
    if k not in cache:
        if rev == 'WT':
            cache[k] = open(os.path.join(ROOT, REL, m + '.lean'), encoding='utf8').read()
        else:
            cache[k] = subprocess.run(['git', '-C', ROOT, 'show', f'{rev}:{REL}{m}.lean'], capture_output=True,
                                      encoding='utf8').stdout
    return cache[k]


def _old_normalise(stmt):
    stmt = ' '.join(stmt.replace('↦', '=>').split())
    names = []
    for b in BINDER.finditer(stmt):
        for n in b.group(1).split():
            if TOKEN.fullmatch(n) and n not in names:
                names.append(n)
    ren = {n: f'v{i}' for i, n in enumerate(names)}
    return TOKEN.sub(lambda t: ren.get(t.group(0), t.group(0)), stmt)


def stmt_of(rev, m, n):
    s = at(rev, m)
    mm = re.search(r"^(?:@\[[^\]]*\]\s*)?(?:private )?(?:theorem|lemma) " + re.escape(n) + r"(?![\w'])", s, re.M)
    if not mm:
        return None
    t = stmtx.statement(s, mm.end())
    return None if t is None else normalise(t)


def declared(rev, m, n):
    return re.search(r"^(?:@\[[^\]]*\]\s*)?(?:private )?(?:theorem|lemma) " + re.escape(n) + r"(?![\w'])",
                     at(rev, m), re.M) is not None


bad = ok = 0
for jf in sys.argv[2:]:
    for g in json.load(open(jf, encoding='utf8')):
        if 'members' in g:   # share_groups2 format: host module gets a fresh copy of members[0]
            ref_mod, ref_name = g['members'][0]['mod'], g['members'][0]['name']
            others = g['members'][1:]
        else:
            ref_mod, ref_name = g['host'], g['name']
            others = g['others']
        ref = stmt_of(base, ref_mod, ref_name)
        for o in others:
            if declared('HEAD', o['mod'], o['name']):
                continue  # not applied (or kept)
            st = stmt_of(base, o['mod'], o['name'])
            if st is None or ref is None:
                print('MISSING', jf, ref_mod, ref_name, o['mod'], o['name'])
                continue
            if st != ref:
                bad += 1
                print('DIFFER', os.path.basename(jf), f"{ref_mod}.{ref_name}", '<-', f"{o['mod']}.{o['name']}")
            else:
                ok += 1
print(ok, 'equal,', bad, 'different')
