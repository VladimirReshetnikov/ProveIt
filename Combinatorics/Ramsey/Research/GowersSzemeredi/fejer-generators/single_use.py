"""Declarations of final-route proof modules that are used exactly once.

usage: single_use.py decl_needs2.txt final_by_size.txt out.json
Uses = distinct other declarations whose type or value mentions the constant (from the Lean
environment of Proofs18Final, auxiliary `_proof_`/`match_`/`eq_` constants folded into their owner),
cross-checked by a whole-corpus text search of the short name (any .lean file, comments stripped).
A candidate must be used by exactly one declaration, appear in exactly one place in the corpus
besides its own definition, and not be mentioned in any non-Lean file of the repository.
"""
import collections
import json
import os
import re
import subprocess
import sys

ROOT = r'C:\ProveIt\.claude\worktrees\q-fabius-deformations-merge-9bc27b'
GS = os.path.join(ROOT, 'Combinatorics', 'Ramsey', 'Lean', 'GowersSzemeredi')
final = set(open(sys.argv[2]).read().split())
AUX = re.compile(r"\.(_proof_\d+|_proof_\d+_\d+|match_\d+|eq_\d+|eq_def|eq_unfold|congr_simp|_simp_\d+(_\d+)?|"
                 r"_unary|_mutual|proof_\d+|induct|_sunfold|_cstage\d+)$")


def base(n):
    while True:
        b = AUX.sub('', n)
        if b == n:
            return n
        n = b


owner, users = {}, collections.defaultdict(set)
for l in open(sys.argv[1], encoding='utf8'):
    head, ms, same = (l.rstrip('\n').split(' | ') + ['', ''])[:3]
    m, n = head.split(' ', 1)
    b = base(n)
    owner.setdefault(b, m)
    for x in ms.split():
        c = base(x.split(':', 1)[1])
        if c != b:
            users[c].add(b)
    for x in same.split():
        c = base(x)
        if c != b:
            users[c].add(b)
srcs = {f[:-5]: open(os.path.join(GS, f), encoding='utf8').read() for f in os.listdir(GS) if f.endswith('.lean')}
code = {m: re.sub(r'--[^\n]*', '', re.sub(r'/-.*?-/', '', t, flags=re.S)) for m, t in srcs.items()}
nonlean = subprocess.run(['git', '-C', ROOT, 'grep', '-h', '-o', '-I', r'\b[A-Za-z_][A-Za-z0-9_.]*\b', '--',
                          ':!*.lean'], capture_output=True, text=True, encoding='utf8', errors='replace').stdout
cited = set(nonlean.split())
DECL = re.compile(r"^(?:@\[[^\]]*\]\s*)?(private |protected )?(?:noncomputable )?(theorem|lemma|def|abbrev) ([^\s(:{\[]+)", re.M)
tok = collections.Counter()
for t in code.values():
    for w in re.findall(r"[A-Za-z_Ͱ-Ͽ][\w'.Ͱ-Ͽ₀-₉]*", t):
        tok[w.split('.')[-1]] += 1
by_mod_short = collections.defaultdict(list)
for k, v in owner.items():
    by_mod_short[(v, k.split('.')[-1])].append(k)
res = []
for m in sorted(final):
    if not m.startswith('Proofs'):
        continue
    for d in DECL.finditer(srcs[m]):
        short = d.group(3).split('.')[-1]
        full = by_mod_short.get(('GowersSzemeredi.' + m, short), [])
        if len(full) != 1:
            continue
        u = users.get(full[0], set())
        if len(u) != 1:
            continue
        hits = tok[short]
        if hits != 2 or short in cited or d.group(3) in cited:
            continue
        e = re.compile(r'\n\n(?=\S)').search(srcs[m], d.end())
        nlines = srcs[m][d.start():e.start() if e else len(srcs[m])].count('\n') + 1
        user = next(iter(u))
        res.append(dict(mod=m, name=d.group(3), kind=d.group(2), private=bool(d.group(1)), lines=nlines,
                        user=user, user_mod=owner.get(user, '?').split('.')[-1]))
json.dump(res, open(sys.argv[3], 'w', encoding='utf8'), indent=1)
kinds = collections.Counter(r['kind'] for r in res)
print(len(res), 'single-use declarations', dict(kinds), sum(r['lines'] for r in res), 'lines')
print('same-module use:', sum(1 for r in res if r['user_mod'] == r['mod']))
for r in sorted(res, key=lambda r: -r['lines'])[:25]:
    print(f"{r['lines']:4} {r['kind']:7} {'priv' if r['private'] else 'pub '} {r['mod']}.{r['name'][:40]} -> {r['user_mod']}.{r['user'].split('.')[-1][:40]}")
