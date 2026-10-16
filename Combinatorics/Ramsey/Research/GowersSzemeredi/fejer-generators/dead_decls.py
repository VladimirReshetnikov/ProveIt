"""Declarations of final-route proof modules that nothing uses.

usage: dead_decls.py decl_needs2.txt final_by_size.txt out.json
A declaration is dead when
  * no other declaration of the Proofs18Final environment uses it (auxiliary constants folded in),
  * its short name occurs nowhere else in any .lean file of the corpus (comments stripped), including
    modules outside the final route, heavy modules and audits,
  * it is not mentioned in any non-Lean file of the repository,
  * it is not paper-named (lemma_/theorem_/corollary_/proposition_/prop_/cor_ followed by a digit, or
    ending in _holds), not an instance, and carries no attribute.
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
                 r"_unary|_mutual|proof_\d+|induct|_sunfold|_cstage\d+|_private.*)$")


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
others = []
for dp, dn, fn in os.walk(os.path.join(ROOT, 'Combinatorics', 'Ramsey', 'Lean')):
    for f in fn:
        if f.endswith('.lean') and not os.path.join(dp, f).startswith(GS + os.sep):
            others.append(open(os.path.join(dp, f), encoding='utf8', errors='replace').read())
code = [re.sub(r'--[^\n]*', '', re.sub(r'/-.*?-/', '', t, flags=re.S)) for t in list(srcs.values()) + others]
tok = collections.Counter()
for t in code:
    for w in re.findall(r"[A-Za-z_\u0370-\u03ff][\w'.\u0370-\u03ff₀-₉]*", t):
        tok[w.split('.')[-1]] += 1
nonlean = subprocess.run(['git', '-C', ROOT, 'grep', '-h', '-o', '-I', r'\b[A-Za-z_][A-Za-z0-9_.]*\b', '--',
                          ':!*.lean'], capture_output=True, text=True, encoding='utf8', errors='replace').stdout
cited = {w.split('.')[-1] for w in nonlean.split()}
PAPER = re.compile(r'^(lemma|theorem|corollary|proposition|prop|cor)_?\d|_holds$')
DECL = re.compile(r"^(@\[[^\]]*\]\s*)?(private |protected )?(?:noncomputable )?(theorem|lemma|def|abbrev) ([^\s(:{\[]+)", re.M)
by_mod_short = collections.defaultdict(list)
for k, v in owner.items():
    by_mod_short[(v, k.split('.')[-1])].append(k)
res = []
for m in sorted(final):
    if not m.startswith('Proofs'):
        continue
    s = srcs[m]
    for d in DECL.finditer(s):
        if d.group(1):
            continue
        short = d.group(4).split('.')[-1]
        if PAPER.search(short) or short in cited:
            continue
        full = by_mod_short.get(('GowersSzemeredi.' + m, short), [])
        if len(full) != 1 or users.get(full[0]):
            continue
        if tok[short] != 1:
            continue
        e = re.compile(r'\n\n(?=\S)').search(s, d.end())
        a = d.start()
        doc = s.rfind('/--', 0, a)
        if doc != -1 and s[s.index('-/', doc) + 2:a].strip() == '':
            a = doc
        nlines = s[a:e.start() if e else len(s)].count('\n') + 1
        res.append(dict(mod=m, name=d.group(4), kind=d.group(3), private=bool(d.group(2)), lines=nlines))
json.dump(res, open(sys.argv[3], 'w', encoding='utf8'), indent=1)
print(len(res), 'dead declarations,', sum(r['lines'] for r in res), 'lines;',
      dict(collections.Counter(r['kind'] for r in res)), 'private:', sum(r['private'] for r in res))
for r in sorted(res, key=lambda r: -r['lines'])[:30]:
    print(f"{r['lines']:4} {r['kind']:7} {'priv' if r['private'] else 'pub '} {r['mod']}.{r['name']}")
