"""Families of identical-statement lemmas where one member can host the others after adding an import.

usage: python -X utf8 share_groups7.py MAX_NEW_MODULES out.json
For each family (same leading-binder-normalised statement, same namespace, unattributed, all member
modules built), pick a host member h such that, for every other member module x,
  * h is not a descendant of x (the import `x -> h` creates no cycle),
  * importing h adds at most MAX_NEW_MODULES proof modules to x's closure;
and the host's name, if the host copy is private, is declared nowhere else.  Families whose
statement mentions a name declared `private` in some member module are skipped (the copies talk
about different private definitions).  Output is in apply_share.py format plus `imports`.
"""
import collections
import json
import os
import re
import sys

import stmtx

GS = r'C:\ProveIt\.claude\worktrees\q-fabius-deformations-merge-9bc27b\Combinatorics\Ramsey\Lean\GowersSzemeredi'
OUT = r'C:\ProveIt\.claude\worktrees\q-fabius-deformations-merge-9bc27b\.lake\build\lib\lean\GowersSzemeredi'
LIMIT = int(sys.argv[1])
mods = [f[:-5] for f in os.listdir(GS) if f.endswith('.lean')]
src = {m: open(os.path.join(GS, m + '.lean'), encoding='utf8').read() for m in mods}
imp = {m: re.findall(r'^import GowersSzemeredi\.(\S+)', src[m], re.M) for m in mods}
memo = {}


def anc(m):
    if m not in memo:
        s = set()
        memo[m] = s
        for d in imp.get(m, []):
            s |= {d} | anc(d)
    return memo[m]


def ns_at(m, pos):
    stack = []
    for line in src[m][:pos].split('\n'):
        a = re.match(r'namespace (\S+)', line)
        b = re.match(r'end (\S+)', line)
        if a:
            stack.append(a.group(1))
        elif b and stack and stack[-1] == b.group(1):
            stack.pop()
    return '.'.join(stack)


built = {m for m in mods if os.path.exists(os.path.join(OUT, m + '.olean'))}
DECL = re.compile(r"^(?:@\[[^\]]*\]\s*)?(private |protected )?(?:noncomputable )?"
                  r"(?:theorem|lemma|def|abbrev|structure|inductive|instance|class) ([^\s(:{\[]+)", re.M)
declared = collections.defaultdict(set)
private = collections.defaultdict(set)
for m in mods:
    for d in DECL.finditer(src[m]):
        declared[d.group(2)].add(m)
        if d.group(1) == 'private ':
            private[m].add(d.group(2))
HEAD = re.compile(r'^((?:@\[[^\]]*\]\s*)?)(private )?(theorem|lemma) (\S+)', re.M)
END = re.compile(r'\n\n(?=\S)')
IDENT = re.compile(r"(?<![\w.'])[A-Za-z_][\w']*")

decls = []
for m in mods:
    if 'Audit' in m or not m.startswith('Proofs') or m not in built:
        continue
    s = src[m]
    for mm in HEAD.finditer(s):
        name = mm.group(4)
        if '.' in name or mm.group(1).strip():
            continue
        j = stmtx.statement_end(s, mm.end())
        if j < 0 or '\n\n' in s[mm.end():j]:
            continue
        e = END.search(s, j)
        lines = s[mm.start():e.start() if e else len(s)].count('\n') + 1
        raw = s[mm.end():j]
        decls.append(dict(key=(ns_at(m, mm.start()), stmtx.normalise(raw)), raw=raw, mod=m, name=name,
                          private=bool(mm.group(2)), lines=lines))
fam = collections.defaultdict(list)
for d in decls:
    fam[d['key']].append(d)
res = []
for key, ms in fam.items():
    mset = {d['mod'] for d in ms}
    if len(mset) < 2 or len(mset) != len(ms):
        continue
    toks = set(IDENT.findall(ms[0]['raw']))
    if any(toks & private[d['mod']] for d in ms):
        continue
    best = None
    for h in ms:
        others = [x for x in ms if x is not h]
        if any(h['mod'] in anc(x['mod']) | {x['mod']} and False for x in others):
            continue
        if any(x['mod'] in anc(h['mod']) for x in others):
            continue  # x upstream of h: importing h into x would be a cycle
        cost = max(len((anc(h['mod']) | {h['mod']}) - anc(x['mod']) - {x['mod']}) for x in others)
        if cost > LIMIT:
            continue
        if h['private'] and declared[h['name']] - mset:
            continue
        if any(not x['private'] and x['name'] == h['name'] for x in others):
            pass  # deleted outright, same name
        if best is None or cost < best[0]:
            best = (cost, h, others)
    if best is None:
        continue
    cost, h, others = best
    # a public copy elsewhere with the host's name would collide once the host is visible there
    if any(declared[h['name']] - mset for _ in [0]) and not h['private']:
        clash = declared[h['name']] - mset
        if clash:
            continue
    res.append(dict(host=h['mod'], name=h['name'], host_private=h['private'], cost=cost,
                    imports=sorted(x['mod'] for x in others if h['mod'] not in anc(x['mod'])),
                    others=[dict(mod=x['mod'], name=x['name'], private=x['private'], lines=x['lines'])
                            for x in others],
                    saved=sum(x['lines'] for x in others)))
res.sort(key=lambda r: -r['saved'])
json.dump(res, open(sys.argv[2], 'w', encoding='utf8'), indent=1)
for r in res:
    print(f"{r['saved']:4} +{r['cost']:<3} {r['host']}.{r['name']} <- " +
          ', '.join(f"{o['mod']}.{o['name']}" for o in r['others']) +
          (f"  [import into {', '.join(r['imports'])}]" if r['imports'] else ''))
print(len(res), 'groups,', sum(r['saved'] for r in res), 'lines')
