"""Groups of used lemmas with identical statements (up to their own name) that can share one public copy.

usage: python -X utf8 share_groups.py USED_RANGES out.json
A group qualifies when some member module (the host) is an ancestor of every other member module, every
member module has a local olean, and making the host copy public under its own name collides with no
other declaration of that name in any module downstream of the host.
"""
import collections
import json
import os
import re
import sys

import stmtx
normalise = stmtx.normalise

GS = r'C:\ProveIt\.claude\worktrees\q-fabius-deformations-merge-9bc27b\Combinatorics\Ramsey\Lean\GowersSzemeredi'
OUT = r'C:\ProveIt\.claude\worktrees\q-fabius-deformations-merge-9bc27b\.lake\build\lib\lean\GowersSzemeredi'
mods = [f[:-5] for f in os.listdir(GS) if f.endswith('.lean')]
src = {m: open(os.path.join(GS, m + '.lean'), encoding='utf8').read() for m in mods}
imp = {m: re.findall(r'^import GowersSzemeredi\.(\S+)', src[m], re.M) for m in mods}
rev = collections.defaultdict(set)
for m, ds in imp.items():
    for d in ds:
        rev[d].add(m)
memo = {}


def anc(m):
    if m not in memo:
        s = set()
        memo[m] = s
        for d in imp.get(m, []):
            s |= {d} | anc(d)
    return memo[m]


def desc(m):
    s, st = set(), [m]
    while st:
        x = st.pop()
        for y in rev[x]:
            if y not in s:
                s.add(y)
                st.append(y)
    return s


used = collections.defaultdict(set)
for l in []:
    m, n, a, b = l.split()
    used[m.split('.', 1)[1]].add(n.split('.')[-1])

BINDER = re.compile(r'[({\[]\s*([^:(){}\[\]]+?)\s*:')
TOKEN = re.compile(r"[A-Za-z_\u0370-\u03ff][\w'\u0370-\u03ff]*")


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


def _old_normalise(stmt):
    stmt = ' '.join(stmt.replace('↦', '=>').split())
    names = []
    for b in BINDER.finditer(stmt):
        for n in b.group(1).split():
            if TOKEN.fullmatch(n) and n not in names:
                names.append(n)
    ren = {n: f'v{i}' for i, n in enumerate(names)}
    return TOKEN.sub(lambda t: ren.get(t.group(0), t.group(0)), stmt)



decls = []
HEAD = re.compile(r'^((?:@\[[^\]]*\]\s*)?)(private )?(theorem|lemma) (\S+)', re.M)
for m in mods:
    if 'Audit' in m:
        continue
    s = src[m]
    for mm in HEAD.finditer(s):
        name = mm.group(4)
        if '.' in name or not m.startswith('Proofs'):
            continue
        j = stmtx.statement_end(s, mm.end())
        if j < 0:
            continue
        stmt = normalise(s[mm.end():j])
        if '\n\n' in s[mm.end():j]:
            continue
        end = re.compile(r'\n\n(?=\S)').search(s, j)
        body_lines = s[mm.start():end.start() if end else len(s)].count('\n') + 1
        if mm.group(1).strip():
            continue
        decls.append((stmt, m, name, bool(mm.group(2)), body_lines))

groups = collections.defaultdict(list)
for stmt, m, name, priv, n in decls:
    groups[stmt].append((m, name, priv, n))
res = []
for stmt, members in groups.items():
    if len({m for m, *_ in members}) < 2:
        continue
    todo = sorted(members, key=lambda x: len(anc(x[0])))
    while todo:
        host, hname, hpriv, hn = todo.pop(0)
        others = [x for x in todo if host in anc(x[0])]
        if not others:
            continue
        if not all(os.path.exists(os.path.join(OUT, x[0] + '.olean')) for x in others + [(host,)]):
            continue
        member_mods = {x[0] for x in others}
        bad = [d for d in mods
               if d not in member_mods and d != host and 'Audit' not in d
               and re.search(r'^(?:private )?(?:theorem|lemma|def|abbrev) ' + re.escape(hname) + r"(?![\w'])", src[d], re.M)]
        if hname == 'centeredAbs_add_le':
            print('DEBUG', host, hname, 'bad=', bad, file=sys.stderr)
        if bad:
            continue
        todo = [x for x in todo if x not in others]
        res.append({'host': host, 'name': hname, 'host_private': hpriv,
                    'others': [{'mod': m, 'name': n, 'private': p, 'lines': k} for m, n, p, k in others],
                    'saved': sum(k for *_, k in others)})
res.sort(key=lambda r: -r['saved'])
json.dump(res, open(sys.argv[2], 'w', encoding='utf8'), indent=1)
for r in res:
    print(f"{r['saved']:4} {r['host']}.{r['name']} <- " + ', '.join(f"{o['mod']}.{o['name']}" for o in r['others']))
print(len(res), 'groups,', sum(r['saved'] for r in res), 'lines')
