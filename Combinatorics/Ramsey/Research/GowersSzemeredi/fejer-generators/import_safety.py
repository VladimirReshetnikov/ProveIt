"""Safety of the imports share_groups7 proposes.  usage: import_safety.py share_groups7.json out.json

For each proposed import x -> h: N = closure(h) - closure(x) are the newly visible modules, D the
descendants of x (with x).  The import is SAFE when either every module of D is built locally
(the forced rebuild then covers all of D), or N declares nothing with a global effect (simp/ext/
instance/attribute/notation/macro/syntax) and no public name of N is declared in D.
Writes the safe groups (with `extra_rebuild`: the descendants to rebuild) to out.json."""
import collections
import json
import os
import re
import sys

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
    s, st = {m}, [m]
    while st:
        for y in rev[st.pop()]:
            if y not in s:
                s.add(y)
                st.append(y)
    return s


built = {m for m in mods if os.path.exists(os.path.join(OUT, m + '.olean'))}
GLOBAL = re.compile(r'@\[[^\]]*\b(simp|ext|instance|norm_cast|push_cast|fun_prop|gcongr|positivity)\b|'
                    r'^\s*(instance|attribute \[|notation|infix|prefix|postfix|macro|syntax|elab|scoped)', re.M)
DECL = re.compile(r"^(?:@\[[^\]]*\]\s*)?(private |protected )?(?:noncomputable )?"
                  r"(?:theorem|lemma|def|abbrev|structure|inductive|instance|class) ([^\s(:{\[]+)", re.M)
pub = {m: {d.group(2) for d in DECL.finditer(src[m]) if not d.group(1)} for m in mods}
alld = {m: {d.group(2) for d in DECL.finditer(src[m])} for m in mods}
safe = []
for g in json.load(open(sys.argv[1], encoding='utf8')):
    h = g['host']
    ok, extra, why = True, set(), []
    for x in g['imports']:
        N = (anc(h) | {h}) - anc(x) - {x}
        D = desc(x)
        heavy = D - built
        glob = sorted(n for n in N if GLOBAL.search(src[n]))
        names = set().union(*(pub[n] for n in N)) if N else set()
        clash = sorted({(d, nm) for d in D for nm in alld[d] & names})
        if not glob and not clash:
            continue  # nothing new can change how any descendant elaborates
        if not heavy:
            extra |= D
            continue
        ok = False
        why.append(f"{x}: {len(heavy)} heavy descendants; global-effect in {glob[:3]}; clashes {clash[:3]}")
    print(('SAFE  ' if ok else 'UNSAFE'), g['saved'], g['host'] + '.' + g['name'], '|', '; '.join(why)[:200])
    if ok:
        g['extra_rebuild'] = sorted(extra)
        safe.append(g)
json.dump(safe, open(sys.argv[2], 'w', encoding='utf8'), indent=1)
print(len(safe), 'safe groups,', sum(g['saved'] for g in safe), 'lines; extra rebuild',
      len(set().union(*(set(g['extra_rebuild']) for g in safe))) if safe else 0)
