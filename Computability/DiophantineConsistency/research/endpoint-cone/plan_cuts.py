"""Usage: py plan_cuts.py [ROOT_MODULE]   (ALLOW=glob,glob restricts edited modules)

Plan import cuts that remove term-unused project modules from the endpoint closure.
Reads cone_exact.tsv (reached counts) and module_uses.tsv (exact direct module usage).
A cut A->Z is allowed when A uses nothing of Z; A then imports directly every project
module it uses that its remaining imports no longer cover. Mathlib/Foundation imports
that a cut removes from A's closure are not restored here; restore them before compiling
(notation, namespaces and instances leave no trace in the usage graph)."""
import os, re, json, collections, sys
S = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'out')
os.chdir(os.path.join(os.path.dirname(os.path.abspath(__file__)), *['..'] * 4))
import tomllib
cfg = tomllib.load(open('lakefile.toml', 'rb'))
srcdir = {lib['name']: lib.get('srcDir', '.') for lib in cfg.get('lean_lib', [])}
def path(m):
    d = srcdir.get(m.split('.')[0]); 
    if d is None: return None
    p = os.path.join(d, *m.split('.')) + '.lean'
    return p if os.path.exists(p) else None
rows = [l.split('\t') for l in open(S + '/cone_exact.tsv', encoding='utf-8').read().splitlines()]
hit = {m: int(a) for a, b, m in rows}
proj = set(hit)
uses = collections.defaultdict(set)
for l in open(S + '/module_uses.tsv', encoding='utf-8').read().splitlines():
    a, b = l.split('\t'); uses[a].add(b)
imps = {}
for m in proj:
    p = path(m)
    imps[m] = re.findall(r'^import\s+(\S+)', open(p, encoding='utf-8').read(), re.M) if p else []
pimps = {m: [i for i in imps[m] if i in proj] for m in proj}
def closure(start, g):
    seen = set(); st = list(start)
    while st:
        x = st.pop()
        if x in seen: continue
        seen.add(x); st.extend(g.get(x, []))
    return seen
root = sys.argv[1] if len(sys.argv) > 1 else 'DiophantineConsistency.PRACurrentConsistencyEndpoint'
g = {m: list(v) for m, v in pimps.items()}
before = closure([root], g)
zero = {m for m in proj if hit[m] == 0}
import fnmatch
ALLOW = os.environ.get("ALLOW", "*").split(",")
def allowed(a): return any(fnmatch.fnmatch(a, p) for p in ALLOW)
added = collections.defaultdict(set); removed = collections.defaultdict(set)
changed = True
while changed:
    changed = False
    cl = closure([root], g)
    for a in sorted(cl):
        for z in list(g[a]):
            if z in zero and z not in uses[a] and allowed(a):
                rest = [i for i in g[a] if i != z]
                cov = closure(rest, g)
                need = {u for u in uses[a] if u not in cov}
                # cover each lost need by importing it directly
                g[a] = rest + sorted(need)
                removed[a].add(z); added[a] |= need
                changed = True
after = closure([root], g)
print('endpoint closure', len(before), '->', len(after), '; zero modules left', len(after & zero))
lines = lambda m: open(path(m), encoding='utf-8').read().count('\n') if path(m) else 0
print('lines', sum(map(lines, before)), '->', sum(map(lines, after)))
edits = {a: {'remove': sorted(removed[a]), 'add': sorted(added[a] - removed[a])} for a in removed}
json.dump(edits, open(S + '/cut_plan.json', 'w'), indent=1)
print(len(edits), 'modules edited')
for a, e in sorted(edits.items()): print(a, 'REMOVE', e['remove'], 'ADD', e['add'])
print('remaining zero:', sorted(after & zero))
