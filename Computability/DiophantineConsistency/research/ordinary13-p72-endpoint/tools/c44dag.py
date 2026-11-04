"""Import DAG utilities for Compact44.

  closure  M...      transitive Compact44 imports of the given modules
  rdeps    M...      transitive Compact44 dependents of the given modules (topological order)
"""
import os, re, sys
D = r'C:\ProveIt\Computability\DiophantineConsistency\Lean\DiophantineConsistency\Compact44'
imp = re.compile(r'^import DiophantineConsistency\.Compact44\.(\w+)', re.M)
deps = {}
for f in os.listdir(D):
    if f.endswith('.lean'):
        deps[f[:-5]] = set(imp.findall(open(os.path.join(D, f), encoding='utf-8').read()))
def closure(ms):
    seen, st = set(), list(ms)
    while st:
        x = st.pop()
        for y in deps.get(x, ()):
            if y not in seen:
                seen.add(y); st.append(y)
    return seen
order, mark = [], set()
def topo(x):
    if x in mark: return
    mark.add(x)
    for y in sorted(deps.get(x, ())): topo(y)
    order.append(x)
for m in sorted(deps): topo(m)
cmd, ms = sys.argv[1], sys.argv[2:]
if cmd == 'closure':
    print(' '.join(sorted(closure(ms))))
elif cmd == 'rdeps':
    tgt = set(ms)
    out = [m for m in order if m in tgt or (closure([m]) & tgt)]
    print('\n'.join(out))
