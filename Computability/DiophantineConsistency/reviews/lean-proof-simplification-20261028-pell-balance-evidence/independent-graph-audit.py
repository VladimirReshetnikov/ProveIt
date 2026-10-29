from pathlib import Path
import re,collections
p=Path('/tmp/pell-balance-commit-graph/Computability/DiophantineConsistency/Lean/DiophantineConsistency');rev=collections.defaultdict(set)
for f in p.rglob('*.lean'):
 module='DiophantineConsistency.'+'.'.join(f.relative_to(p).with_suffix('').parts)
 for dep in re.findall(r'^import\s+([^\s]+)',f.read_text(),re.M):rev[dep].add(module)
root='DiophantineConsistency.ArithmeticPellRecurrence';seen=set();todo=list(rev[root]);direct=set(todo)
while todo:
 n=todo.pop()
 if n in seen:continue
 seen.add(n);todo.extend(rev[n]-seen)
assert len(direct)==3 and len(seen)==51
print('3 direct and 51 transitive including direct, within commit snapshot DiophantineConsistency sources');print('direct',sorted(direct))
