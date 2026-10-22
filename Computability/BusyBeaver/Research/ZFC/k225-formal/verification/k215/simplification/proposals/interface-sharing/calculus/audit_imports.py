"""Owned project-import analysis, not compiler verification."""
if not __debug__:raise SystemExit('Disable optimized Python')
import json,copy
from pathlib import Path
B=Path(__file__).resolve().parent;G=json.loads((B/'inputs/DEPENDENCY_GRAPH.json').read_text())
H=copy.deepcopy(G);k='BusyBeaver.ZFC.KLowerQHyp'
H[k]['imports']=['BusyBeaver.ZFC.KQ1Model' if n=='BusyBeaver.ZFC.QuotientModel' else n for n in H[k]['imports']]
def closure(g):
 seen=set();todo=['BusyBeaver.ZFC.KEndpoint215']
 while todo:
  n=todo.pop()
  if n in seen or n not in g:continue
  seen.add(n);todo.extend(g[n]['imports'])
 return seen
a=closure(G);b=closure(H)
out={'before':len(a),'after':len(b),'removed':sorted(a-b),'added':sorted(b-a),'removed_bytes':sum(G[n]['bytes'] for n in a-b),'scope':'Fetched project import graph only; not compiler verification.'}
(B/'IMPORT_AUDIT.json').write_text(json.dumps(out,indent=2)+'\n');print(out)
