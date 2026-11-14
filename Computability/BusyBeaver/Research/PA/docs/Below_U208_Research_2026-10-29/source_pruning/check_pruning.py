import json,sys,hashlib
from pathlib import Path
sys.path.insert(0,str(Path(__file__).parent));import source_language as L
b=Path(__file__).resolve().parent;raw=(b/'inputs/sites.json').read_bytes();rows=json.loads(raw);root=L.tree(rows);g,_=L.graph_arithmetic(rows)
def at(n,p):
 for c in p:n=n[int(c)]
 return n
out={'source_sha256':hashlib.sha256(raw).hexdigest(),'baseline':L.metrics(root),'cases':[]}
for name,ranges,patches in [('first',[(3847,3850)],[('001101110',at(root,'0011011101'))]),('second',[(3891,3893)],[('1110011',at(root,'11100111'))]),('both',[(3847,3850),(3891,3893)],[('001101110',at(root,'0011011101')),('1110011',at(root,'11100111'))])]:
 t=root
 for p,n in patches:t=L.replace(t,p,n)
 rr=L.sites(t);gg,_=L.graph_arithmetic(rr);ii=L.graph_intervals(rr);L.require(gg==ii,'CFG resolvers disagree')
 deleted={i for lo,hi in ranges for i in range(lo,hi)};ret=[i for i in range(len(rows))if i not in deleted];mp={old:new for new,old in enumerate(ret)}
 def move(i):
  for lo,hi in ranges:
   if lo<=i<hi:return hi
  return i
 mismatches=[]
 for new,old in enumerate(ret):
  if gg[new]!=[g[old][0],[mp[move(j)]for j in g[old][1]]]:mismatches.append([old,new,g[old],gg[new]])
 incoming={str(i):[[j,branch]for j,(_,ts)in enumerate(g)for branch,k in enumerate(ts)if k==i and j not in deleted]for i in deleted}
 out['cases'].append({'name':name,'ranges':ranges,'metrics':L.metrics(t),'retained_cfg_mismatches':mismatches,'external_entries_to_deleted':incoming,'note':'Conditional semantic bypass needs established zero guards at loop entries; this audit alone is not a binary-machine proof.'})
expected=json.loads((b/'expected.json').read_text()); L.require(json.loads(json.dumps(out))==expected,'Pruning receipt mismatch'); print('PASS: three closed-factor source bypasses; no state-count improvement claimed')
