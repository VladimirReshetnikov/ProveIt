import json
from pathlib import Path
src=Path(__file__).resolve().parents[1] / 'binary-radius6-conservation-certificate.json'
r=json.loads(src.read_text());f=r['rule_bits_indexed_by_window'];P=r['potential_by_vertex']
replacements={(0,1):(1,2),(0,2):(-1,1),(0,1,3):(-1,1,4),(0,2,4):(0,3,4)}
def step(c):
 groups=[]
 for x in sorted(c):
  if not groups or x-groups[-1][-1]>2: groups.append([x])
  else: groups[-1].append(x)
 out=set()
 for group in groups:
  a=group[0]; shape=tuple(x-a for x in group); new={a+x for x in replacements.get(shape,shape)}
  assert not out&new;out.update(new)
 assert len(out)==len(c)
 return out
for w in range(8192):
 c={i-6 for i in range(13) if w>>i&1}; actual=int(0 in step(c));assert actual==int(f[w]);assert actual-((w>>6)&1)==P[w>>1]-P[w&4095]
steps=hits=0
for d in range(7,47):
 c={0,3,4,d};end=20*20+(2*d-11)*20
 expected={k*k+(2*d-11)*k:k for k in range(21)}
 for t in range(end+1):
  hit=c&set(range(5))=={0,3,4};assert hit==(t in expected),(d,t,c)
  if hit:assert c=={0,3,4,d+expected[t]};hits+=1
  c=step(c);steps+=1
out={'status':'PASS','local_rules_compared':8192,'potential_identities':8192,'direct_steps':steps,'exact_pattern_hits':hits,'gap_inputs':40,'method':'Independent literal component rewrites and all exported potential identities; no producer imported'}
Path(__file__).with_name('binary-rule-receipt.json').write_text(json.dumps(out,indent=2)+'\n');print(out)
