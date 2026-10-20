"""Own literal source census for the guarded CC2-retagging obstruction."""
from pathlib import Path
import json,hashlib
R=Path('/home/codex/.codex/worktrees/ec20/Proofs')
P=R/'Computability/BusyBeaver/Research/ZFC/candidate-k218/sites218.json'
rows=json.loads(P.read_text());ids={p:i for i,(p,_,_)in enumerate(rows)};spans={}
def span(p):
 if p in ids:v=(ids[p],ids[p]+1)
 else:
  a,b=span(p+'0'),span(p+'1');assert a[1]==b[0];v=(a[0],b[1])
 spans[p]=v;return v
span('')
def edge(i,bit,k):
 p=rows[i][0];anc=[p[:j]for j,b in enumerate(p)if b==bit]
 if len(anc)<k:return 0
 a,b=spans[anc[-k]];return a if bit=='1'else b%len(rows)
found=[]
for p,(a,b)in spans.items():
 if b-a!=2 or p+'0'not in ids or p+'1'not in ids:continue
 if rows[a][1:]!=['CD',6]or rows[a+1][1:]!=['CC',2]:continue
 i=a+1;target=edge(i,'1',2);gap=i-target
 assert edge(a,'0',1)==i+1
 if gap==2:kind='two preceding leaves: right-crossing count at most2'
 else:
  assert gap==3
  assert rows[target][1:]==['CD',5]and rows[target+1][1:]==['CC',1]
  assert edge(target,'0',1)==target+2 and edge(target+1,'1',1)==target
  kind='three preceding leaves, first two forced into the CD5/CC1 block: at most2'
 found.append({'decrement':a,'continue':i,'path':rows[i][0],'target':target,'zero_target':i+1,'ordinal_distance':gap,'obstruction':kind})
found.sort(key=lambda r:r['continue'])
assert [r['continue']for r in found]==[8,4569,4575,4587,4593,4601,4607,4710,4716]
files=[P,Path(__file__),R/'Computability/BusyBeaver/Research/ZFC/k218-continuation-search/marker-relay/evidence/runtime-attempt/literal-counterexample.json',Path('/tmp/zfc-intake187/K219_Alternatives_2026-10-20/K219_Alternatives_2026-10-20/report/report.tex')]
out={'status':'LITERAL_CFG_CENSUS_PASS_WITH_ORDINARY_RETAGGING_OBSTRUCTION','reviewer':'review_upstream_reflection','scope':'Source-only exact ordinal CFG and primitive-order preservation. No search, allocation or runtime replay.','occurrences':found,'ordinary_claim':'None of these nine CC2 sites can become CC3 or higher under an ordered binary-tree reassociation that retains the primitive ordinal positions and exact successors of both decrement guards.','limits':['This does not forbid genuine primitive-word changes or a different all-natural comparison macro.','This does not rule out allocating or repairing a physical CC2 entry.','The Source141 closed-increment retagging theorem remains valid; its premises differ from these guarded loops.'],'inputs':[{'path':str(p),'sha256':hashlib.sha256(p.read_bytes()).hexdigest()}for p in files]}
q=Path(__file__).parent/'review.json';q.write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({'status':out['status'],'occurrences':len(found),'sha256':hashlib.sha256(q.read_bytes()).hexdigest()}))
