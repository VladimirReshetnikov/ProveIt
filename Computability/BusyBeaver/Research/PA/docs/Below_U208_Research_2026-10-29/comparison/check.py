from pathlib import Path
import json,hashlib
import source_language as L
P=Path(__file__).resolve().parent
def need(x,m):
 if not x:raise ValueError(m)
def read(p):
 t={}
 for l in p.read_text().splitlines():
  if not l or l.startswith('#'):continue
  q,b,w,d,r=l.split();k=int(q),int(b);need(k not in t,'duplicate');need(b in('0','1') and w in('0','1') and d in('L','R'),'symbols');t[k]=int(w),d,int(r)
 return t
records=json.loads((P/'records.json').read_text());tables={r['id']:read(P/'inputs'/str(r['id'])/'table.tm') for r in records};words=[];graphs=[]
for r in records:
 d=P/'inputs'/str(r['id']);t=tables[r['id']];states={q for q,b in t};need(len(states)==208 and len(t)==416,'census');need(set(t)=={(q,b)for q in states for b in(0,1)},'totality');need({z for w,d,z in t.values()}-states=={254},'halt');need(hashlib.sha256((d/'table.tm').read_bytes()).hexdigest()==r['sha256'],'table hash');m={int(k):v for k,v in r['mapping'].items()};need(set(m)==states|{254} and len(set(m.values()))==209 and m[0]==0 and m[254]==254,'map bijection');need({(m[q],b):(w,v,m[z])for(q,b),(w,v,z)in t.items()}==tables[r['representative']],'literal conjugacy')
 seen={0};todo=[0]
 for q in todo:
  for b in(0,1):
   z=t[q,b][2]
   if z!=254 and z not in seen:seen.add(z);todo.append(z)
 need(seen==states,'reachability');raw=(d/'sites.json').read_bytes();need(hashlib.sha256(raw).hexdigest()==r['source_sha256'],'source hash');s=json.loads(raw);L.tree(s);g=L.graph_intervals(s);need(g==L.graph_arithmetic(s)[0],'CFG resolvers');words.append([x[1:]for x in s]);graphs.append(g)
need(len(records)==9 and all(w==words[0]for w in words)and all(g==graphs[0]for g in graphs),'common source')
# Distinguish representatives by unique rooted deterministic traversal, not failed heuristic.
def canonical(t):
 m={0:0,254:-1};todo=[0];rows=[]
 for q in todo:
  for b in(0,1):
   w,d,z=t[q,b]
   if z not in m:m[z]=len(todo);todo.append(z)
   rows.append((m[q],b,w,d,m[z]))
 return rows
reps=sorted({r['representative']for r in records});need(len(reps)==2 and canonical(tables[reps[0]])!=canonical(tables[reps[1]]),'two classes')
print(json.dumps({'status':'NINE_U208_TABLES_TWO_GRAPH_CLASSES_PASS','tables':9,'classes':2,'states_each':208,'rows_each':416,'source_primitives':len(words[0]),'ordinal_CFG_edges':sum(len(x[1])for x in graphs[0]),'scope':'Exact graph/source snapshot checks; not a fresh calibration or runtime proof'},indent=2))
