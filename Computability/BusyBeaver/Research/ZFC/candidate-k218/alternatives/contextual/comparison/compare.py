"""Own literal/tree/CFG comparison; imports no submitted module."""
from pathlib import Path
import hashlib,json,collections
ROOT=Path('/home/codex/.codex/worktrees/ec20/Proofs')
PK=Path(__file__).resolve().parents[1]/'K218_Construction_2026-10-20'
R=ROOT/'Computability/BusyBeaver/Research/ZFC'
OUT=Path(__file__).resolve().parent
sha=lambda x:hashlib.sha256(x).hexdigest()
compact=lambda x:(json.dumps(x,separators=(',',':'))+'\n').encode()
def table(p):
 t={}
 for l in p.read_text().splitlines():
  if not l or l.startswith('#'):continue
  q,b,w,d,z=l.split();q,b,w,z=map(int,(q,b,w,z));assert (q,b)not in t and b in(0,1) and w in(0,1) and d in('L','R');t[q,b]=(w,d,z)
 qs={q for q,b in t};assert set(t)=={(q,b)for q in qs for b in(0,1)} and {z for w,d,z in t.values()}-qs=={254}
 return t

def tree(rows):
 d={}
 for p,op,a in rows:
  n=d
  for c in p:assert c in'01' and 'leaf'not in n;n=n.setdefault(c,{})
  assert not n;n['leaf']=(op,a)
 nodes={};intervals={};counter=0
 def build(n,p):
  nonlocal counter
  lo=counter
  if 'leaf'in n:assert len(n)==1;x=n['leaf'];counter+=1
  else:assert set(n)=={'0','1'};x=(build(n['0'],p+'0'),build(n['1'],p+'1'))
  nodes[p]=x;intervals[p]=(lo,counter);return x
 result=build(d,'');assert counter==len(rows) and [p for p in sorted(nodes)if isinstance(nodes[p][0],str)]==[x[0]for x in rows]
 return result,nodes,intervals

def graph(rows,intervals):
 def escape(p,edge,k):
  while p:
   last,p=p[-1],p[:-1]
   if last==edge:
    k-=1
    if k==0:return intervals[p][1 if edge == '0' else 0]%len(rows)
  return 0
 g=[]
 for i,(p,op,a)in enumerate(rows):
  n=(i+1)%len(rows)
  successors={'CI':[n],'CD':[escape(p,'0',1),n],'CB':[escape(p,'0',a or 1)],'CC':[escape(p,'1',a or 1)],'CH':[]}[op]
  g.append([op,a,successors])
 return g

def binding(t,nodes):
 result={};steps=0
 for p,sub in nodes.items():
  if isinstance(sub[0],str):continue
  tape={i:int(b)for i,b in enumerate(p)};saved=dict(tape);q=84;h=0;count=0
  while h!=len(p):
   assert h in tape and count<2000
   w,d,q=t[q,tape[h]];tape[h]=w;h+=1 if d=='R'else-1;count+=1
  assert tape==saved and(q,0)in t
  result[p]=q;steps+=count
 return result,steps

def canonical(t):
 qs={q for q,b in t};order=[0];m={0:0}
 for q in order:
  for b in(0,1):
   z=t[q,b][2]
   if z!=254 and z not in m:m[z]=len(m);order.append(z)
 assert set(m)==qs;m[254]=len(qs)
 return {(m[q],b):(w,d,m[z])for(q,b),(w,d,z)in t.items()}

paths={'K219':(R/'candidate-k219/k219.native.tm',R/'candidate-k219/sites219.json'),'K218':(R/'candidate-k218/k218.native.tm',R/'candidate-k218/sites218.json'),'contextual218':(PK/'machine/k218.native.tm',PK/'machine/sites218.json')}
T={};S={};N={};B={};G={};report={'status':'OWN_LITERAL_SOURCE_CFG_AND_PREFIX_REVIEW_PASS','actual_submitted_execution':False,'inputs':{},'sources':{},'tables':{}}
for name,(tp,sp)in paths.items():
 t=table(tp);rows=json.loads(sp.read_bytes());tr,nodes,intervals=tree(rows);g=graph(rows,intervals);entries,steps=binding(t,nodes)
 T[name]=t;S[name]=rows;N[name]=nodes;B[name]=entries;G[name]=g
 report['inputs'][name]={'table':str(tp),'table_sha256':sha(tp.read_bytes()),'source':str(sp),'source_sha256':sha(sp.read_bytes())}
 report['sources'][name]={'leaves':len(rows),'DAG':len(set(nodes.values())),'depth':max(map(len,nodes)),'guarded_edges':sum(len(x[2])for x in g),'prefixes':len(entries),'prefix_steps':steps,'source_graph_sha256':sha(compact(g))}
 report['tables'][name]={'states':len(t)//2,'rows':len(t),'all_graph_reachable':len(canonical(t))==len(t)}
assert G['K219']==G['K218']==G['contextual218'];assert len(S['K219'])==4744
report['source_comparison']={'same_4744_primitive_word':True,'same_6166_guarded_successors':True,'different_main_vs_alt_addresses':sum(x[0]!=y[0]for x,y in zip(S['K218'],S['contextual218'])),'first37_same_as_K219':{n:S[n][:37]==S['K219'][:37]for n in S},'DAG_intersection':len(set(N['K218'].values())&set(N['contextual218'].values()))}
for name in ['K218','contextual218']:
 base=T['K219'];t=T[name];report['tables'][name].update({'added':sorted({q for q,b in t}-{q for q,b in base}),'removed':sorted({q for q,b in base}-{q for q,b in t}),'changes':[{'row':k,'old':base[k],'new':v}for k,v in sorted(t.items())if k in base and base[k]!=v]})
report['different_common_rows']=[{'row':k,'main':T['K218'][k],'alternative':T['contextual218'][k]}for k in sorted(T['K218'].keys()&T['contextual218'].keys())if T['K218'][k]!=T['contextual218'][k]]
report['not_label_isomorphic']=canonical(T['K218'])!=canonical(T['contextual218']);assert report['not_label_isomorphic']
roles={}
for name in ['K218','contextual218']:
 roles[name]={}
 for q in[79,85,96,188,190,212,221]:
  xs=[p for p,z in B[name].items()if z==q];types=collections.Counter(sha(compact(N[name][p]))for p in xs)
  roles[name][str(q)]={'rows':[T[name].get((q,b))for b in(0,1)],'prefixes':xs,'subtree_types':dict(types)}
report['roles']=roles
assert roles['K218']['85']['subtree_types']==roles['contextual218']['85']['subtree_types']
report['same_folded85_roles_and_multiplicities']=True
# Exact two-cell positive detours, arbitrary outside cells untouched.
for name,helper in [('K218',190),('contextual218',221)]:
 t=T[name]
 for bit,end,expected in [(0,12,3),(1,150,5)]:
  tape={-1:bit,0:1};original=dict(tape);q=85;h=0
  for _ in range(expected):
   assert h in tape;w,d,q=t[q,tape[h]];tape[h]=w;h+=1 if d=='R'else-1
  assert q==end and h==1 and tape==original
report['same_two_cell_fold_routes']={'zero_marker':{'steps':3,'child':12},'one_marker':{'steps':5,'child':150},'outside_untouched':True}
report['row157']={'same_157_read1_action':T['K218'][157,1]==T['contextual218'][157,1]==(1,'L',148),'scope':'Needs a fresh contextual certificate; no transfer from isolated row equality.'}
(OUT/'comparison.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({k:v for k,v in report.items()if k not in('inputs','roles','different_common_rows','tables')},indent=2));print('common differing rows',len(report['different_common_rows']))
