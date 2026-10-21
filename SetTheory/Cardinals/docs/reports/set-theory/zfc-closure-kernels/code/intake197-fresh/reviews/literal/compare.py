#!/usr/bin/env python3
"""Independent literal/source comparison only; imports no submitted modules."""
from pathlib import Path
import hashlib,json,zipfile,io,collections
P=Path('/tmp/zfc-intake197/extracted/K216_Permuted_Commands_2026-10-21')
O=Path('/tmp/zfc-intake195/extracted/K216_Partial_Selector_2026-10-20')
OUT=Path(__file__).parent
sha=lambda x:hashlib.sha256(x).hexdigest()
def table(raw):
 t={}
 for line in raw.decode().splitlines():
  if not line.strip() or line.startswith('#'):continue
  q,b,w,d,z=line.split(); q,b,w,z=map(int,(q,b,w,z))
  assert (q,b) not in t and b in (0,1) and w in (0,1) and d in ('L','R')
  t[q,b]=(w,d,z)
 s={q for q,b in t};assert len(t)==2*len(s) and all((q,b) in t for q in s for b in (0,1))
 assert {z for w,d,z in t.values()}-s=={254}
 return t

def source(raw):
 rows=json.loads(raw);d={}
 for path,op,k in rows:
  assert path not in d and set(path)<=set('01')
  assert op in ('CI','CD','CB','CC','CH')
  d[path]=(op,k)
 def tr(p):
  if p in d:return d[p]
  return (tr(p+'0'),tr(p+'1'))
 t=tr('')
 return rows,t
leaf=lambda t:isinstance(t[0],str)
def leaves(t,p=''):
 if leaf(t):return [(p,*t)]
 return leaves(t[0],p+'0')+leaves(t[1],p+'1')
def width(t):return 1 if leaf(t) else width(t[0])+width(t[1])
def stats(t):
 seen=set()
 def visit(s):
  seen.add(s)
  if not leaf(s):visit(s[0]);visit(s[1])
 visit(t);r=leaves(t)
 return dict(dag=len(seen),leaves=len(r),guards=sum(1+(op=='CD') for _,op,_ in r),depth=max(len(p) for p,_,_ in r),zero=max(len(x) for p,_,_ in r for x in p.split('1')))
def tree_at(t,path):
 for b in path:t=t[int(b)]
 return t
def boundary(t):
 if leaf(t):
  op,k=t
  return (1,0) if op=='CD' else (k,0) if op=='CB' else (0,k) if op=='CC' else (0,0)
 l,r=boundary(t[0]),boundary(t[1]);return(max(l[0]-1,r[0],0),max(l[1],r[1]-1,0))
def cfg(t):
 out=[];n=width(t)
 def rec(q,start,bs,cs):
  if leaf(q):
   op,k=q;nxt=(start+1)%n
   def get(st,k):return st[k-1] if 0<k<=len(st) else 0
   dest=(nxt,) if op=='CI' else (get(bs,1),nxt) if op=='CD' else (get(bs,k),) if op=='CB' else (get(cs,k),) if op=='CC' else ()
   out.append((op,k if op not in ('CB','CC') else None,dest));return
  cut=start+width(q[0]);end=(start+width(q))%n
  rec(q[0],start,(end,)+bs,cs);rec(q[1],cut,bs,(start,)+cs)
 rec(t,0,(),());return out

def isom(t,u):
 # Every working state is graph-reachable.  A start-preserving isomorphism
 # of deterministic labelled transitions is forced by the two outgoing rows.
 f={0:0,254:254};g={0:0,254:254};queue=collections.deque([(0,0,'')]);done=set()
 while queue:
  q,r,path=queue.popleft()
  if (q,r) in done:continue
  done.add((q,r))
  for b in (0,1):
   x,y=t[q,b],u[r,b]
   if x[:2]!=y[:2]:return {'isomorphic':False,'witness_path':path+str(b),'left_state':q,'right_state':r,'left':x,'right':y,'reason':'write/move mismatch'}
   a,c=x[2],y[2]
   if (a in f and f[a]!=c) or (c in g and g[c]!=a):return {'isomorphic':False,'witness_path':path+str(b),'left':x,'right':y,'reason':'forced state-map conflict','existing_left_mapping':f.get(a),'existing_right_inverse':g.get(c)}
   f[a]=c;g[c]=a
   if a!=254:queue.append((a,c,path+str(b)))
 return {'isomorphic':True,'states':len(f)-1,'mapping':f}

def diff(t,u):
 return {'changed_common':sum(t[k]!=u[k] for k in t.keys()&u.keys()),'removed_states':sorted({q for q,b in t}-{q for q,b in u}),'added_states':sorted({q for q,b in u}-{q for q,b in t})}
def providers(t):
 ss=sorted({q for q,b in t});left=[q for q in ss if t[q,0]==(0,'R',150)];right=[q for q in ss if t[q,0]==(0,'R',77)]
 sels=[q for q in ss if t[q,0][0:2]==(0,'R') and t[q,0][2] in left and t[q,1][0:2]==(1,'R') and t[q,1][2] in right]
 return {'left_providers_zero_to150':left,'right_providers_zero_to77':right,'exact_existing_one_step_selector_states':sels}
oldraw=(P/'parent/K217_Dominated_Continuation_2026-10-20.zip').read_bytes()
z=zipfile.ZipFile(io.BytesIO(oldraw));pref='K217_Dominated_Continuation_2026-10-20/'
base=table(z.read(pref+'machine/k217.native.tm'))
oldsrcraw=z.read(pref+'machine/sites217.json')
T={'primary195':table((O/'machine/k216.native.tm').read_bytes()),'210':table((P/'machine/k216.native.tm').read_bytes()),'120':table((P/'secondary/k216-120.native.tm').read_bytes())}
S={}
for name,path in [('primary195',O/'source/sites216.json'),('reference205',P/'source/reference205.json'),('frozen202',P/'source/frozen202.json'),('210',P/'machine/sites216.json'),('120',P/'secondary/sites120.json')]:
 raw=path.read_bytes();rr,t=source(raw);assert [list(r) for r in leaves(t)]==rr;S[name]=(rr,t)
# Literal exact closed command permutations and outside preservation.
paths=('111','110101','110100101');base_tree=S['frozen202'][1];bodies=[tree_at(base_tree,p) for p in paths]
assert [width(t) for t in bodies]==[106,26,26] and all(boundary(t)==(0,0) for t in bodies)
for name,order in [('210',(2,1,0)),('120',(1,2,0))]:
 def swap(t,p=''):
  if p in paths:return bodies[order[paths.index(p)]]
  return t if leaf(t) else (swap(t[0],p+'0'),swap(t[1],p+'1'))
 assert swap(base_tree)==S[name][1]
assert cfg(S['reference205'][1])==cfg(base_tree)
assert [r[1:] for r in S['reference205'][0]]==[r[1:] for r in S['frozen202'][0]]
# Authenticate actual changed-row recipes, not merely the reported counts.
recipes={}
for name in ('210','120'):
 rec=json.loads((P/f'provenance/transition_recipe{name}.json').read_text());c=base.copy()
 for row in rec['rows']:
  key=(row['state'],row['read']);old=None if row['old'] is None else tuple(row['old']);new=None if row['new'] is None else tuple(row['new'])
  assert c.get(key)==old
  if new is None:del c[key]
  else:c[key]=new
 assert c==T[name]
 assert diff(base,c)['changed_common']==38
 recipes[name]=diff(base,c)
# Primary195 marker fold's literal assumptions versus new layouts.
key_states=[81,92,100,111,134,143,163,164,183,195,196,201,205]
rows={name:{str(q):[t.get((q,b)) for b in (0,1)] for q in key_states} for name,t in T.items()}
incoming={name:[[q,b,*v] for (q,b),v in t.items() if v[2] in (164,183)] for name,t in T.items()}
# Parent numerical runtime infrastructure is byte-identical to accepted195 copies.
nested=z.read(pref+'parent/K218_Dominated_Rho8_2026-10-20.zip');nz=zipfile.ZipFile(io.BytesIO(nested));np='K218_Dominated_Rho8_2026-10-20/'
closure={}
for rel in ('validate_native.py','runtime/symbolic_runtime.py','runtime/independent_runtime.py','inputs/legacy_mapping.json'):
 raw=nz.read(np+'binary/code/'+rel);old=(O/'code'/rel).read_bytes();assert raw==old
 closure[rel]={'sha256':sha(raw),'equal_to_accepted195_copy':True}
helper=z.read(pref+'code/vendor/source_language.py')
res={'status':'PASS_OWN_LITERAL_SOURCE_COMPARISON','scope':'No submitted Python/C++ or machine proof/runtime execution; own parsers compare literal rows, source trees, recipes and imported bytes. No manifest suite.',
'parent_archive_sha256':sha(oldraw),'nested149_sha256':sha(nested),'parent_source_sha256':sha(oldsrcraw),'runtime_closure':closure,'source_language_sha256':sha(helper),
'sources':{n:stats(v[1]) for n,v in S.items()},'reference_frozen_same_word_cfg':True,'literal_closed_permutations_checked':['210','120'],
'recipes_vs_parent217':recipes,'new_vs_primary195':{n:diff(T['primary195'],T[n]) for n in ('210','120')},
'forced_start_preserving_isomorphism':{'195_vs210':isom(T['primary195'],T['210']),'195_vs120':isom(T['primary195'],T['120']),'210_vs120':isom(T['210'],T['120'])},
'partial_fold_literal_rows':rows,'partial_fold_incoming':incoming,'partial_fold_provider_census':{n:providers(t) for n,t in T.items()},
'word_equal_primary195':{n:[r[1:] for r in S['primary195'][0]]==[r[1:] for r in S[n][0]] for n in ('frozen202','210','120')},
'files':{str(p):sha(p.read_bytes()) for p in [P/'code/audit_command_permutation.py',P/'code/build_sources.py',P/'code/reconstruct.py',P/'machine/k216.native.tm',P/'secondary/k216-120.native.tm',O/'machine/k216.native.tm',Path(__file__)]}}
(OUT/'comparison.json').write_text(json.dumps(res,indent=2)+'\n')
print(json.dumps({k:v for k,v in res.items() if k not in ('files','partial_fold_literal_rows')},indent=2))
