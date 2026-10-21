"""Source-rotation helpers used by the portable whole_rotations driver.

The historical direct-entry local-window fold search is archival. It also
requires inv_fold.py and sim_fold.py from the repository's candidate-k221/code
directory, supplied through LEGACY_FOLD_CODE; those two modules are not bundled.
The documented whole_rotations.py command does not call that archival path.
"""
from pathlib import Path
from collections import defaultdict,Counter
from functools import lru_cache
import sys,json,time,hashlib,random,os
ROOT=Path(__file__).resolve().parent
PACKET=ROOT.parent
PACKAGED=(PACKET/'vendor/K221_minimal').is_dir()
BASE=Path(os.environ.get('BASELINE221',PACKET/'vendor/K221_minimal' if PACKAGED else ROOT/'K221_Construction_2026-10-20'))
K220=Path(os.environ.get('BASELINE220',ROOT/'K220_Construction_2026-10-20'))
sys.path.insert(0,str(BASE/'portable'))
import source_language as s,build221 as b
def invariant(*args,**kwargs):
 sys.path.insert(0,str(Path(os.environ.get('LEGACY_FOLD_CODE',ROOT.parent/'ProveIt/Computability/BusyBeaver/Research/ZFC/candidate-k221/code'))))
 from inv_fold import invariant as implementation
 return implementation(*args,**kwargs)

def run(*args,**kwargs):
 sys.path.insert(0,str(Path(os.environ.get('LEGACY_FOLD_CODE',ROOT.parent/'ProveIt/Computability/BusyBeaver/Research/ZFC/candidate-k221/code'))))
 from sim_fold import run as implementation
 return implementation(*args,**kwargs)

T0=b.read_table(Path(os.environ.get('SEARCH_TABLE',PACKET/'inputs/k219.native.tm' if PACKAGED else K220/'machine/k220.native.tm')).read_bytes())
S0=s.tree(json.loads(Path(os.environ.get('SEARCH_SITES',PACKET/'inputs/sites219.json' if PACKAGED else K220/'machine/sites220.json')).read_text()))
CFG0,NCHECKS=s.graph_arithmetic(s.sites(S0))
W0=[r[1:] for r in s.sites(S0)]

def sim(T):return {k:(w,'R' if d==1 else 'L',q) for k,(w,d,q) in T.items()}

def folds(T,tree,R=8,ms=9,contextual=False):
 inv=invariant(sim(T),0,R)
 if contextual:
  gg,pp=b.decoder_map(T,tree)
  for q,ps in pp.items():
   knew={i:next(iter(x)) for i in range(-R,0) if len(x:={int(('1'+p)[i]) for p in ps if len(p)>=-i-1})==1 and all(len(p)>=-i-1 for p in ps)}
   inv[q]=knew
 S=sorted({q for q,_ in T}); hits=[]; ST=sim(T)
 for K,D in __import__('itertools').combinations(S,2):
  if K not in inv or D not in inv:continue
  if not any(o in inv[D] and inv[D][o]!=v for o,v in inv[K].items()):continue
  phi=lambda q:K if q==D else q
  same=[r for r in (0,1) if ST[K,r][:2]==ST[D,r][:2] and phi(ST[K,r][2])==phi(ST[D,r][2])]
  if len(same)!=1:continue
  r=1-same[0]
  M={k:(w,d,phi(z)) for k,(w,d,z) in ST.items() if k[0]!=D}
  goals={}
  for X in (K,D):
   if 0 in inv[X] and inv[X][0]!=r:continue
   w,d,z=ST[X,r];tape=dict(inv[X]);tape[0]=r;after=dict(tape);after[0]=w
   goals[X]=(tape,(phi(z),1 if d=='R' else -1,after))
  for m in ('L','R'):
   found=None
   for h in S:
    if h==D:continue
    M[K,r]=(r,m,h)
    if all(run(M,K,tape,0,ms,goal)!=None for tape,goal in goals.values()):
     found=(r,m,h);break
   if found:
    MM={(q,c):(w,1 if d=='R' else -1,z) for (q,c),(w,d,z) in M.items()}
    hits.append((K,D,r,found,MM));break
 return hits

def rotations(T,tree,maxzr=6):
 try:gg,pp=b.decoder_map(T,tree)
 except ValueError:return
 ns={n:q for q,vs in gg.items() for n in vs}
 parents=defaultdict(set)
 for n in ns:
  for ch in n:parents[ch].add(n)
 @lru_cache(None)
 def replace(n,X,Y):
  if n==X:return Y
  if s.leaf(n):return n
  return replace(n[0],X,Y),replace(n[1],X,Y)
 for X,q in ns.items():
  if len(gg[q])!=1:continue
  for direction in ('L','R'):
   Y=X[1 if direction=='L' else 0]
   if s.leaf(Y) or parents[Y]!={X}:continue
   r=ns[Y]
   if len(gg[r])!=1 or r==q:continue
   if direction=='L':A,(B,C)=X
   else:(A,B),C=X
   # Enough conditions for source sequencing associativity; verify graph later.
   if s.boundary(A)[0] or s.boundary(C)[1]:continue
   if any(s.leaf(z) for z in (A,B,C)):continue
   Z=(A,B) if direction=='L' else (B,C)
   if Z in ns:continue
   XX=(Z,C) if direction=='L' else (A,Z)
   tree2=replace(tree,X,XX)
   if s.metrics(tree2)['maximum_zero_run']>maxzr:continue
   M=dict(T)
   if direction=='L':
    M[q,0]=(0,1,r);M[q,1]=(1,1,ns[C]);M[r,0]=(0,1,ns[A]);M[r,1]=(1,1,ns[B])
   else:
    M[q,0]=(0,1,ns[A]);M[q,1]=(1,1,r);M[r,0]=(0,1,ns[B]);M[r,1]=(1,1,ns[C])
   expected={replace(n,X,XX):z for n,z in ns.items() if n !=Y};expected[Z]=r
   try:
    g2,p2=b.decoder_map(M,tree2)
    if {n:z for z,vs in g2.items() for n in vs}!=expected:continue
   except ValueError:continue
   yield [direction,q,r,pp[q]],M,tree2

def search(depth=3, contextual=False):
 out=ROOT/(os.environ.get('SEARCH_OUT','rotsearch_context' if contextual else 'rotsearch_global'));out.mkdir(exist_ok=True)
 started=time.time();seen=set();nhit=0;nseen=0
 def visit(T,tree,chain,laststates=set()):
  nonlocal nhit,nseen
  key=(b.table_bytes(T),s.compact(s.sites(tree)))
  if key in seen:return
  seen.add(key);nseen+=1
  for K,D,r,action,M in folds(T,tree,contextual=contextual):
   nhit+=1;name='hit%05d'%nhit
   sr=s.sites(tree)
   graph,nchecks=s.graph_arithmetic(sr)
   if graph!=CFG0 or s.graph_intervals(sr)!=CFG0:print('BAD GRAPH',chain,flush=True);continue
   (out/(name+'.tm')).write_bytes(b.table_bytes(M));(out/(name+'.prefold.tm')).write_bytes(b.table_bytes(T));(out/(name+'.sites.json')).write_bytes(s.compact(sr));(out/(name+'.json')).write_text(json.dumps(dict(chain=chain,fold=[K,D,r,action],cases=nchecks,contextual=contextual),indent=2))
   print('HIT',name,chain,K,D,r,action,flush=True)
  if nseen%10==0:print('VISIT',nseen,'hits',nhit,'seconds',round(time.time()-started,1),'chain',[(x[0],x[1],x[2],len(x[3])) for x in chain],flush=True)
  if len(chain)>=depth:return
  for tag,M,tr in rotations(T,tree):
   states={tag[1],tag[2]}
   if len(chain)>=2 and not states&laststates:continue
   visit(M,tr,chain+[tag],states)
 visit(T0,S0,[])
 print('DONE',nseen,'hits',nhit,'seconds',time.time()-started,flush=True)
 (out/'summary.json').write_text(json.dumps(dict(tables=nseen,hits=nhit,seconds=time.time()-started)))

if __name__=='__main__':
 legacy=Path(os.environ.get('LEGACY_FOLD_CODE',ROOT.parent/'ProveIt/Computability/BusyBeaver/Research/ZFC/candidate-k221/code'))
 if not all((legacy/name).is_file() for name in ('inv_fold.py','sim_fold.py')):
  raise SystemExit('Archival direct-entry search: set LEGACY_FOLD_CODE to the ProveIt candidate-k221/code directory containing inv_fold.py and sim_fold.py. For the standalone bundled search, use whole_rotations.py as documented in README.md.')
 search(int(sys.argv[1]) if len(sys.argv)>1 else 3,'--contextual' in sys.argv)
