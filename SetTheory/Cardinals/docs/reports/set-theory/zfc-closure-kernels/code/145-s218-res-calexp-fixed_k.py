import os,sys,json,itertools
from pathlib import Path
from functools import cache
ROOT=Path(__file__).resolve().parent
os.environ['K220_BASE']=str(ROOT/'K220_Construction_2026-10-20');os.environ['K221_BASE']=str(ROOT/'K221_Construction_2026-10-20')
sys.path.insert(0,str(ROOT/'K219_Construction_2026-10-20/research/experiments'))
import orientation_postfix as o
from h_fusion import splice
z=o.z;INC=('CI',1)
I,R,Q,N=o.I,o.R,o.Q,o.N
p,y,C,c='p','y','C','c'
r=R(y,C);sub=Q(C,I(R(C,p),R(C,y)))
w=Q(y,I(c,N(Q(y,I(c,N(r))))))
u=Q(p,I(sub,w));h=Q(y,I(r,N(Q(p,I(c,N(u))))))
NEW=N(I(o.v,Q(C,I(h,N(w)))))
OLDWORD=o.postfix(o.BUNDLE,set());NEWWORD=o.postfix(NEW,set())
assert len(OLDWORD)==len(NEWWORD)
PUSH0=o.M[1][0]

@cache
def plus(n,shape):
 if n==0:return None
 if n==1:return INC
 if shape=='left':return(plus(n-1,shape),INC)
 if shape=='balanced':return(plus(n//2,shape),plus(n-n//2,shape))
 return(INC,plus(n-1,shape))

def pushconst(n,shape):
 return PUSH0 if n==0 else(PUSH0,plus(n,shape))

def make(a,b,offset,shape,policy):
 mapping={**o.M,'p':pushconst(a,shape),'y':pushconst(b,shape),'C':o.M['c']if offset==0 else(o.M['c'],plus(offset,shape))}
 if policy=='whole':return splice(z.TREE,2650,4563,z.serial([mapping[m]for m in NEWWORD]))
 i=2650;edits=[]
 for old,new in zip(OLDWORD,NEWWORD):
  j=i+len(z.flat(o.M[old]))
  if old!=new:edits.append((i,j,mapping[new]))
  i=j
 assert i==4563
 t=z.TREE
 for a,b,repl in reversed(edits):t=splice(t,a,b,repl)
 return t

if __name__=='__main__':
 out=ROOT/'fixed_k_results';out.mkdir(exist_ok=True);results=[]
 for a,b,offset in [(0,1,2),(1,0,2),(0,2,3),(2,0,3),(1,2,3),(2,1,3),(1,8,0),(8,1,0),(1,17,0),(17,1,0)]:
  for shape,policy in itertools.product(['right','left','balanced'],['each','whole']):
   name=f'p{a}_y{b}_offset{offset}_{shape}_{policy}'
   t=make(a,b,offset,shape,policy);r={'name':name,'public_binders':[a,b],'offset':offset,'shape':shape,'policy':policy,'metrics':z.s.metrics(t)}
   rows=z.s.sites(t);assert z.s.graph_arithmetic(rows)[0]==z.s.graph_intervals(rows)
   try:
    tab,met=z.compile_tree(z.T,z.TREE,t);r['compiler']=met
    if met['working_states']<=225:
     d=out/name;d.mkdir(exist_ok=True);(d/'sites.json').write_bytes(z.s.compact(rows));(d/'candidate.tm').write_bytes(z.b.table_bytes(tab))
   except Exception as e:r['error']=repr(e)
   results.append(r);print(json.dumps(r),flush=True)
 (out/'summary.json').write_text(json.dumps(results,indent=2)+'\n')
