from pathlib import Path
from functools import cache
import sys,json,os,itertools
ROOT=Path(__file__).resolve().parents[1]
BASE=ROOT/'k220_replay/baseline/K221_Construction_2026-10-20'
sys.path.insert(0,str(BASE/'portable'))
import source_language as s, build221 as b
P224=ROOT/'k220_replay/parent_replay/baseline_replay/baseline/K224_Construction_2026-10-20/portable'
sys.path.insert(0,str(P224/'verification'));import construct_rel225 as cr
os.environ['K221_BASE']=str(BASE)
sys.path.insert(0,str(ROOT/'baseline220/K220_Construction_2026-10-20/research/encoding/scripts'))
import recompile
old=s.tree(json.loads((ROOT/'baseline220/K220_Construction_2026-10-20/machine/sites220.json').read_text()))
T=b.read_table((ROOT/'baseline220/K220_Construction_2026-10-20/machine/k220.native.tm').read_bytes())
groups,_=cr.decoder_map(s,cr.read_table(P224/'parent225/candidate225.k.tm'),s.tree(json.loads((P224/'parent225/sites225.json').read_text())))
q=lambda k:cr.sole(groups,k)
R=q(155); I=q(90);E=q(182);Q=q(86)
positions=[]
def visit(n,p,lo):
 if n==R:positions.append((p,lo,lo+len(s.sites(n))))
 if not s.leaf(n):visit(n[0],p+'0',lo);visit(n[1],p+'1',lo+len(s.sites(n[0])))
visit(old,'',0)
print('R positions',positions)
pat=[x for x in positions if x[1:]==(650,730)]
assert len(pat)==1,pat
path=pat[0][0]
ci=('CI',1);stop=('CC',2)
@cache
def shapes(atoms):
 if len(atoms)==1:return (atoms[0],)
 return tuple((x,y)for k in range(1,len(atoms))for x in shapes(atoms[:k])for y in shapes(atoms[k:]))
@cache
def all_nodes(t):
 return frozenset({t}) if s.leaf(t) else frozenset({t})|all_nodes(t[0])|all_nodes(t[1])
orig_word=[x[1:] for x in s.sites(old)]
out=ROOT/'theory_notes/binders';out.mkdir(exist_ok=True)
res=[];best=999
for swap,m,k in itertools.product((False,True),range(1,9),range(0,5)):
 if m==1 and k==0:continue
 if m>4 and k>1:continue
 push=R[0] if not swap else(R[0][1],R[0][0])
 for incs in shapes((ci,)*m):
  loop=(('CD',7),(incs,stop))
  pair=(I[0],(I[1][0],loop))
  atoms=(push,pair)+((ci,)*k)
  for binder in shapes(atoms):
   n=s.replace(old,path,binder)
   if len(all_nodes(n))>211:continue
   mm=s.metrics(n)
   if mm['maximum_zero_run']>7:continue
   name=f'binder_{int(swap)}_{m}_{k}_{len(res)}'
   row={'name':name,'swap':swap,'m':m,'k':k,'metrics':mm}
   try:
    gg,nc=s.graph_arithmetic(s.sites(n));assert gg==s.graph_intervals(s.sites(n))
    nt,cm=recompile.compile_tree(T,old,n);row['compile']=cm
    if cm['working_states']<best:
     best=cm['working_states'];print('BEST',best,row,flush=True)
    if cm['working_states']<=221:
     d=out/name;d.mkdir(exist_ok=True);(d/'candidate.tm').write_bytes(b.table_bytes(nt));(d/'sites.json').write_bytes(s.compact(s.sites(n)))
   except Exception as ex:row['error']=repr(ex)
   res.append(row)
(out/'results.json').write_text(json.dumps(res,indent=2)+'\n')
print('CASES',len(res),'BEST',best)
