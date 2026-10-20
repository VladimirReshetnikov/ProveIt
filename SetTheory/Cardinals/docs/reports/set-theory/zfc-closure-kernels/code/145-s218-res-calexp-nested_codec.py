import os,sys,json,collections,itertools
from pathlib import Path
ROOT=Path(__file__).resolve().parent
os.environ['K220_BASE']=str(ROOT/'K220_Construction_2026-10-20')
os.environ['K221_BASE']=str(ROOT/'K221_Construction_2026-10-20')
sys.path.insert(0,str(ROOT/'K219_Construction_2026-10-20/research/experiments'))
import additive_binder as z
import tag_permutations as tp
POP=tp.CORE[0];PAIR=tp.CORE[1][0]
TRANSFER=(('CD',7),(('CI',1),('CC',2)))
assert z.s.boundary(TRANSFER)==(0,0,False)

def seq(xs,shape=0):
 if len(xs)==1:return xs[0]
 if shape==0:return (xs[0],seq(xs[1:],shape))
 if shape==1:return (seq(xs[:-1],shape),xs[-1])
 split=len(xs)//2;return (seq(xs[:split],shape),seq(xs[split:],shape))

def constructor(t,shape):
 return seq([POP,PAIR,TRANSFER]+[('CI',6)]*t+[PAIR,TRANSFER],shape)

def source(perm,shape):
 repl={};deletes=set()
 for lo,ce,hi,t in tp.HITS:
  repl[lo,ce]=constructor(perm[t],shape);deletes.update(range(ce,hi))
 consumed=set()
 def edit(tree,i=0):
  j=i+len(z.flat(tree))
  if (i,j)in repl:consumed.add((i,j));return repl[i,j]
  if z.s.leaf(tree):return None if i in deletes else tree
  a=edit(tree[0],i);b=edit(tree[1],i+len(z.flat(tree[0])))
  return a if b is None else b if a is None else(a,b)
 tree=edit(z.TREE)
 assert consumed==set(repl)
 return tree

if __name__=='__main__':
 out=ROOT/'nested_codec_results';out.mkdir(exist_ok=True);results=[]
 for permkeys in itertools.permutations([0,2,3]):
  perm=dict(zip([0,2,3],permkeys));perm[1]=1
  for shape in range(3):
   tree=source(perm,shape);r={'tags':perm,'shape':shape,'metrics':z.s.metrics(tree)}
   try:
    tab,m=z.compile_tree(z.T,z.TREE,tree);r['compiler']=m
   except Exception as e:r['error']=repr(e)
   results.append(r);print(json.dumps(r),flush=True)
 (out/'summary.json').write_text(json.dumps(results,indent=2)+'\n')
 p=lambda a,b:(a+b)*(a+b+1)//2+b
 cases=0
 for t in range(4):
  for a,b,old in itertools.product(range(3),repeat=3):
   regs=[17,b,p(a,old),8,6,9,0,0,4];got,n=z.runmacro(constructor(t,0),regs)
   want=regs.copy();want[1]=p(t,p(a,b));want[2]=old
   assert got==want,(t,a,b,old,got,want)
   cases+=1
 print('Macro tests:',cases)
