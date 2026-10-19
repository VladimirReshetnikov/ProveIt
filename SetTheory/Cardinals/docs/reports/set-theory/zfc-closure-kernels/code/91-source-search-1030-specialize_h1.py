from pathlib import Path
import json,sys,time
BASE=Path(__file__).resolve().parent/'base/zfc245-proof-20261018'
sys.path[:0]=[str(BASE/'code'),str(BASE/'reference/context246/code')]
import rebuild_machines as rebuild
import parametric_prefix_affine as affine
import review_affine_source as paths
T,start=rebuild.read_table(BASE/'machine/zfc245_old.tm')
T[46,0]=0,'R',62;T[46,1]=1,'R',78;T[62,0]=0,'R',53;T[62,1]=1,'R',77;T[77,0]=0,'R',103
G=json.loads((BASE/'inputs/closed-sequence-grammar-next22.json').read_text());sites=json.loads((BASE/'certificate/sites_physical.json').read_text())
prefix='1110100101'
# AST190 is the known last phase of the general equality routine:
# if H>0 decrement H, clear H, and bypass the following halt.
def expand(j,p=''):
 row=G['ast_dag'][j]
 if row[0]=='N':return expand(row[1],p+'0')+expand(row[2],p+'1')
 op,arg=(row[1]+[None])[:2];kind={'inc':'CI','dec':'CD','cont':'CC','brk':'CB','halt':'CH'}[op]
 return [[p,kind,rebuild.PHYSICAL[arg]if kind in('CI','CD')else arg]]
newsites=[v for v in sites if not v[0].startswith(prefix)]
newsites+= [[prefix+'00','CD',rebuild.PHYSICAL[5]]]+expand(190,prefix+'010')+[[prefix+'011','CH',None]]+expand(210,prefix+'1')
newsites.sort()
Path('h1-specialized245_old.tm').write_text(rebuild.encode(T,95))
Path('h1-specialized-sites.json').write_text(json.dumps(newsites))
T={(str(q),b):(w,d,str(t))for(q,b),(w,d,t)in T.items()};affine.PADDING=64;cases=0
for p,op,r in newsites:
 for zero in((True,False)if op=='CD'else(None,)):
  branch=(r,zero)if op=='CD'else None;extra=0;effect=None;overflow=False
  if op=='CI':s,overflow=paths.full_inc(p);effect='inc',r
  elif op=='CD'and not zero:s,overflow=paths.full_inc(p);effect='dec',r;extra=1
  elif op=='CD':s,overflow=paths.full_inc(paths.full_strip(p,'0',1))
  elif op=='CB':s,overflow=paths.full_inc(paths.full_strip(p,'0',r))
  elif op=='CC':s=paths.full_strip(p,'1',r)
  else:s=''
  right=[('b',int(b))for b in s]+[('r',0,1,64+extra+int(overflow)-len(s)),('b',1),('box',('plain',effect))]
  try:affine.run(T,p,branch,affine.canon([('b',1)],right),halt=op=='CH',fuel=1000)
  except Exception as e:
   print('FAIL',p,op,r,zero,repr(e));raise
  cases+=1
print('ALL CASES PASS',cases)
