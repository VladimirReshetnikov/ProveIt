import sys
if not __debug__: raise SystemExit("Run without -O: assertions are required for verification.")
from pathlib import Path
import sys,json,math,hashlib
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'independent_review'))
import source_tools as S
P=ROOT/'sites.json'
rows=json.loads(P.read_text());g=S.graph_intervals(rows);assert g==S.graph_arithmetic(rows)[0]
r=[2,0,2,0,0,0,0,0,0];pc=0;roots=[]
for t in range(436):
 if pc==0:roots.append([t,r.copy()])
 if t==435:break
 _,op,k=rows[pc];assert op!='CH'
 if op=='CI':r[k]+=1;branch=0
 elif op=='CD':branch=int(r[k]>0);r[k]-=branch
 else:branch=0
 pc=g[pc][1][branch]
assert pc==0 and r==[5,0,0,0,1,0,0,0,0]
def P(a,b):return(a+b)*(a+b+1)//2+b
def inv(n):
 w=(math.isqrt(8*n+1)-1)//2;b=n-w*(w+1)//2;return w-b,b
assert inv(2)==(0,1)and inv(0)==(0,0)and inv(3)==(2,0)and inv(4)==(1,1)and inv(1)==(1,0)
t,w,d,h=0,2,0,0;commands=[]
# Two NIPs, then DROP, then MP(1). Test-before-pop is essential.
for name in ('NIP','NIP','DROP','MP1'):
 before=[t,w,d,h]
 if name=='NIP':assert h!=1;h,w=inv(w)
 elif name=='DROP':t,w=h,P(t,w)
 else:
  d+=1
  if 4*P(t,d)==h:t,w=d,P(0,w)
  else:t=0
  h=0
 commands.append({'command':name,'before':before,'after':[t,w,d,h]})
assert[t,w,d,h]==[0,0,1,0]
out={'status':'INDEPENDENT_INTERVAL_CFG_AND_DIRECT_COMMAND_DISCHARGE_PASS','source_sha256':hashlib.sha256((ROOT/'sites.json').read_bytes()).hexdigest(),'primitive_steps':435,'roots':roots,'commands':commands,'safe_seed':r,'proof':'Counter is arbitrary in soundness; Start_y=AX(0;1,y) resets counter/cache for cofinal strong refutations. NIP/MP/DROP wire tags0/1/2, AXc+3 unchanged.'}
assert json.loads((Path(__file__).parent/'discharge.json').read_text())==out;print(json.dumps(out,indent=2))
