from pathlib import Path
import sys,json,itertools,hashlib
F=Path(__file__).resolve().parent;O=F.parent/'reproduced';O.mkdir(parents=True,exist_ok=True);sys.path.insert(0,str(F));import complement_quantifier as c
s,m=c.s,c.m
D=lambda r:('CD',r)
I=lambda r:('CI',r)
move=lambda a,b:(D(a),(I(b),('CC',2)))
def assoc(xs):
 if len(xs)==1:return [xs[0]]
 return [(a,b) for k in range(1,len(xs)) for a in assoc(xs[:k]) for b in assoc(xs[k:])]
nip=s.subtree(c.tree,'110100101');eqch=nip[1][0];unpair=nip[1][1][0]
assert s.boundary(eqch)==(0,0,True)
results=[]
for no,body in enumerate(assoc([move(1,5),unpair,move(6,1)])):
 newnip=(nip[0],(eqch,body))
 rr=s.replace(c.tree,'110100101',newnip)
 rr=s.replace(rr,'1101',s.subtree(rr,'1101001'))
 assert s.graph_arithmetic(s.sites(rr))[0]==s.graph_intervals(s.sites(rr))
 for t,ws,h in itertools.product(range(4),repeat=3):
  if h==1:continue
  regs=[3,t,ws,0,5,h,0,0,0];got,_=m.run_macro(s,newnip,regs)
  z=0
  while (z+1)*(z+2)//2<=ws:z+=1
  tail=ws-z*(z+1)//2;head=z-tail;want=regs.copy();want[1]=head;want[2]=tail;want[5]=t
  assert got==want,(no,regs,got,want)
 for omit in [False,True]:
  tt=rr
  if omit:tt=s.replace(tt,'11111',s.subtree(tt,'11111')[1])
  raw=s.compact(s.sites(tt));name=f'merged-n-{no}-{int(omit)}';(O/(name+'.sites.json')).write_bytes(raw)
  rec={'id':name,'association':no,'omit_MP_dummy_zero':omit,'metrics':s.metrics(tt),'source_sha256':hashlib.sha256(raw).hexdigest(),'calibration':'OPEN: source command is sound; proof completeness has not been established'};results.append(rec);print(rec,flush=True)
(O/'merged_n_results.json').write_text(json.dumps(results,indent=2)+'\n')
