#!/usr/bin/env python3
import json,sys,itertools
from pathlib import Path
from explore import T,B
path=Path(sys.argv[1]);obj=json.loads(path.read_text());U=T.copy();U.update({(q,b):(w,1 if d=='R' else-1,t)for q,b,w,d,t in obj['table']});U.pop((255,0));U.pop((255,1))
def check(vals,r,mode,fuel=500):
 word=list(B(vals));word[sum(v+2 for v in vals[:r])+1]='0';one={i for i,b in enumerate(word) if b=='1'};q=73 if mode=='i'else 95;h=0;vs=vals.copy();h0=-1;qt=48;origin=0;boundary=set()
 if mode=='i':vs[r]+=1
 if mode=='z':qt=112
 if mode=='p':vs[r]-=1;h0=0;origin=1;boundary={0}
 for step in range(fuel):
  if q==qt and h==h0:
   want=boundary|{origin+i for i,b in enumerate(B(vs))if b=='1'}
   if mode!='i':return {'pass':one==want,'steps':step,'q':q,'h':h,'ones':sorted(one),'wanted':sorted(want)}
   tail=origin+len(B(vs));ok=all((i in one)==(i in want)for i in range(-3,tail));p=tail
   while any(i>=p for i in one):
    if p in one or p+1 not in one:ok=False;break
    p+=1
    while p in one:p+=1
   return {'pass':ok,'steps':step,'q':q,'h':h,'ones':sorted(one),'expected_prefix':sorted(want),'tail_begin':tail}
  if h<0:return dict(**{'pass':False},reason='crossed_opaque_left',steps=step,q=q,h=h,ones=sorted(one))
  w,d,q=U[q,int(h in one)]
  if w:one.add(h)
  else:one.discard(h)
  h+=d
 return dict(**{'pass':False},reason='fuel',steps=fuel,q=q,h=h,ones=sorted(one))
passed=0
for size in[2,3,4]:
 for vals in itertools.product(range(4),repeat=size):
  for r in range(size-1):
   for mode in['i','z'if vals[r]==0 else'p']:
    result=check(list(vals),r,mode)
    if not result['pass']:
     out=dict(status='FINITE_COUNTEREXAMPLE',candidate=str(path),earlier_passes=passed,values=vals,selected=r,mode=mode,result=result);path.with_suffix('.replay.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2));sys.exit()
    passed+=1
out=dict(status='FINITE_SCREEN_PASS',candidate=str(path),cases=passed);path.with_suffix('.replay.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
