from pathlib import Path
import json,collections
P=Path(__file__).resolve().parent
T={}
for l in(P/'runtime193.native.tm').read_text().splitlines():
 q,b,w,d,n=l.split();T[int(q),int(b)]=int(w),1 if d=='R' else-1,int(n)
R=json.loads((P/'single_hit_checks.json').read_text());S=json.loads((P/'pa194.sites.json').read_text());I=json.loads((P/'pa194.instructions.json').read_text());physical=[6,2,0,4,3,7,8,5,1]
def frame(site,vs,n=0,extra=0):
 ones={-1,48+n+extra};ones.update(j for j,b in enumerate(S[site][0])if b=='1');pos=49+n+extra
 for v in vs:ones.update(range(pos+1,pos+v+2));pos+=v+2
 return ones

trie={}
for i,entry in enumerate(S):
 node=trie
 for ch in entry[0]:node=node.setdefault(int(ch),{})
 node['pc']=i

def clean_frame(q,h,ones):
 if q!=84 or not ones or min(ones)!=h-1:return False
 node=trie;pos=h
 while 'pc'not in node:
  b=int(pos in ones)
  if b not in node:return False
  node=node[b];pos+=1
 high=max(ones)
 while pos<=high and pos not in ones:pos+=1
 if pos>high or pos<h+48:return False
 vals=[];pos+=1
 while pos<=high:
  if pos in ones or pos+1 not in ones:return False
  cnt=0;pos+=1
  while pos in ones:cnt+=1;pos+=1
  vals.append(cnt-1)
 return len(vals)>=10

def check(rows,site,br,n=0):
 vs=[0]*9+[1];code=I[site]
 if br is not None and not br[1]:vs[br[0]]=1
 targetvs=list(vs);extra=0
 if code[0]=='dec':
  r=physical[code[1]];nxt=code[2]if vs[r]==0 else code[3]
  if vs[r]:targetvs[r]-=1;extra=1
 elif code[0]=='inc':
  targetvs[physical[code[1]]]+=1;targetvs.append(1);nxt=code[2]
 elif code[0]=='jump':nxt=code[1]
 else:nxt=None
 ones=frame(site,vs,n);expected=frame(nxt,targetvs,n,extra)if nxt is not None else None
 q=84;h=0;seen={};trace=[]
 ray={}
 for src in {q for q,b in rows}:
  z=src;direction=None;vis=set()
  while z!=254 and z not in vis:
   vis.add(z);w,d,to=rows[z,0]
   if direction is not None and d!=direction:break
   direction=d;z=to
  else:
   if z in vis:ray[src]=direction
 for st in range(20001):
  if st and clean_frame(q,h,ones):
   return dict(kind='correct_root'if(h==0 and ones==expected)else'wrong_root',steps=st,head=h,actual_ones=sorted(ones),expected_ones=sorted(expected or[]),site=site,branch=br,values=vs,gap=n)
  if q==254:return dict(kind='correct_halt'if nxt is None else'wrong_halt',steps=st,site=site,branch=br,values=vs,gap=n)
  if q in ray and h not in ones and(not ones or(ray[q]>0 and h>max(ones))or(ray[q]<0 and h<min(ones))):return dict(kind='outward_ray',steps=st,site=site,branch=br,values=vs,gap=n,ray_state=q,ray_head=h,ones=sorted(ones))
  if st==20000:return dict(kind='bound',steps=st,site=site,branch=br,values=vs,gap=n)
  # Only small configurations need recording; exact equality checks yield cycle.
  if len(ones)<1000:
   key=q,h,tuple(sorted(ones))
   if key in seen:return dict(kind='exact_cycle',steps=st,cycle_start=seen[key],site=site,branch=br,values=vs,gap=n)
   seen[key]=st
  w,d,q=rows[q,int(h in ones)];(ones.add if w else ones.discard)(h);h+=d
out={}
for idx,rec in R.items():
 if rec.get('symbolic',{}).get('ok')==False:
  q,b,w,d,n=rec['edit'];rows=dict(T);rows[q,b]=w,1 if d=='R'else-1,n;site,br=rec['symbolic']['failed'];checks=[check(rows,site,br,g)for g in[0,1,10]]
  out[idx]=dict(edit=rec['edit'],checks=checks)
print(collections.Counter(x['kind']for r in out.values()for x in r['checks']))
print('baseline0',check(T,0,[7,True])['kind']);print('baselinepositive',check(T,0,[7,False])['kind'])
assert out==json.loads((P/'physical_counterchecks.json').read_text())
