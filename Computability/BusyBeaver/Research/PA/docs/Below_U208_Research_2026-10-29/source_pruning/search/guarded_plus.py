import sys,json,random,hashlib
from pathlib import Path
from collections import defaultdict
import source_language as L
B=Path(sys.argv[1]).resolve(); OUT=Path(sys.argv[2]).resolve()
def read(p):
 t={}
 for line in p.read_text().splitlines():
  if not line or line[0]=='#':continue
  q,b,w,d,z=line.split();t[int(q),int(b)]=(int(w),1 if d=='R'else-1,int(z))
 return t
def enc(t):return '#! start 0\n'+''.join(f'{q} {b} {w} {"R"if d==1 else"L"} {z}\n'for(q,b),(w,d,z)in sorted(t.items()))
def segment(t,q,p,b):
 tape={-1:1,**{i:int(c)for i,c in enumerate(p+str(b))}};old=tape.copy();h=len(p)
 for n in range(50):
  if h==len(p)+1:return(q if tape==old else None)
  if h not in tape or (q,tape[h]) not in t:return
  w,d,q=t[q,tape[h]];tape[h]=w;h+=d
 return

def mapping(root,t):
 places=defaultdict(list)
 def rec(n,q,p):
  places[q].append((p,n))
  if not L.leaf(n):
   for b in(0,1):
    z=segment(t,q,p,b)
    if z is not None:rec(n[b],z,p+str(b))
 rec(root,84,'');return places

def rotations(root,t):
 places=mapping(root,t);inc=defaultdict(list)
 for(q,b),(w,d,z)in t.items():inc[z].append((q,b))
 for q,ps in places.items():
  if len({n for p,n in ps})!=1:continue
  n=ps[0][1]
  if L.leaf(n)or any(t[q,b][:2]!=(b,1)for b in(0,1)):continue
  for side in(0,1):
   r=t[q,side][2]
   if r==254 or inc[r]!=[(q,side)]or any(t[r,b][:2]!=(b,1)for b in(0,1))or L.leaf(n[side]):continue
   if side==0:(a,b),c=n;new=a,(b,c)
   else:a,(b,c)=n;new=(a,b),c
   if any(L.boundary(x)!=(0,0,False)for x in(a,b,c)):continue
   middle=t[r,1-side][2]
   if any(t[middle,bit][:2]!=(bit,1)for bit in(0,1)):continue
   if any(x<162 and x!=89 for x in(q,r)):continue
   tt=t.copy()
   if side==0:
    aa,bb,cc=t[r,0][2],t[r,1][2],t[q,1][2];tt[q,0]=(0,1,aa);tt[q,1]=(1,1,r);tt[r,0]=(0,1,bb);tt[r,1]=(1,1,cc)
   else:
    aa,bb,cc=t[q,0][2],t[r,0][2],t[r,1][2];tt[q,0]=(0,1,r);tt[q,1]=(1,1,cc);tt[r,0]=(0,1,aa);tt[r,1]=(1,1,bb)
   rr=root
   for p,n in ps:rr=L.replace(rr,p,new)
   mm=mapping(rr,tt)
   if sum(1 for ps in mm.values() for p,n in ps if not L.leaf(n)) != 3908:continue
   m=L.metrics(rr)
   if m['maximum_zero_run']>10:continue
   yield rr,tt,(q,r,side,[p for p,n in ps])

def tags(t):
 inc=defaultdict(list)
 for(q,b),(w,d,z)in t.items():inc[z].append((w,d))
 return {q:v[0][0]for q,v in inc.items()if q not in(0,254) and all(d==1 and w==v[0][0]for w,d in v)}
def folds(t):
 tag=tags(t);qs={q for q,b in t}
 # Keep one branch exactly; replace other by a two-cell lookback path via an existing helper.
 for a in sorted(qs):
  for b in sorted(qs):
   if a<b and t[a,0]==t[b,0] and t[a,1]==t[b,1]:yield(a,b,'duplicate',None)
 for a in tag:
  for b in tag:
   if a>=b or tag[a]==tag[b]:continue
   for bit in(0,1):
    if t[a,1-bit]!=t[b,1-bit]:continue
    if t[a,bit][:2]!=(bit,1)or t[b,bit][:2]!=(bit,1):continue
    for helper in qs-{a,b}:
     good=True
     for q in[a,b]:
      tape={-1:tag[q],0:bit};h=-1;s=helper;seen=set()
      for k in range(40):
       if h==1:
        good &= s==t[q,bit][2]and tape=={-1:tag[q],0:bit};break
       if h not in tape or s in(254,a,b) or(s,h,tuple(tape.items()))in seen:good=False;break
       seen.add((s,h,tuple(tape.items())));w,d,s=t[s,tape[h]];tape[h]=w;h+=d
      else:good=False
      if not good:break
     if good:yield(a,b,bit,helper)
def main():
 source=B/'machine/sites.json'
 if not source.exists():source=B/'source/u208.sites.json'
 root=L.tree(json.loads(source.read_text()));t=read(B/'machine/u208.native.tm');rng=random.Random(13);out=OUT;out.mkdir(exist_ok=True)
 beam=[(root,t,[])];seen={enc(t)}
 for depth in range(12):
  new=[];count=0
  for r,t,recipe in beam:
   for rr,tt,move in rotations(r,t):
    key=enc(tt)
    if key in seen:continue
    seen.add(key);count+=1;rec=recipe+[move]
    for fold in folds(tt):
     name=hashlib.sha256(key.encode()).hexdigest()[:12];p=out/name;p.mkdir(exist_ok=True);(p/'prefold.tm').write_text(key);(p/'sites.json').write_text(json.dumps(L.sites(rr),separators=(',',':'))+'\n');(p/'recipe.json').write_text(json.dumps({'rotations':rec,'fold':fold},indent=2));print('FOUND',p,fold,flush=True)
    new.append((rr,tt,rec))
  rng.shuffle(new);beam=new[:16];print('depth',depth,'new',count,'total',len(seen),flush=True)
  if not beam:break
if __name__=='__main__':main()
