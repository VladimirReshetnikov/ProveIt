from conditional_pair import *
import random
rng=random.Random(209208)
def quick(T,q,k,driver,ctx,limit=24):
 if ctx.get(0,k)!=k:return True
 vals={i:rng.randrange(2)for i in range(-26,27)};vals.update(ctx);vals[0]=k;w,d,z=T[q,k];expected=dict(vals);expected[0]=w
 h=0;s=driver;v=dict(vals)
 for _ in range(limit):
  if s==254 or h not in v:return False
  w1,d1,s=T[s,v[h]];v[h]=w1;h+=d1
  if(s,h,v)==(z,d,expected):return True
 return False

def run(name,file,depth=8):
 T=read(file);Q=sorted({q for q,k in T});ct,cnt=histories(T,depth);results=[]
 for direction in(-1,1):
  tags={};pairs=[]
  for q in Q:
   if q==0:continue
   for k in(0,1):
    cs=[c for c in ct[q]if c.get(0,k)==k]; vs={c.get(direction)for c in cs}
    if len(vs)==1 and None not in vs:tags[q,k]=vs.pop()
  for k in(0,1):
   for a in Q:
    if tags.get((a,k))!=0:continue
    for b in Q:
     if tags.get((b,k))==1 and T[a,1-k]==T[b,1-k]and T[a,k]!=T[b,k]:pairs.append((a,b,k))
  req=set((q,k)for a,b,k in pairs for q in(a,b));drivers={}
  for q,k in sorted(req):
   good=set()
   for driver in Q:
    cs=[c for c in ct[q]if c.get(0,k)==k]
    if not all(quick(T,q,k,driver,c)for c in cs):continue
    if all(exact(T,T,q,lambda z:z,c,k,start=driver)is not None for c in cs):good.add(driver)
   drivers[q,k]=good
  count=0;possible=0;found=[]
  for(a,b,k),(c,d,l)in itertools.combinations(pairs,2):
   if len({a,b,c,d})!=4:continue
   count+=1
   U=drivers[a,k]&drivers[c,l]-{a,b,c,d};V=drivers[b,k]&drivers[d,l]-{a,b,c,d}
   for u,v in itertools.product(U,V):
    possible+=1;rho=lambda q:a if q==b else c if q==d else q;H=max(Q)+1
    if H==254:H+=1
    C={(q,x):(w,di,rho(z))for(q,x),(w,di,z)in T.items()if q not in(b,d)}
    C[a,k]=(k,direction,H);C[c,l]=(l,direction,H);C[H,0]=(0,-direction,u);C[H,1]=(1,-direction,v)
    if all(exact(T,C,q,rho,context,x)is not None for q in(a,b,c,d)for x in(0,1)for context in ct[q]):
     key=f'macro_{name}_{direction}_{a}_{b}_{c}_{d}_{u}_{v}';write(C,P/(key+'.tm'));found.append(key);print('FOUND',key,flush=True)
  r={'class':name,'direction':direction,'depth':depth,'tags':len(tags),'pairs':len(pairs),'combinations':count,'selector_candidates':possible,'drivers':{str(q)+','+str(k):sorted(v)for(q,k),v in drivers.items()},'found':found};results.append(r);print(name,direction,'pairs',len(pairs),'combinations',count,'selectors',possible,'found',found,flush=True)
 return results
if __name__=='__main__':
 r=run('primary',ROOT/'machine/u208.native.tm')+run('compatibility',ROOT/'alternative/u208.native.tm');(P/'macro_results.json').write_text(json.dumps(r,indent=2))
