from base import *
from history_search import histories
import hashlib
P=Path(__file__).resolve().parent
ROOT=P/'inputs'

def exact(T,C,q,rho,ctx,b,limit=24,start=None):
 if 0 in ctx and ctx[0]!=b:return []
 ow,od,oz=T[q,b];oz=rho(oz);ctx=dict(ctx);ctx[0]=b
 stack=[(rho(q) if start is None else start,0,{},ctx,[])];cert=[]
 while stack:
  s,h,writes,vals,tr=stack.pop()
  if tr and (s,h)==(oz,od) and all(writes.get(x,vals.get(x,('v',x)))==(ow if x==0 else vals.get(x,('v',x)))for x in set(writes)|{0}):cert.append({'input':vals,'trace':tr});continue
  if s==254 or len(tr)>=limit:return None
  k=writes.get(h,vals.get(h))
  if k is None:
   for b1 in(0,1):v=dict(vals);v[h]=b1;stack.append((s,h,dict(writes),v,tr))
   continue
  w,d,z=C[s,k];wr=dict(writes);wr[h]=w;stack.append((z,h+d,wr,vals,tr+[[s,h,k,w,d,z]]))
  if len(stack)+len(cert)>4096:return None
 return cert

def run(name,file,depth=7):
 T=read(file);Q=sorted({q for q,b in T});ct,cnt=histories(T,depth);tags={};pairs={0:[],1:[]}
 for q in Q:
  if q==0:continue
  for b in(0,1):
   cs=[c for c in ct[q]if c.get(0,b)==b]; vals={c.get(-1)for c in cs}
   if len(vals)==1 and None not in vals:tags[q,b]=vals.pop()
 for b in(0,1):
  for a in Q:
   if tags.get((a,b))!=0:continue
   for c in Q:
    if tags.get((c,b))!=1:continue
    if T[a,1-b]==T[c,1-b] and T[a,b]!=T[c,b]:pairs[b].append((a,c))
 print(name,'tags',len(tags),'pairs',list(map(len,pairs.values())),flush=True)
 count=0;hits=[]
 for(a,b),(c,d)in itertools.product(pairs[0],pairs[1]):
  if len({a,b,c,d})!=4:continue
  count+=1;rho=lambda q:a if q==b else c if q==d else q
  def act(q,k):w,di,z=T[q,k];return(w,di,rho(z))
  U=[q for q in Q if q not in(b,d) and act(q,0)==act(a,0) and act(q,1)==act(c,1)]
  V=[q for q in Q if q not in(b,d) and act(q,0)==act(b,0) and act(q,1)==act(d,1)]
  for u,v in itertools.product(U,V):
   H=max(Q)+1
   if H==254:H+=1
   C={(q,k):(w,di,rho(z))for(q,k),(w,di,z)in T.items()if q not in(b,d)}
   C[a,0]=(0,-1,H);C[c,1]=(1,-1,H);C[H,0]=(0,1,u);C[H,1]=(1,1,v)
   cert=[]
   for q in(a,b,c,d):
    for k in(0,1):
     for context in ct[q]:
      ex=exact(T,C,q,rho,context,k)
      if ex is None:break
      cert.append({'q':q,'b':k,'context':context,'branches':ex})
     else:continue
     break
    else:continue
    break
   else:
    key=f'{name}_{a}_{b}_{c}_{d}_{u}_{v}';write(C,P/(key+'.tm'));(P/(key+'.certificate.json')).write_text(json.dumps(cert));hits.append(key);print('FOUND',key,flush=True)
 r={'name':name,'input_sha256':hashlib.sha256(file.read_bytes()).hexdigest(),'depth':depth,'history_nodes':sum(cnt.values()),'tags':len(tags),'pairs':{k:len(v)for k,v in pairs.items()},'combinations':count,'found':hits};print(r,flush=True);return r
if __name__=='__main__':
 r=[run('primary',ROOT/'machine/u208.native.tm'),run('compatibility',ROOT/'alternative/u208.native.tm')];(P/'conditional_results.json').write_text(json.dumps(r,indent=2))
