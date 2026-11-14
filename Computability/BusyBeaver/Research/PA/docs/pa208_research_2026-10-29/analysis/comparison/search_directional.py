from pathlib import Path
from functools import lru_cache
import collections,json,subprocess,sys,time
sys.dont_write_bytecode=True
import source_inventory as I
import search_rotations as S
L=I.L;out=S.work/'directional';out.mkdir(exist_ok=True)

def enum(t,root):
 occ=collections.defaultdict(set);seen=set()
 def visit(q,n):
  if (q,n)in seen:return
  seen.add((q,n));occ[q].add(n)
  if L.leaf(n):return
  for b in(0,1):
   w,d,z=t[q,b]
   if(w,d)==(b,1):visit(z,n[b])
 visit(84,root)
 incoming=collections.defaultdict(list)
 for(p,b),(_,_,q)in t.items():incoming[q].append((p,b))
 rotations=[]
 for p,ns in occ.items():
  if (p,0)not in t or any(L.leaf(n)for n in ns):continue
  if any(t[p,b][:2]!=(b,1)for b in(0,1)):continue
  for side in(0,1):
   q=t[p,side][2]
   if(q,0)not in t or any(t[q,b][:2]!=(b,1)for b in(0,1)):continue
   if incoming[q]!=[(p,side)]or any(L.leaf(n[side])for n in ns):continue
   fs=[(*n[0],n[1])if side==0 else(n[0],*n[1])for n in ns]
   if all(L.boundary(f[0])[0]==0 and L.boundary(f[2])[1]==0 for f in fs):rotations.append((p,q,side))
 return rotations

def rotate(t,root,rot):
 p,q,s=rot
 @lru_cache(None)
 def trans(z,n):
  if z==p:
   if s==0:return n[0][0],(n[0][1],n[1])
   return(n[0],n[1][0]),n[1][1]
  if L.leaf(n):return n
  ch=list(n)
  for b in(0,1):
   w,d,zz=t[z,b]
   if(w,d)==(b,1):ch[b]=trans(zz,n[b])
  return tuple(ch)
 nr=trans(84,root);nt=dict(t)
 if s==0:
  a,b,c=t[q,0][2],t[q,1][2],t[p,1][2]
  nt.update({(p,0):(0,1,a),(p,1):(1,1,q),(q,0):(0,1,b),(q,1):(1,1,c)})
 else:
  a,b,c=t[p,0][2],t[q,0][2],t[q,1][2]
  nt.update({(p,0):(0,1,q),(p,1):(1,1,c),(q,0):(0,1,a),(q,1):(1,1,b)})
 return nt,nr

def key(t):return tuple(t.values())
def test(t,root,hist,folds,idx):
 name=f'candidate{idx:05d}';d=out/name;d.mkdir(exist_ok=True)
 rows=L.sites(root);(d/'machine.tm').write_text(S.encode(t));(d/'sites.json').write_text(json.dumps(rows,separators=(',',':'))+'\n')
 (d/'sites.tsv').write_text(''.join(f'{p}\t{o}\t{-1 if a is None else a}\n'for p,o,a in rows))
 result=subprocess.run([str(S.exe),str(d/'machine.tm'),str(d/'sites.tsv')],capture_output=True,text=True)
 rec={'name':name,'history':hist,'folds':folds,'states':len(t)//2,'pass':result.returncode==0,'message':result.stdout+result.stderr}
 (d/'result.json').write_text(json.dumps(rec,indent=2)+'\n');print(json.dumps(rec),flush=True)
 return rec

def main():
 b=I.base;t=I.read(b/'machine/variant_plain/u208.native.tm');ss=json.loads((b/'machine/variant_plain/u208.sites.json').read_text());root=L.tree(ss)
 maxdepth=int(sys.argv[1])if len(sys.argv)>1 else 3
 seen={key(t)};frontier=[(t,root,[])];results=[];began=time.monotonic()
 for depth in range(1,maxdepth+1):
  nf=[]
  for t,r,hist in frontier:
   for rot in enum(t,r):
    nt,nr=rotate(t,r,rot);k=key(nt)
    if k in seen:continue
    seen.add(k);nh=hist+[rot];mt,folds=S.merge(nt)
    if folds:results.append(test(mt,nr,nh,folds,len(results)))
    elif depth<maxdepth:nf.append((nt,nr,nh))
  print('DEPTH',depth,'frontier',len(nf),'seen',len(seen),'candidates',len(results),'time',time.monotonic()-began,flush=True);frontier=nf
 (out/'results.json').write_text(json.dumps(results,indent=2)+'\n')
if __name__=='__main__':main()
