from pathlib import Path
import sys, json, random, hashlib, time, collections
SRC=Path(__file__).resolve().parents[1]/'inputs'
sys.path.insert(0,str(SRC/'code'))
import source_language as L

def read(path):
 t={}
 for l in Path(path).read_text().splitlines():
  if l.startswith('#') or not l:continue
  q,b,w,d,z=l.split();t[int(q),int(b)]=(int(w),1 if d=='R' else -1,int(z))
 return t

def encode(t):
 return '#! start 0\n'+''.join(f'{q} {b} {w} {"R" if d==1 else "L"} {z}\n' for (q,b),(w,d,z) in sorted(t.items()))

def allnodes(root,p=''):
 yield p,root
 if not L.leaf(root):
  yield from allnodes(root[0],p+'0');yield from allnodes(root[1],p+'1')

def interfaces(t,root):
 paths=collections.defaultdict(list);byq=collections.defaultdict(set)
 for p,node in allnodes(root):
  if L.leaf(node):continue
  q=84;h=0;count=0
  while h<len(p):
   if h<0:break
   b=int(p[h]);w,d,z=t[q,b]
   if w!=b:break
   q=z;h+=d;count+=1
   if count>1000:break
  else:
   paths[q].append(p);byq[q].add(node)
 return paths,byq

def candidates(t,root):
 paths,byq=interfaces(t,root)
 inc=collections.defaultdict(list)
 for k,v in t.items():inc[v[2]].append((k,v))
 pure={q for q,b in t if all(t[q,c][:2]==(c,1) for c in (0,1))}
 ans=[]
 for q in sorted(pure):
  if not paths[q] or len(byq[q])!=1 or any(v[1]!=1 for k,v in inc[q]):continue
  for b in (0,1):
   r=t[q,b][2]
   if r not in pure or inc[r]!=[((q,b),(b,1,r))]:continue
   if len(byq[r])!=1:continue
   node=next(iter(byq[q]))
   if L.leaf(node[b]):continue
   a,c,e=(node[0][0],node[0][1],node[1]) if b==0 else (node[0],node[1][0],node[1][1])
   if any(L.boundary(x)!=(0,0,False) for x in (a,c,e)):continue
   ans.append((q,r,b,paths[q]))
 return ans

def rotate(t,root,cand):
 q,r,b,paths=cand;t=dict(t)
 for p in paths:
  node=L.subtree(root,p)
  if b==0:
   a,c=node[0];e=node[1];node=(a,(c,e))
  else:
   a=node[0];c,e=node[1];node=((a,c),e)
  root=L.replace(root,p,node)
 if b==0:
  a,c,e=t[r,0][2],t[r,1][2],t[q,1][2]
  t.update({(q,0):(0,1,a),(q,1):(1,1,r),(r,0):(0,1,c),(r,1):(1,1,e)})
 else:
  a,c,e=t[q,0][2],t[r,0][2],t[r,1][2]
  t.update({(q,0):(0,1,r),(q,1):(1,1,e),(r,0):(0,1,a),(r,1):(1,1,c)})
 return t,root

def dup(t):
 vals=collections.defaultdict(list)
 for q,b in t:
  if b==0:vals[t[q,0],t[q,1]].append(q)
 return [qs for qs in vals.values() if len(qs)>1]

if __name__=='__main__':
 t=read(SRC/'machine/u208.native.tm');rows=json.loads((SRC/'machine/sites.json').read_text());root=L.tree(rows)
 print('candidates',len(candidates(t,root)),flush=True)
 for c in candidates(t,root):print(c[:3],c[3],flush=True)
 print('dups',dup(t))
