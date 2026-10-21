from pathlib import Path
from functools import lru_cache
import argparse,json,hashlib
if not __debug__:raise SystemExit('Assertions required')
ap=argparse.ArgumentParser();ap.add_argument('--old',type=Path,required=True);ap.add_argument('--new',type=Path,required=True);ap.add_argument('--output',type=Path,required=True);args=ap.parse_args()
def tree(rows):
 leaves={p:(op,k) for p,op,k in rows}
 assert len(leaves)==len(rows)
 used=[]
 def build(p):
  if p in leaves: used.append(p); return leaves[p]
  assert any(q.startswith(p) for q in leaves), ('incomplete tree',p)
  return build(p+'0'),build(p+'1')
 t=build(''); assert used==[r[0] for r in rows]; return t

def leaf(t):return isinstance(t[0],str)
@lru_cache(None)
def length(t):return 1 if leaf(t) else length(t[0])+length(t[1])
def at(t,p):
 for c in p:t=t[int(c)]
 return t
def nodes(t):
 out=set()
 def walk(x):
  if x in out:return
  out.add(x)
  if not leaf(x):walk(x[0]);walk(x[1])
 walk(t);return out

def continuation_cfg(t):
 N=length(t);out=[]
 def walk(n,start,breaks,continues):
  if leaf(n):
   op,k=n;after=(start+1)%N
   def target(stack,k):return stack[-k]%N if len(stack)>=k else 0
   edges=[] if op=='CH' else [target(continues,k)] if op=='CC' else [target(breaks,k)] if op=='CB' else [target(breaks,1),after] if op=='CD' else [after]
   assert len(out)==start
   out.append([op,None if op in ('CB','CC') else k,edges]);return
  end=start+length(n);middle=start+length(n[0])
  walk(n[0],start,breaks+[end],continues)
  walk(n[1],middle,breaks,continues+[start])
 walk(t,0,[],[]);return out
def resolve(rows):
 leaves={p:i for i,(p,_,_)in enumerate(rows)};ints={}
 def visit(p):
  if p in leaves:z=(leaves[p],leaves[p]+1)
  else:
   a=visit(p+'0');b=visit(p+'1');assert a[1]==b[0];z=(a[0],b[1])
  ints[p]=z;return z
 assert visit('')==(0,len(rows))
 def jump(p,bit,k):
  while p:
   b=p[-1];p=p[:-1]
   if b==bit:
    k-=1
    if not k:return ints[p][0]if bit=='1'else ints[p][1]%len(rows)
  return 0
 cfg=[]
 for i,(p,op,k)in enumerate(rows):
  if op=='CI':edges=[(i+1)%len(rows)]
  elif op=='CD':edges=[jump(p,'0',1),(i+1)%len(rows)]
  elif op in('CB','CC'):edges=[jump(p,'0'if op=='CB'else'1',k)]
  else:assert op=='CH';edges=[]
  cfg.append([op,k if op in('CI','CD')else None,edges])
 return cfg

def replace(t,p,n):
 if not p:return n
 k=int(p[0]);return tuple(replace(t[j],p[1:],n)if j==k else t[j]for j in (0,1))
H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert H(args.old)=='212cf0ffde43c1cc22c183dd8bf0b3a699396f96c9942ee92a7cc372cd273ca9'
assert H(args.new)=='b64d9fa23d97e7c81154468e9a62a5d8e12b39709d2a4d45c5ca9a4e40ca51ce'
os=json.loads(args.old.read_text());ns=json.loads(args.new.read_text());old=tree(os);new=tree(ns)
assert new==replace(old,'0000111',(at(old,'0000111'),('CB',1)))
oc=continuation_cfg(old);nc=continuation_cfg(new);assert oc==resolve(os) and nc==resolve(ns)
j=lambda x:x if x<9 else x+1
changed=[]
for i in range(len(os)):
 assert os[i][1:]==ns[j(i)][1:]
 want=[j(v)for v in oc[i][2]]
 if nc[j(i)][2]!=want:changed.append([i,j(i),oc[i][2],nc[j(i)][2],want])
assert changed==[[7,7,[9,8],[9,8],[10,8]]]
assert nc[9]==['CB',None,[24]] and ns[24][1:]==['CD',3]
sfirst=next(i for i,(p,o,k)in enumerate(os)if p=='010');accesses=sorted({k for p,o,k in os[sfirst:]if o in ('CI','CD')})
assert not({0,3,8}&set(accesses))
out=dict(status='EXACT_FORCED_TRANSFER_SOURCE_PASS',old_sha256=H(args.old),source_sha256=H(args.new),leaves=len(ns),nodes=len(nodes(new)),changed_edges=changed,inserted_target=24,S_register_accesses=accesses,scope='Literal insertion and full CFG transport; inserted return selects S, not root. Written loop proof establishes forced-S then candidate n-1.')
args.output.write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
