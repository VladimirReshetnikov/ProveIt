from pathlib import Path
from functools import lru_cache
import json,hashlib,argparse
if not __debug__:raise SystemExit('Assertions required')
ap=argparse.ArgumentParser();ap.add_argument('--old',type=Path,required=True);ap.add_argument('--new',type=Path,required=True);ap.add_argument('--output',type=Path,required=True);args=ap.parse_args()
oldpath,newpath=args.old,args.new
assert hashlib.sha256(oldpath.read_bytes()).hexdigest()=='05e7caa159d95cdf9ee254d313c44c52369ac91e52cbc23d54b15f0b64b95922'
assert hashlib.sha256(newpath.read_bytes()).hexdigest()=='3511c2772d815348e0113c790dfd1494bb2d824701c17ef762daaa89e3c8040c'
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
oldrows=json.loads(oldpath.read_text());rows=json.loads(newpath.read_text());old=tree(oldrows);new=tree(rows)
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
before=resolve(oldrows);after=resolve(rows);assert before==continuation_cfg(old)and after==continuation_cfg(new)
cut=len(oldrows);assert cut==4775 and len(rows)==cut+2
assert rows[-2:]==[['10','CI',6],['11','CC',2]]
assert after[-2:]==[['CI',6,[cut+1]],['CC',None,[0]]]
changes=[]
for i,(a,b)in enumerate(zip(before,after)):
 assert a[:2]==b[:2]or a[0]in('CB','CC')and b[0]in('CB','CC'),(i,a,b)
 want=[cut if v==0 else v for v in a[2]]
 assert b[2]==want,(i,a,b,want)
 if a!=b:changes.append({'ordinal':i,'old_site':oldrows[i],'new_site':rows[i],'old':a,'new':b})
assert at(new,'000')==(at(old,'0'),at(old,'10'))
blocks=[]
for name,np,op in [('AX','0011001','1101001'),('MP','001101','110101'),('S','01','111')]:
 a,b=at(new,np),at(old,op);assert a==b;blocks.append({'name':name,'new_path':np,'old_path':op,'leaves':length(a),'literal_subtree_identical':True})
assert [x['ordinal']for x in changes]==[4696,4772]
record={'status':'EXACT_COMPOSITE_CONSTANT_BIAS_SOURCE_PASS','old_sha256':hashlib.sha256(oldpath.read_bytes()).hexdigest(),'source_sha256':hashlib.sha256(newpath.read_bytes()).hexdigest(),'old_leaves':cut,'new_leaves':len(rows),'nodes':len(nodes(new)),'independent_resolvers_agree':True,'all_old_returns_redirected_to_footer':True,'changed_return_edges':changes,'blocks':blocks,'footer':after[-2:],'scope':'Complete finite ordinal CFG equality after replacing every old return-to0 by4775, plus literal prelude/AX/MP/S identity. The existing composite-S compiler and separately proved constant-bias scheduler establish logical calibration; runtime, credit, and blankstartup remain separate obligations.'}
args.output.write_text(json.dumps(record,indent=2)+'\n');print(json.dumps(record,indent=2))
