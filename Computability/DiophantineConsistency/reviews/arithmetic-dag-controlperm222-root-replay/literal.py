from pathlib import Path
from functools import lru_cache
import re,json,hashlib
R=Path('/home/codex/.codex/worktrees/46be/Proofs');B=R/'Computability/BusyBeaver/Lean/BusyBeaver/ZFC'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
nodes={};pins=[]
for name,expected in [('Dag222',461),('Dag219',7),('DagDom',18),('DagPerm',7)]:
 p=B/(name+'.lean');parsed={};pins.append(dict(path=str(p),sha256=sha(p)))
 for line in p.read_text().splitlines():
  h=re.match(r'\s*\| (\d+) =>',line)
  if h:
   es=re.findall(r'\.(node|inc|decnz|brk|cont|halt)(?: (\d+))?',line)
   assert len(es)==2,line
   parsed[int(h[1])]=tuple((k,int(n)if n else 0)for k,n in es)
 assert len(parsed)==expected
 nodes.update(parsed)
assert set(nodes)==set(range(487))
@lru_cache(None)
def stats(e):
 if e[0]!='node':return 0,1
 a,b=nodes[e[1]];ha,sa=stats(a);hb,sb=stats(b);return max(ha,hb)+1,sa+sb
phys=[6,2,0,4,3,7,8,5,1]
def leaves(e,path=()):
 if e[0]!='node':return [(path,e)]
 a,b=nodes[e[1]];return leaves(a,path+(False,))+leaves(b,path+(True,))
entries=leaves(('node',0))
def inc(path):
 q=list(path);i=len(q)-1
 while i>=0 and q[i]:q[i]=False;i-=1
 if i>=0:q[i]=True
 return tuple(q)
def strip(path,bit,k):
 i=len(path)
 while i>0 and k>0:
  i-=1
  if path[i]==bit:k-=1
 return path[:i]
def resolve(path):
 e=('node',0);offset=0;depth=0
 while e[0]=='node':
  a,b=nodes[e[1]];bit=path[depth]if depth<len(path)else False;depth+=1
  if bit:offset+=stats(a)[1];e=b
  else:e=a
 return offset+1
pathRows=[]
for path,(op,r)in entries:
 if op=='halt':row=(4,0,0,0)
 elif op=='inc':q=resolve(inc(path));row=(1,phys[r],q,q)
 elif op=='decnz':row=(2,phys[r],resolve(inc(strip(path,False,1))),resolve(inc(path)))
 elif op=='brk':q=resolve(inc(strip(path,False,r)));row=(3,0,q,q)
 elif op=='cont':q=resolve(strip(path,True,r));row=(3,0,q,q)
 else:raise AssertionError(op)
 pathRows.append(row)
def car(c,n,E):
 def F(tag,k=0):
  if tag=='normal':return c+n
  if tag=='brk':return E('normal')if k<=1 else E('brk',k-1)
  if tag=='cont':return E(tag,k)
  return 0
 return F
def cdr(c,E):
 def F(tag,k=0):
  if tag=='cont':return c if k==1 else E(tag,max(k-1,0))
  return E(tag,k)if tag!='halt'else 0
 return F
def build(e,c,E):
 op,r=e
 if op=='node':
  a,b=nodes[r];n=stats(a)[1];return build(a,c,car(c,n,E))+build(b,c+n,cdr(c,E))
 if op=='halt':return [(4,0,0,0)]
 if op=='inc':q=E('normal');return [(1,phys[r],q,q)]
 if op=='decnz':return [(2,phys[r],E('brk',1),E('normal'))]
 if op=='brk':q=E('normal')if r==0 else E('brk',r);return [(3,0,q,q)]
 assert op=='cont'and r>0;q=E('cont',r);return [(3,0,q,q)]
occRows=build(('node',0),1,lambda *_:1)
assert occRows==pathRows and len(pathRows)==4751
assert all(0<=op<8 and 0<=r<9 and 0<=a<8192 and 0<=b<8192 for op,r,a,b in pathRows)
packed=sum((op+8*r+128*a+1048576*b)<<(36*i)for i,(op,r,a,b)in enumerate(pathRows))
result=dict(scope='Read-only finite proposal audit from current literal source; not a Lean certificate and no old generator executed.',root_node=0,node_count=487,root_depth=stats(('node',0))[0],row_count=len(pathRows),dual_construction_equal=True,physical_map=phys,max_successor=max(max(r[2:])for r in pathRows),all_nonhalt_successors_positive=all(a>0 and b>0 for op,_,a,b in pathRows if op!=4),packed_width=36,packed_bit_length=packed.bit_length(),rows_sha256=hashlib.sha256(json.dumps(pathRows,separators=(',',':')).encode()).hexdigest(),first_rows=pathRows[:10],last_rows=pathRows[-4:],sources=pins,script=dict(path=__file__,sha256=sha(__file__)))


source= B/'ArithmeticDagControlPerm222.lean'
literal=re.search(r'^def packedRows : Nat := (0x[0-9a-fA-F]+)$',source.read_text(),re.M)
if literal is None:raise RuntimeError('unique packed literal')
if int(literal[1],16)!=packed:raise RuntimeError('complete packed integer mismatch')
if packed >= 2**(36*4751):raise RuntimeError('extra high slots')
for index,row in enumerate(pathRows):
 raw=(packed>>(36*index))%(1<<36)
 if raw != row[0]+8*row[1]+128*row[2]+1048576*row[3]:
  raise RuntimeError('complete slot mismatch '+str(index))
result.update(status='PASS_FULL_LITERAL',source=dict(path=str(source),sha256=sha(source)),
 literal_sha256=hashlib.sha256(literal[1].encode()).hexdigest(),
 complete_slot_count=len(pathRows),no_high_bits=True)
print(json.dumps(result,indent=2))
