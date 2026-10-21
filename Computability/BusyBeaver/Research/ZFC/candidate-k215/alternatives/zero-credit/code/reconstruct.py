#!/usr/bin/env python3
"""Reconstruct the new machine/source from frozen immediate parent data."""
from pathlib import Path
import hashlib,json,sys,argparse
import source_language as U
ROOT=Path(__file__).resolve().parents[1]

def sha(raw):return hashlib.sha256(raw).hexdigest()
def table(raw):
 out={};start=None
 for line in raw.decode().splitlines():
  if line.startswith('#! start '):start=int(line[9:]);continue
  if not line or line.startswith('#'):continue
  q,b,w,d,z=line.split();q,b,w,z=map(int,(q,b,w,z));assert(q,b)not in out
  assert b in(0,1)and w in(0,1)and d in('L','R');out[q,b]=(w,d,z)
 return start,out

def encode(T,start):
 return ('#! start '+str(start)+'\n'+''.join(f'{q} {b} {w} {d} {z}\n'for(q,b),(w,d,z)in sorted(T.items()))).encode()
def canonical(T,start,mirror=False):
 mapping={start:0};todo=[start];rows=[]
 for q in todo:
  for b in(0,1):
   w,d,z=T[q,b]
   if(z,0)not in T and(z,1)not in T:t=-1
   else:
    if z not in mapping:mapping[z]=len(mapping);todo.append(z)
    t=mapping[z]
   if mirror:d='L'if d=='R'else'R'
   rows.append([mapping[q],b,w,d,t])
 return rows,mapping

def reconstruct():
 base=ROOT/'reference/commands120';raw=(base/'k215.native.tm').read_bytes();src=(base/'sites215.json').read_bytes()
 assert sha(raw)=='da83e8de52f4d9536cee2d5ed4af4311308bda51196d18891b96e4bc9ca6cb4f'
 assert sha(src)=='d5c994e3d0c8fe26dd337aca48e5f25ff4f28fd18973f2c04c99589d6ba3f53d'
 start,T=table(raw);assert start==0 and len(T)==430
 assert T[8,1]==(1,'R',13)and T[198,0]==(1,'L',40)
 T[8,1]=(1,'R',103);T[198,0]=(0,'L',40)
 native=encode(T,74)
 old=U.tree(json.loads(src));H=U.subtree(old,'0111');assert H==(('CD',6),('CC',2))
 new=U.replace(old,'0111',(H,('CB',1)));sites=U.sites(new)
 assert U.graph_arithmetic(sites)[0]==U.graph_intervals(sites)
 source=(json.dumps(sites,separators=(',',':'))+'\n').encode()
 rows,m=canonical(T,74);assert len(m)==215 and set(m)=={q for q,b in T}
 m[254]=215;dense=encode({(m[q],b):(w,d,m[z])for(q,b),(w,d,z)in T.items()},0)
 assert native==(ROOT/'machine/zc215.native.tm').read_bytes()
 assert dense==(ROOT/'machine/zc215.tm').read_bytes()
 assert source==(ROOT/'source/zc215.sites.json').read_bytes()
 assert json.loads((ROOT/'machine/canonicalization.json').read_text())['native_to_dense']=={str(k):v for k,v in m.items()}
 return {'status':'EXACT_RECONSTRUCTION_PASS','states':215,'rows':430,'source_metrics':U.metrics(new),'native_sha256':sha(native),'dense_sha256':sha(dense),'source_sha256':sha(source),'dense_dispatcher':m[84]}
if __name__=='__main__':
 if not __debug__:raise RuntimeError('Run with assertions enabled')
 print(json.dumps(reconstruct(),indent=2))
