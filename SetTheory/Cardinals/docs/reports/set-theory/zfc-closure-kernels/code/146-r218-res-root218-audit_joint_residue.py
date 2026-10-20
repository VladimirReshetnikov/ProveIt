#!/usr/bin/env python3
"""Check unbounded inductiveness of the zero/even-positive/odd certificate.

This checker does not run the reachability search or import its C++ code.
Images are independently obtained from concrete representatives. The tail
classes have constant parity after either increment or positive decrement,
so representatives 4 and5 cover the entire unbounded tail.
"""
from pathlib import Path
import hashlib,json,struct,sys,time
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'theory_notes'))
from audit_abstract_certificate import compile_cfg,check
source_raw=(ROOT/'baseline219/K219_Construction_2026-10-20/machine/sites219.json').read_bytes()
rows=json.loads(source_raw);cfg=compile_cfg(rows)
prod_raw=(ROOT/'machine218/abstract219.json').read_bytes();prod=json.loads(prod_raw)
assert prod['source_sha256']==hashlib.sha256(source_raw).hexdigest()
check(rows,prod['domains'],[3,0,0,0,3,0,0,0,0])
raw=(ROOT/'root218/joint_residue.bin').read_bytes();n,B,W=struct.unpack_from('<III',raw)
assert (n,B,W)==(len(rows),3**9,(3**9+63)//64)
assert len(raw)==12+n*W*8
blocks=[memoryview(raw)[12+i*W*8:12+(i+1)*W*8] for i in range(n)]
bits=[int.from_bytes(b,'little') for b in blocks]
assert all(b>>B==0 for b in bits)
pow3=[3**j for j in range(9)]
digit=lambda v:0 if v==0 else 1 if v%2==0 else 2
initial=sum(digit(v)*pow3[j] for j,v in enumerate([3,0,0,0,3,0,0,0,0]))
assert bits[0]>>initial&1
began=time.monotonic();profiles=edges=0
for i,((path,op,r),targets,dom,blob) in enumerate(zip(rows,cfg,prod['domains'],blocks)):
 if not bits[i]:continue
 assert dom is not None
 if op=='CH':profiles+=bits[i].bit_count();continue
 if op in ('CC','CB'):
  assert bits[i]&~bits[targets[0]]==0
  count=bits[i].bit_count();profiles+=count;edges+=count;continue
 images=[set() for _ in range(3)]
 for v in range(6):
  if not dom[r]&(1<<min(v,4)):continue
  if op=='CI':j=targets[0];value=v+1
  elif v==0:j=targets[0];value=0
  else:j=targets[1];value=v-1
  images[digit(v)].add((j,digit(value)))
 for wi,(word,) in enumerate(struct.iter_unpack('<Q',blob)):
  while word:
   low=word&-word;mask=64*wi+low.bit_length()-1;word-=low;profiles+=1
   old=(mask//pow3[r])%3
   for target,new in images[old]:
    z=mask+(new-old)*pow3[r]
    assert blocks[target][z//8]>>(z%8)&1,(i,mask,target,z)
    edges+=1
 if i%500==0:print('AUDIT',i,'profiles',profiles,'edges',edges,flush=True)
assert profiles==sum(b.bit_count() for b in bits)
digit_masks=[[sum(1<<m for m in range(B) if m//pow3[r]%3==d) for d in range(3)] for r in range(9)]
per_point=[]
for i,b in enumerate(bits):
 possible=[[d for d in range(3) if b&digit_masks[r][d]] for r in range(9)]
 per_point.append(dict(ordinal=i,profiles=b.bit_count(),digits=possible))
result=dict(status='INDEPENDENT_JOINT_RESIDUE_INDUCTIVE_CERTIFICATE_PASS',source_sha256=hashlib.sha256(source_raw).hexdigest(),product_certificate_sha256=hashlib.sha256(prod_raw).hexdigest(),binary_certificate_sha256=hashlib.sha256(raw).hexdigest(),profiles=profiles,closure_edges=edges,seconds=time.monotonic()-began,classes=['zero','positive even','odd'],scope='All natural register values, by finite abstract induction intersected with independently checked product invariant.',points=per_point)
(ROOT/'root218/joint_residue_audit.json').write_text(json.dumps(result,separators=(',',':'))+'\n')
print(json.dumps({k:v for k,v in result.items() if k!='points'},indent=2))
