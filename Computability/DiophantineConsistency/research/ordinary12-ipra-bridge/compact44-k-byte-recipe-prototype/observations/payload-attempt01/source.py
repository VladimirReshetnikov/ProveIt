#!/usr/bin/env python3
"""External K local-byte recipe comparison; not a Lean file theorem."""
from hashlib import sha256
from pathlib import Path
import gzip
import json
import re
import sys

ROOT=Path(__file__).resolve().parents[3]
FILES={
 'rows':('research/ordinary12-ipra-bridge/compact44-943-table-prototype/Compact943Data.lean','10a75f23bf358ac745949b9d2717da33c8ccbc4e069892128b913d78d43617f8'),
 'kernel':('research/ordinary12-ipra-bridge/compact44-symbolic-kernel-prototype/CompactSymbolicKernel.lean','f34e96b3d4df160c980632a426aee1340e5c06c93500e899b255610c317da7ae'),
 'param':('research/ordinary12-ipra-bridge/compact44-symbolic-kernel-param-prototype/CompactSymbolicKernelOpaque.lean','fbef8642de957bb39493607cb67edda418f53332af5a92ee594a2a437241e0b8'),
 'mass':('research/ordinary12-ipra-bridge/compact44-coefficient-mass-prototype/CompactCoefficientMass.lean','ca20b0796cbdd1b6c86e6032998fec7d5577b0f775b88d8395db349c7b1b2e6e'),
 'sparse':('research/ordinary12-ipra-bridge/compact44-sparse-k-family-exploration/ConcreteSparseKernel.lean','bf6acf6496295962f2be177aa6ae5aa214f3c66cc01da283daa81226172ae4aa'),
 'windows':('research/ordinary12-ipra-bridge/compact44-symbolic-k-byte-window-exploration/SymbolicKernelBytes.lean','b245515e66a89eba3be43d5edb96197d55c7a5138095c429f21ea920d63761b2'),
 'recipe':('research/ordinary12-ipra-bridge/compact44-k-byte-recipe-prototype/CompactKernelByteRecipe.lean','eb9c2d879a9a8dcd304da80a402d52a4d92bdfcb18c247e54e887914c8528e4b'),
 'binding':('candidates/free-j-polarized-positive/source/positive/coefficients/BINDING.json','dd13365e1c68cd244e67a61abfeb5b351c3ad679acb55a73f714d2885341ee01'),
 'payload':('candidates/free-j-polarized-positive/source/positive/coefficients/payloads/K.bin.gz','b70752bb38570b1e93d480469c63ace9ed4b4552f94eb89d96bc600b1e2a4b6a'),
}
def require(p,msg):
    if not p: raise ValueError(msg)
require(__debug__ and not sys.flags.optimize,'optimized Python rejected')
def digest(b): return sha256(b).hexdigest()
before={key:(ROOT/path).read_bytes() for key,(path,_) in FILES.items()}
for key,(_,pin) in FILES.items(): require(digest(before[key])==pin,'pin mismatch: '+key)
text=before['rows'].decode(); start='-- BEGIN PINNED ORDERED ROWS\n'; end='\n-- END PINNED ORDERED ROWS'
require(text.count(start)==1 and text.count(end)==1,'row markers')
rows=[]
for i,line in enumerate(text.split(start)[1].split(end)[0].splitlines()):
    m=re.fullmatch(r'  \((\d+), (\d+), (\d+), (\d+)\)(,?)',line)
    require(m is not None,'row syntax'); rows.append(tuple(map(int,m.group(1,2,3,4))))
    require(m.group(5)==(',' if i<942 else ''),'row comma')
require(len(rows)==943,'row count')
m=re.search(r'^def slots : List ℕ := \[([0-9,]+)\]$',before['kernel'].decode(),re.M)
require(m is not None,'slot syntax'); slots=list(map(int,m.group(1).split(',')))
require(len(slots)==41 and len(set(slots))==41 and max(slots)<4393,'slot conditions')
def weight(t):
    w,n,e,s=t
    require(0<=w<256 and 0<=n<512 and 0<=e<256 and 0<=s<512,'row bounds')
    return 1+(1<<10)*((1<<41)-(w+(1<<8)*n+(1<<17)*e+(1<<25)*s+127*(1<<34)))
digits=[0]*8850
for e in (30,62,1100,2201): digits[e]+=1
for i,row in enumerate(rows):
    c=weight(row);digits[4393-i]+=c;digits[5495-i]+=c
for i,e in enumerate(slots):
    c=1<<(10+i);digits[4393-e]+=c;digits[5495-e]+=c
digits[8849]+=1
require(all(0<=d<(1<<67) for d in digits),'digit carry bound')
def digit(i): return digits[i] if i<len(digits) else 0
def byte(j):
    q,r=divmod(8*j,67)
    return ((digit(q)>>r)+(digit(q+1)<<(67-r)))%256
recipe=bytes(byte(j) for j in range(74111))
raw=gzip.decompress(before['payload']);meta=json.loads(before['binding'])['ports']['K0']
require(digest(raw)=='c6d523bd32af8dd0345db843cdadf6932bfcad186912a6d112314b60657c554e','raw pin')
require(digest(raw)==meta['sha256_raw'] and digest(before['payload'])==meta['sha256_gzip'],'binding hashes')
require(len(raw)==meta['raw_bytes']==len(recipe)==74111,'length')
require(raw==recipe,'local-window bytes differ from retained payload')
require(int.from_bytes(raw,'little').bit_length()==meta['bits']==592884,'bit length')
require(all((ROOT/path).read_bytes()==before[k] for k,(path,_) in FILES.items()),'input changed')
print(json.dumps({'status':'PASS_EXTERNAL_LOCAL_WINDOW_K_BYTES','rows':len(rows),
 'copy_slots':len(slots),'radix_digits':len(digits),'raw_bytes':len(raw),
 'raw_sha256':digest(raw),'bit_length':meta['bits'],'whole_recipe_matches':True,
 'scope':'external source transcription and gzip comparison; not a Lean file theorem'},indent=2,sort_keys=True))
