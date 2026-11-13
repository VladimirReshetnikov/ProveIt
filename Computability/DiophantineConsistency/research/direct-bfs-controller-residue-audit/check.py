#!/usr/bin/env python3
"""External arithmetic check; not a Lean proof or source-object audit."""
from pathlib import Path
from hashlib import sha256
from math import gcd
import gzip, json, re

research = Path(__file__).resolve().parent.parent
root = research.parent
lean = research / 'direct-bfs-lean-kernel-prototype/DirectBFSSymbolicKernel.lean'
kfile = root / 'candidates/ten-positive-qcube-product-square/coefficients/K.bin.gz'
symbolic = research / 'ordinary12-ipra-bridge/compact44-symbolic-kernel-prototype/CompactSymbolicKernel.lean'
raw = gzip.decompress(kfile.read_bytes())
need = lambda b, s: None if b else (_ for _ in ()).throw(RuntimeError(s))
hash_raw = sha256(raw).hexdigest()
need(hash_raw == '0a86821a704294199c2e1a50379d242c96840a3366e9d965689ba3d74605203f', 'wrong BFS payload')
k = int.from_bytes(raw, 'little')
need(k.bit_length() == 592884, 'wrong byte order or bit length')
text = lean.read_text(); rows_text = text.split('def rows :',1)[1].split('theorem rows_length',1)[0]
rows = [tuple(map(int,x)) for x in re.findall(r'\((\d+),\s*(\d+),\s*(\d+),\s*(\d+)\)', rows_text)]
need(len(rows) == 943, 'wrong row count')
slots_text = symbolic.read_text().split('def slots :',1)[1].split('theorem slots_length',1)[0]
slots = list(map(int,re.findall(r'\d+',slots_text)))
need(len(slots)==41, 'wrong slot count')
modulus = 590069 * 581197
radix = pow(2,67,modulus)
def p(e): return pow(radix,e,modulus)
def value(t):
 w,n,e,s=t
 need(w<256 and n<512 and e<256 and s<512,'row width')
 return w+2**8*n+2**17*e+2**25*s+127*2**34
def selector(t):return 1+2**10*(2**41-value(t))
res = sum(p(e) for e in (30,62,1100,2201))
res += sum(selector(t)*(p(4393-i)+p(5495-i)) for i,t in enumerate(rows))
res += sum(2**(10+i)*(p(4393-x)+p(5495-x)) for i,x in enumerate(slots))
res += p(8807)*p(42)
res %= modulus
need(res==k%modulus==264033855341,'payload and direct symbolic residue differ')
q=pow(2,590069,modulus); pulse=pow(2,67*1063,modulus)
gamma=pulse*(q*q-1)*(1+q*(res+q))%modulus
need(gamma==299052170727 and gcd(gamma,modulus)==1 and pow(gamma,581196,modulus)==1,'unit check failed')
print(json.dumps({'status':'PASS','scope':'external arithmetic only', 'source_sha256':sha256(lean.read_bytes()).hexdigest(), 'slots_source_sha256':sha256(symbolic.read_bytes()).hexdigest(), 'gzip_sha256':sha256(kfile.read_bytes()).hexdigest(), 'raw_sha256':hash_raw,'raw_bytes':len(raw),'byte_order':'little','bit_length':k.bit_length(),'rows':len(rows),'slots':len(slots),'modulus':modulus,'kernel_residue':res,'q_residue':q,'pulse_residue':pulse,'gamma_residue':gamma,'gamma_gcd':gcd(gamma,modulus),'gamma_pow_581196':pow(gamma,581196,modulus)},indent=2))
