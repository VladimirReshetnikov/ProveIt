#!/usr/bin/env python3
"""No-Lean source and finite-example checks for symbolic-k byte windows."""
import hashlib,json,os,pathlib,sys
if not __debug__ or not sys.flags.isolated or not sys.flags.no_site or os.environ.get('PYTHONOPTIMIZE'):raise RuntimeError('isolated nonoptimized Python required')
P=pathlib.Path;root=P.cwd();p=root/'Computability/DiophantineConsistency/research/ordinary12-ipra-bridge/compact44-symbolic-k-byte-window-exploration';H=lambda x:hashlib.sha256(P(x).read_bytes()).hexdigest();t=json.loads((p/'terminal-observation.json').read_bytes());
for name,sha in t['source_sha256'].items():assert H(p/(name+'.lean'))==sha
for name,sha in t['log_sha256'].items():assert H(p/'observations/generic'/(name+'.log'))==sha
assert H(p/'observations/kernel/SymbolicKernelBytes.log')==t['symbolic_log_sha256']=='9064aceff3e27f00bef7cf082463cdf8113cd4acecb0b28b1fe6f89db5e6a8b9'
assert (p/'observations/kernel/SymbolicKernelBytes.log').read_text()==''.join("'SymbolicKernelBytes."+n+"' depends on axioms: [propext, Classical.choice, Quot.sound]\n" for n in ('kernelDigits_bounded','kernel_byte'))
assert [x['exit'] for x in t['generic_sessions']]==[0,0,0,0,1,1,0] and [x['exit'] for x in t['kernel_sessions']]==[0,0]
for d in range(1,9):
 for q in range(0,9):
  for m in range(1,9):
   if d*q % m:continue
   for y in range(150):assert y//d % m == (y%(d*q)//d + (y//(d*q)%(d*q))*q)%m if q else True
# Independent integer examples include crossing offsets, zero padding and j=0.
r=2**67; xs=[r-1,123,0,2**66]; n=sum(x*r**i for i,x in enumerate(xs))
for j in range(80):
 k=8*j;i,s=divmod(k,67);a=xs[i] if i<len(xs) else 0;b=xs[i+1] if i+1<len(xs) else 0
 assert (n//2**k)%256==(a//2**s+b*2**(67-s))%256
assert ((2**66+r)//2**64)%256==12 and (1//2**72)%256==0
print(json.dumps({'status':'PASS_NO_LEAN_SYMBOLIC_K_BYTE_WINDOW_SOURCE_REVIEW','reviewed_commit':'9898cb5114','symbolic_source_sha256':H(p/'SymbolicKernelBytes.lean'),'generic_byte_source_sha256':H(p/'ByteWindow.lean'),'symbolic_log_sha256':H(p/'observations/kernel/SymbolicKernelBytes.log'),'finite_examples':80,'lean_launched':False,'scope':'Source-level and finite examples only; natural symbolic paramKernel, author-only provider, no retained-file, kernelNat, model or internal PRA binding.'},indent=2,sort_keys=True))
