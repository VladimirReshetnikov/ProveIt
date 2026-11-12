#!/usr/bin/env python3
"""Independent conditional 87→86 source review; no Lean."""
import hashlib,itertools,json,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];A=D/'research/ordinary14-87-to-86-conditional-map-draft'
def sha(b):return hashlib.sha256(b).hexdigest()
def pin(p,h):
 b=p.read_bytes();assert sha(b)==h,str(p);return b
s=pin(A/'ConditionalMap87To86.lean','f8e33f0decf12d7d3dfd78d6e162d45e0606d80653a3227455a5ac4b5a32ae7c').decode()
pin(A/'check_source.py','336c6a700a4d423225822583e23aec8f740d97d45fbe55c273dc37ac530b5774')
receipt=pin(A/'observation.json','d8aade8fb2dbf645c3447504d204cb21f51aa36ff31e5db67e2d50ea98af9d49')
r=(A/'README.md').read_bytes();tail=(b'\nIndependent source review is recorded in\n'
 b'`../../reviews/ordinary14-87-to-86-conditional-map-draft-independent/`.\n')
assert r.endswith(tail) and sha(r[:-len(tail)])=='a6f859722c2f4b8027b629fab3af4592d6801f32b12064c451a3ae2e27e36674'
for f in ('Function.update v 13 (v 13-C beta v*K)',
 '(hgap : v 1+v 2<q beta v) (hstrict : C beta v*K<v 13)',
 'have hC := cast_C beta v hgap','P72Root.ι_tsub (le_of_lt hstrict)',
 'tsub_pos_of_lt hstrict','rw [←cast_reverse p beta K v hport hK hgap hstrict] at h',
 'rw [←h]','(hz : InternalZero (P87ShiftedGuard.graph p).output v)'):
 assert f in s,f
n=0
for q,F,a,K,omega in itertools.product(range(1,12),range(1,6),range(0,6),range(5),range(1,15)):
 if F+a<q and (q-F-a)*K<omega:
  C=max(0,max(0,q-F)-a); h=max(0,omega-C*K)
  assert h>0 and h+C*K==omega
  n+=1
assert n>0
# Strictness is required to make the reconstructed natural coordinate positive.
assert max(0,6-2*3)==0

def replay(p,expected):
 rr=subprocess.run([sys.executable,'-I','-S','-B',str(p)],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=300)
 assert not rr.stderr and rr.stdout==expected
replay(A/'check_source.py',receipt)
p=D/'reviews/ordinary14-86-to-87-positive-map-draft-independent';replay(p/'check.py',(p/'result.json').read_bytes())
print(json.dumps({'scope':'conditional source review only; no Lean or unconditional reverse theorem',
 'prelink_readme_sha256':sha(r[:-len(tail)]),'bounded_strict_cases':n},sort_keys=True,indent=2))
