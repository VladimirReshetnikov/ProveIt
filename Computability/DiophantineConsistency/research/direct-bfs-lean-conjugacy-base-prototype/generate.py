#!/usr/bin/env python3
"""Reproduce array-backed mappings from the pinned finite candidate source."""
from pathlib import Path
import hashlib,re,sys
here=Path(__file__).resolve().parent
src=here.parent/'direct-bfs-lean-conjugacy-prototype/DirectBFSConjugacy.lean'
if hashlib.sha256(src.read_bytes()).hexdigest()!='c7861effba21ee41e4bbf85e2dad7621779b33fa56371b357877c223759b383c':raise ValueError('candidate source changed')
text=src.read_text()
def parse(name):
 m=re.search(r'def '+name+r' : List Nat := \[([^]]+)\]',text)
 if m is None:raise ValueError('missing '+name)
 return list(map(int,m.group(1).split(',')))
def inverse(a):
 if sorted(a)!=list(range(len(a))):raise ValueError('not a permutation')
 b=[None]*len(a)
 for i,x in enumerate(a):b[x]=i
 return b
h,v,r=map(parse,['horizontal','vertical','rowMap'])
if [len(h),len(v),len(r)]!=[250,439,943]:raise ValueError('wrong sizes')
out='''import DirectBFSSymbolicKernel
import DiophantineConsistency.Compact943Data

/-! Array-backed candidate typed-color conjugacy; assertions are separate. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DirectBFSConjugacyBase
'''
for name,a in [('horizontal',h),('horizontalInverse',inverse(h)),('vertical',v),('verticalInverse',inverse(v)),('rowMap',r),('rowInverse',inverse(r))]:out+=f'def {name} : Array Nat := #[{",".join(map(str,a))}]\n'
out+='''
def original : Array (Nat × Nat × Nat × Nat) := Compact943Data.rows.toArray
def direct : Array (Nat × Nat × Nat × Nat) := DirectBFSSymbolicKernel.rows.toArray

def rename (t : Nat × Nat × Nat × Nat) : Nat × Nat × Nat × Nat :=
  (horizontal.getD t.1 0,vertical.getD t.2.1 0,horizontal.getD t.2.2.1 0,vertical.getD t.2.2.2 0)
end DirectBFSConjugacyBase
'''
p=here/'DirectBFSConjugacyBase.lean'
if '--check' in sys.argv:
 if p.read_text()!=out:raise ValueError('source mismatch')
 print('array-backed source reproduced exactly')
elif p.exists():raise ValueError('refuse overwrite')
else:p.write_text(out)
