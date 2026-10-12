from pathlib import Path
import json,time,sys
import sympy as S
from compiler import *
if not __debug__:raise RuntimeError('Verification must not run with python -O.')
root=Path(__file__).resolve().parents[1]
cases=[('triple-pole-r2',2,[(0,3,1)],()),('quartic-pole-r2',2,[(0,4,1)],()),('triple-pole-r3',3,[(0,3,1)],()),('adjacent-two-r2',2,[(0,1,1),(1,1,2)],()),('separated-two-r2',2,[(0,1,1),(3,1,-2)],()),('three-simple-r3',3,[(0,1,1),(1,1,1),(2,1,1)],()),('shifted-double-r2',2,[(1,2,1)],()),('mixed-poles-r2',2,[(0,2,1),(1,1,2)],()),('polynomial-plus-pole',2,[(1,1,2)],(1,1))]
checks=[];artifacts=[]
for name,r,poles,poly in cases:
 t0=time.time(); print('START',name,flush=True)
 ex=hankel(r,poles,poly);f=compile_expression(ex)
 ts=taylor(f,10)
 for n in range(1,11):assert ts[n]==direct_determinant(r,n,poles,poly),(name,n,ts[n])
 assert ts[0]==0
 W=capacity(r,poles);mw=max(map(len,f),default=0)
 assert mw<=W,(name,mw,W)
 checks.append(dict(name=name,rank=r,poles=poles,weight_budget=W,output_max_word_length=mw,hyperlog_terms=len(f),exact_coefficients_checked=11,seconds=round(time.time()-t0,3)))
 artifacts.append(dict(name=name,determinant=str(ex),generator=encode(f)))
 (root/'data'/'compiler_checks.json').write_text(json.dumps(checks,indent=2))
 (root/'data'/'compiled_examples.json').write_text(json.dumps(artifacts,indent=2))
 print('PASS',checks[-1],flush=True)
# Zero weights and invalid ranks are handled explicitly, not left to SymPy.
assert compile_hankel(2, []) == {}
assert compile_hankel(3, [(0, 2, 1), (0, 2, -1)]) == {}
for invalid_rank in (-1, 1.5, True):
 try:
  hankel(invalid_rank, [(0, 1, 1)])
 except ValueError:
  pass
 else:
  raise AssertionError('Invalid rank accepted')
# Genuine corruption control: remove a nonempty word term from a known formula.
f=compile_hankel(2,[(0,3,1)]);bad=dict(f);bad[(0,1,0,1)]+=1/(1-z)
assert taylor(bad,4)!=taylor(f,4)
(root/'data'/'compiler_summary.json').write_text(json.dumps({'case_count':len(checks),'exact_taylor_comparisons':11*len(checks),'corrupted_generator_rejected':True,'zero_weight_regressions':2,'invalid_rank_regressions':3},indent=2))
