#!/usr/bin/env python3
"""Check source-pinned modular lemma and the L-2 matching residues."""
from pathlib import Path
import hashlib,json,subprocess,sys
root=Path(__file__).resolve().parents[2]
here=Path(__file__).resolve().parent
for name,digest in json.loads((here/'pins.json').read_text()).items():
    assert hashlib.sha256((root/name).read_bytes()).hexdigest()==digest, name
prev='research/ordinary13-i-unshift-fixed-shifted-power-modular-obstructions/'
run=subprocess.run([sys.executable,'-I','-S','-B',str(root/prev/'check.py')],
                   check=True,capture_output=True,text=True)
assert run.stdout==(root/prev/'receipt.json').read_text()
data=json.loads(run.stdout)
assert data['rho_beta_MC_high_MF_mod3']==[2,1,1,0,1]
# The pinned previous certificate checks all graph rank row bindings.
assert all(((q-1)*(1+q))%3==0 for q in (1,2))
poly=[(4*l*l-10*l+1)%9 for l in range(9)]
assert poly==[1,4,6,7,7,6,4,1,6] and 0 not in poly
for L in range(2,100):
    numerator=(L-2)*(2*L-1)
    assert (numerator%3==0)==(L%3==2)
    if numerator%3==0:
        n=numerator//3; d=L-2
        assert n*(L+1-d)==d*(d+L+1)
        assert n%3==0 and (2*n-1)%3==2
print(json.dumps({'rank_mod3_when_q_is_a_power_of_two':0,
  'offset':'d=L-2','matching_n':'(L-2)*(2*L-1)/3',
  'integer_n_requires_L_mod3':2,'integer_n_implies_rank_mod3':2,
  'rank_numerator_mod9':poly,'matching_rank_impossible':True,
  'other_offsets_or_rank_changes_excluded':False,'graph_zero_nonexistence_proved':False,
  'lean_executed':False,'huge_constants_expanded':False},indent=2,sort_keys=True))
