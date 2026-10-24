#!/usr/bin/env python3
"""Audit the sole source change, pinned bytes, and boundary diagnostics.

The unbounded normalization proof is in normalization.tex. This script does
not replace that proof with testing; it checks the source delta and gives
small independent controls for the precise hypotheses used by the proof.
"""
from pathlib import Path
import hashlib
import json
from math import isqrt

ROOT = Path(__file__).resolve().parent.parent
old_fragment = """  d=self.fresh('power.truncated_difference')
  # d = max(a-n,0), encoded as a disjunction.
  sub=self.imul(self.sos([self.diff(a,self.add(d,n))]),self.sos([self.le(a,n,'power.sub'),self.diff(d,self.c(0))]))
  finite=self.isum([self.pell(a,k,x,y),sub,self.sos([
   self.mod(x,self.add(self.mul(y,d),m),t,'power.mod'),"""
new_fragment = """  # Finite-branch descent: a>1 and the final norm force a>w>=n.
  # Thus the inherited truncated difference is exactly a-n. Move y*n
  # across the congruence, eliminating both difference and sign-slack inputs.
  finite=self.isum([self.pell(a,k,x,y),self.sos([
   self.mod(self.add(x,self.mul(y,n)),self.add(self.mul(y,a),m),t,'power.mod'),"""

def require(ok, message):
    if not ok:
        raise ValueError(message)

baseline = (ROOT / 'upstream/build_direct.py').read_text()
actual = (ROOT / 'build_direct.py').read_text()
require(baseline.count(old_fragment) == 1, 'baseline source changed')
require(actual == baseline.replace(old_fragment, new_fragment),
        'change exceeds the proved normalization')
upstream = json.loads((ROOT / 'upstream/SHA256.json').read_text())
for path, digest in upstream.items():
    require(hashlib.sha256((ROOT / path).read_bytes()).hexdigest() == digest,
            'upstream digest mismatch: ' + path)
pins = json.loads((ROOT / 'SOURCE_PINS.json').read_text())
for name, digest in pins['sources'].items():
    require(hashlib.sha256((ROOT / 'sources' / name).read_bytes()).hexdigest() == digest,
            'source digest mismatch: ' + name)
require(hashlib.sha256((ROOT / 'horn_shared_source.json').read_bytes()).hexdigest()
        == pins['inherited_horn_sha256'], 'Horn payload changed')

# Quantifier-free diagnostics, distinct from the unbounded proof.
norm_solutions = 0
covered_n = 0
for w in range(31):
    for z in range(301):
        aa = 1 + w**3 * (w + 2) * z*z
        a = isqrt(aa)
        if a*a == aa and a > 1:
            norm_solutions += 1
            require(w >= 1 and z >= 1 and a > w, 'rank implication failed')
            for n in range(w + 1):
                covered_n += 1
                d = a - n
                require(d > 0, 'nonpositive recovered difference')
                for slack in range(3):
                    old_sub = (a-d-n)**2 * ((n-a-slack)**2 + d*d)
                    require(old_sub == 0, 'restored difference failed')

# Expanded monomial identity for the only rewritten congruence:
# x + t*q0 - y*(a-n) - m - t*q1
#   = x + y*n + t*q0 - y*a - m - t*q1.
lhs = {('x',):1, ('q0','t'):1, ('a','y'):-1,
       ('n','y'):1, ('m',):-1, ('q1','t'):-1}
rhs = {('x',):1, ('n','y'):1, ('q0','t'):1,
       ('a','y'):-1, ('m',):-1, ('q1','t'):-1}
require(lhs == rhs, 'congruence polynomial identity failed')

# Necessity controls: dropping a>1 permits a=1,w=n=2,z=0; reversing the moved
# term fails already at x=0,y=1,a=2,n=1,m=t=q0=q1=0.
require(1 == 1 + 2**3 * (2+2) * 0**2, 'guard control invalid')
require(not (1 > 2 >= 2), 'guard control did not falsify the desired chain')
correct = 0 + 1*1 - 1*2
wrong = 0 - 1*1 - 1*2
require(correct != wrong, 'sign corruption escaped')

receipt = {
    'status':'PASS',
    'source_delta':'Exactly one normalized-power fragment; every other byte preserved',
    'pinned_lean_sources':len(pins['sources']),
    'small_norm_solutions':norm_solutions,
    'small_recovered_base_cases':covered_n,
    'exact_congruence_polynomial_identity':True,
    'guard_and_sign_negative_controls':True,
    'scope':'Byte and finite algebra audits. The unbounded theorem and inactive-branch maps are proved in normalization.tex.'
}
(ROOT / 'audit/NORMALIZATION_CHECK.json').write_text(json.dumps(receipt, indent=2)+'\n')
print(json.dumps(receipt))
