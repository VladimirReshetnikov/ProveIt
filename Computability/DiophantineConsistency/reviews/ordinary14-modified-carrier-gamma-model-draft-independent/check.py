#!/usr/bin/env python3
"""Independent source and finite review; no Lean invocation."""
import hashlib
import json
from pathlib import Path
import subprocess
import sys

D = Path(__file__).resolve().parents[2]
A = D/'research/ordinary14-modified-carrier-gamma-model-draft'
def sha(data): return hashlib.sha256(data).hexdigest()
def pin(path, digest):
    data = path.read_bytes()
    assert sha(data) == digest, str(path)
    return data
source = pin(A/'CarrierGamma.lean','5d8dc10ca61726a6c2b939c2d98a784fb06b702348b15fa657badf7545984d3a').decode()
pin(A/'check_source.py','a12bb942a45e821bfb770d3a4cd89aaa2576a8fe9436442cb6ee28e7ebe6272c')
receipt = pin(A/'observation.json','abd2ab5e224189c22b3f8ad3bcb5f52a309b8a397d04faed8a7b1adfdd74759b')
readme = (A/'README.md').read_bytes()
tail = (b'\nIndependent source review is recorded in\n'
        b'`../../reviews/ordinary14-modified-carrier-gamma-model-draft-independent/`.\n')
assert readme.endswith(tail)
assert sha(readme[:-len(tail)]) == '4b604bab734125dc9cfcf0f30b3222b9327082ec0398edc097a747498a515955'
L = D/'Lean/DiophantineConsistency'
for name,digest in {
    'ArithmeticHalfBinomialSandwich.lean':'fd6b1c83162c7437e9db151273de060471b58d3260ba45a240d372a27e799c66',
    'ArithmeticPellPowerRecovery.lean':'636b64ce7d7625603b41412ec6acade846e82e64bef36e55cd09cc0f1e09e390',
    'ArithmeticPellRecurrence.lean':'63ec2a49f8d7066dbd8647a663db4bbd7255abd3ca7c3cc0d4d7b3533a189b16',
    'ArithmeticPow.lean':'3d52904ee9745edb76ddcf9540f563cbfd884178a8101bf9f96378a1fc119c76',
}.items(): pin(L/name,digest)
for fragment in ('(hR : 3≤R) (hXa : X≤a) (hwa : w≤a)',
                 'power_le_ycoord a (2:V)', '(ordinate_strictMono a).monotone hR',
                 'have h := x_gt a R', '(a+(4*a+3)*a)+(8*a+9)',
                 'mul_left_cancel₀ (ne_of_gt hU) (add_right_cancel hbal)',
                 'gamma_gt_from_carrier a X w R c d H gamma W hR hXa hwa hH hc hd he'):
    assert fragment in source, fragment
run = subprocess.run([sys.executable,'-I','-S','-B',str(A/'check_source.py')],
                     cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=120)
assert not run.stderr and run.stdout == receipt

def coords(a,R):
    # Independently use the two-coordinate matrix directly.
    d,c=1,0
    for _ in range(R):
        d,c=(a+2)*d+(a+1)*(a+3)*c, d+(a+2)*c
    return d,c
cases=0
for a in range(15):
    H=4*a+3
    for R in range(3,8):
        d,c=coords(a,R)
        assert c >= (2*a+3)**2 and d > (a+1)*c
        for X in range(a+1):
            for W in range(4):
                numerator=d+H*W-X-a*c
                if numerator<0 or numerator%H: continue
                gamma=numerator//H
                for w in range(a+1):
                    assert d+H*W==X+a*c+H*gamma
                    assert c>X+H*w and gamma>w
                    cases+=1
assert cases
a=4; H=4*a+3; d,c=coords(a,2); X=w=4; W=0; gamma=1
assert d+H*W==X+a*c+H*gamma and not w<gamma
print(json.dumps({'scope':'source and finite review only; no Lean',
                  'author_readme_prelink_sha256':sha(readme[:-len(tail)]),
                  'actual_balances':cases,'rank_two_counterexample':True},
                 sort_keys=True,indent=2))
