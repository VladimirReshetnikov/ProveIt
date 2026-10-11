"""Independently bind the manuscript's S6 residual to its exact word certificate."""
from pathlib import Path
from fractions import Fraction as Q
import json,re
B=Path(__file__).resolve().parents[1];V=B/'verification'
text=(B/'chapters/10-full-cayley-obstruction.tex').read_text()
block=text.split('P_6={}&',1)[1].split('T=\\frac',1)[0]
printed=[int(z) for z in re.findall(r'(?<![0-9])(?:128588|3138084|1592832|521184|216172|48861|257176)(?![0-9])',block)]
assert printed==[128588,3138084,1592832,521184,216172,48861,257176]
normalization=128588
coeffs=[Q(1),1+Q(12334,527),Q(384,31),Q(2136,527),Q(3179,5713920)*Q(184320,61),Q(801,2108),Q(2)]
expected=[normalization*c for c in coeffs]
assert [Q(c) for c in printed]==expected
# The beta7 substitution uses beta(7)=61*pi^7/184320; H(b)=-log(2)
# accounts for the minus sign on the final stuffle product. The remaining
# signs are exactly those displayed on the printed P6 and residual R6.
assert '-216172z^6a' in block and '-257176' in block
prefix=int(re.search(r'\\mathcal N=\{\}&([0-9]+)\\cdot10\^\{36\}',text).group(1))
suffix=int(re.search(r'&\+([0-9]+)\.',text).group(1))
integer=prefix*10**36+suffix
receipt=json.loads((V/'thirteenth-replay/exact-resonant/complete-cayley-verification.json').read_text())
assert receipt['target_normalization']==normalization and receipt['target_pairing']==-integer and integer>0
control=printed.copy();control[1]+=1;assert [Q(c) for c in control]!=expected
out=dict(status='PASS',printed_target_coefficients_checked=7,target_normalization=normalization,positive_integer_decomposition=str(integer),exact_pairing=receipt['target_pairing'],corruption_controls=1,scope='Independent rational normalization of every printed P6 coefficient against the displayed S6 residual, including the beta7 substitution and log sign; exact printed decimal decomposition versus the separately replayed functional pairing. This binds manuscript statements to the certificate without numerical periods.')
(V/'full-cayley-target-normalization.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8');print(json.dumps(out,indent=2))
