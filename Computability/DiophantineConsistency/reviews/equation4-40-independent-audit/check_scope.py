#!/usr/bin/env python3
"""Check provisional status and reconstructed root and W bindings."""
from pathlib import Path
import hashlib,json,re
D=Path(__file__).resolve().parent;ROOT=D.parents[1];T=ROOT/'equation4-40.tex';C=ROOT/'research/adaptive-square-sums40-quotient-quartic/candidate.json';H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();inputs=[Path(__file__).resolve(),T,C];before={str(p):H(p) for p in inputs};t=T.read_text();c=json.loads(C.read_text())
assert re.search(r'This equation is a candidate:\s*the quotient witness construction and native\s*intuitionistic PRA equivalence are not yet established\.',t)
assert 'Lean proves that the formalized equation' not in t
assert 'firstQuotient' in c['witnesses'] and 'mainQuotient' in c['witnesses'] and 'psiSquareVariable' not in c['witnesses'] and 'varphiSquareVariable' not in c['witnesses']
assert c['source'][25]==['Bt','-','g27','g28'] and c['source'][97]==['wDifference','-','wValueVariable','Bt']
assert c['source'][113]==['zScaled','*','scaleVariable','firstQuotient'] and c['source'][114]==['zDifference','-','zScaled','ZComputed']
assert c['source'][116]==['dScaled','*','mainScaleVariable','mainQuotient'] and c['source'][117]==['dDifference','-','dScaled','DstarComputed']
assert r'Gates \texttt{zScaled, dScaled} are $Z=\psi z$ and $D=\varphi d$' in t
assert '26. WComputed = g27 - g28\\\\' in t and '98. wDifference = WNamed - WComputed\\\\' in t
assert r'input \texttt{WNamed} is the' in t and r'gate \texttt{WComputed} is $C(X+Kq)-Fq$' in t
assert {str(p):H(p) for p in inputs}==before
out={'status':'PASS_PROVISIONAL_SCOPE_AND_ALIASES','input_sha256':before,'scope':'Finite candidate and documented W and two reconstructed-root aliases only; model witness transport and native equivalence are outside this audit.'};p=D/'scope-receipt.json';assert not p.exists();p.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n');print(out['status'],H(p))
