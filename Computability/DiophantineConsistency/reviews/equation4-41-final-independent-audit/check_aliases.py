#!/usr/bin/env python3
"""Check candidate disclosure and the reconstructed first-root aliases."""
from pathlib import Path
import hashlib,json,re
D=Path(__file__).resolve().parent;ROOT=D.parents[1];T=ROOT/'equation4-41.tex';C=ROOT/'research/adaptive-square-sums41-quartic/candidate.json';H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();inputs=[Path(__file__).resolve(),T,C];before={str(p):H(p) for p in inputs}; t=T.read_text();c=json.loads(C.read_text())
assert 'Lean proves that the formalized equation' in t
assert c['source'][25]==['Bt','-','g27','g28'] and c['source'][99]==['wDifference','-','wValueVariable','Bt']
assert '26. WComputed = g27 - g28\\\\' in t and '100. wDifference = WNamed - WComputed\\\\' in t
assert r'input \texttt{WNamed} is the' in t and r'gate \texttt{WComputed} is $C(X+Kq)-Fq$' in t
assert 'firstQuotient' in c['witnesses'] and 'psiSquareVariable' not in c['witnesses']
assert r'Gate \texttt{zScaled} is the abbreviation $Z=\psi z$' in t
assert {str(p):H(p) for p in inputs}==before
out={'status':'PASS_ALIAS_BINDING','input_sha256':before,'scope':'Documented W and first-root aliases only.'};p=D/'alias-receipt.json';assert not p.exists();p.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n');print(out['status'],H(p))
