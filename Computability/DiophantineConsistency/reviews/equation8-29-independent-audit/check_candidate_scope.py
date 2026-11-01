#!/usr/bin/env python3
"""Check candidate disclosure and the eliminated f-square binding."""
from pathlib import Path
import hashlib,json,re
D=Path(__file__).resolve().parent;ROOT=D.parents[1];T=ROOT/'equation8-29.tex';C=ROOT/'research/adaptive-square-sums29-degree8/candidate.json';H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();inputs=[Path(__file__).resolve(),T,C];before={str(p):H(p) for p in inputs};t=T.read_text();c=json.loads(C.read_text())
assert re.search(r'This equation is a candidate:\s*the model witness transport and native\s*intuitionistic PRA equivalence are not yet established\.',t)
assert 'Lean proves that the formalized equation' not in t
assert 'fSquareVariable' not in c['witnesses'] and ['f2','*','f','f'] in c['source']
assert r'gate \texttt{f2} is $m=f^2$' in t and '26. WComputed = g27 - g28\\\\' in t
assert {str(p):H(p) for p in inputs}==before
out={'status':'PASS_PROVISIONAL_SCOPE_AND_ALIASES','input_sha256':before,'scope':'Finite candidate and documented f-square and W aliases only; model witness transport and native equivalence are outside this audit.'};p=D/'scope-receipt.json';assert not p.exists();p.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n');print(out['status'],H(p))
