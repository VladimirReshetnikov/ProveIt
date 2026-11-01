#!/usr/bin/env python3
"""Check displayed W and evaluator's WNamed/WComputed distinction."""
from pathlib import Path
import hashlib,json
D=Path(__file__).resolve().parent;ROOT=D.parents[1];T=ROOT/'equation4-44.tex';C=ROOT/'research/adaptive-square-sums44/candidate.json';H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest();before={str(p.resolve()):H(p) for p in (Path(__file__).resolve(),T,C)};c=json.loads(C.read_text());t=T.read_text();assert c['source'][25]==['Bt','-','g27','g28'] and c['source'][103]==['wDifference','-','wValueVariable','Bt'];assert '26. WComputed = g27 - g28\\\\' in t and '104. wDifference = WNamed - WComputed\\\\' in t;assert r'gate \texttt{WNamed} is the' in t and r'gate \texttt{WComputed} is $C(X+Kq)-Fq$' in t;assert {str(p):H(p) for p in before}==before
out={'status':'PASS_W_ALIAS_BINDING','input_sha256':before,'scope':'Exact documented and evaluated W aliases only.'};p=D/'w-alias-receipt.json';assert not p.exists();p.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n');print(out['status'],H(p))
