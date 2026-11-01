#!/usr/bin/env python3
"""Check the provisional status disclosure is present in the supplied TeX."""
from pathlib import Path
import hashlib,json,re
D=Path(__file__).resolve().parent;T=D.parents[1]/'equation6-31.tex';H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest();before={str(p.resolve()):H(p) for p in (Path(__file__).resolve(),T)};text=T.read_text();assert re.search(r'This equation is a candidate:\s*the reverse witness construction and native\s*intuitionistic PRA equivalence are not yet established\.',text);assert 'Lean proves that the formalized equation' not in text;assert {p:H(p) for p in before}==before
out={'status':'PASS_PROVISIONAL_SCOPE_DISCLOSURE','input_sha256':before,'scope':'Checks the document disclosure only; no reverse orientation or native equivalence proof.'};p=D/'candidate-scope-receipt.json';assert not p.exists();p.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n');print(out['status'],H(p))
