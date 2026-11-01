#!/usr/bin/env python3
"""Rerun the shipped verifier and independently reproduce both negative controls."""
from pathlib import Path
import contextlib,hashlib,io,json,runpy
D=Path(__file__).resolve().parent;R=D.parents[3];P=R/'Computability/DiophantineConsistency';V=P/'research/adaptive-square-sums47/verify_display4_47.py';H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
files=[V,P/'equation4-47.tex'];before={str(p):H(p) for p in files}
with contextlib.redirect_stdout(io.StringIO()):d=runpy.run_path(str(V))
s=(P/'equation4-47.tex').read_text()
for label,old,new in [('bare_alias',r'\mathcal{P}^2','resA^2'),('outside_term',r'\begin{split}',r'1+\begin{split}')]:
 t=s.replace(old,new,1);assert t!=s
 try:d['validate'](t)
 except ValueError:pass
 else:raise AssertionError(('verifier accepted mutation',label))
assert before=={str(p):H(p) for p in files}
print(json.dumps({'status':'PASS_VERIFIER_NEGATIVE_CONTROLS','inputs_sha256':before,'script_sha256':H(__file__),'rejected':['bare_alias','outside_term'],'scope':'Tests two specific verifier controls; it is not an exhaustive parser proof.'},indent=2,sort_keys=True))
