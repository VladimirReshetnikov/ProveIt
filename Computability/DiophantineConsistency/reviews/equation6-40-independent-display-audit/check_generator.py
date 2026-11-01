#!/usr/bin/env python3
"""Reproduce the checked TeX in an isolated copy, without writing to the workspace."""
from pathlib import Path
import hashlib,json,shutil,subprocess,sys,tempfile
D=Path(__file__).resolve().parent;R=D.parents[3];P=R/'Computability/DiophantineConsistency';S=P/'research/adaptive-square-sums40';H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
inputs=[P/'equation.tex',P/'equation6-40.tex',S/'candidate.json',S/'equation6-40-display.tex',S/'generate_equation6_40.py',S/'verify_display6_40.py'];before={str(x):H(x) for x in inputs}
with tempfile.TemporaryDirectory(prefix='equation6-generator-audit-') as t:
 base=Path(t)/'DiophantineConsistency';dest=base/'research/adaptive-square-sums40';dest.mkdir(parents=True)
 for n in ('candidate.json','equation6-40-display.tex','generate_equation6_40.py'):shutil.copyfile(S/n,dest/n)
 shutil.copyfile(P/'equation.tex',base/'equation.tex')
 run=subprocess.run([sys.executable,str(dest/'generate_equation6_40.py')],capture_output=True,text=True);assert run.returncode==0,(run.stdout,run.stderr)
 assert (base/'equation6-40.tex').read_bytes()==(P/'equation6-40.tex').read_bytes()
 assert before=={str(x):H(x) for x in inputs}
 print(json.dumps({'status':'PASS_ISOLATED_GENERATOR','inputs_sha256':before,'script_sha256':H(__file__),'scope':'Isolated generator reproduces the current TeX byte-for-byte; algebraic validation is separate.'},indent=2,sort_keys=True))
