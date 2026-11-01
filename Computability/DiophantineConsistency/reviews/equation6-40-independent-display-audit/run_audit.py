#!/usr/bin/env python3
"""Run independent equation, generator, parser-control and PDF checks as one audit."""
from pathlib import Path
import hashlib,json,subprocess,sys
D=Path(__file__).resolve().parent;R=D.parents[3];P=R/'Computability/DiophantineConsistency';S=P/'research/adaptive-square-sums40'
H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
scripts=['audit.py','evaluate_samples.py','check_generator.py','check_verifier.py','check_pdf.py'];inputs=[Path(__file__).resolve(),*[D/n for n in scripts],P/'equation.tex',P/'equation6-40.tex',P/'equation6-40.pdf',P/'Lean/DiophantineConsistency/AdaptiveAQ40Literal.lean',*[S/n for n in ('candidate.json','equation6-40-display.tex','generate_equation6_40.py','verify_display6_40.py')]]
before={str(p):H(p) for p in inputs};rows=[]
for script,out in [('audit.py','exact.json'),('evaluate_samples.py','samples.log'),('check_generator.py','generator.json'),('check_verifier.py','verifier.json'),('check_pdf.py','pdf.json')]:
 proc=subprocess.run([sys.executable,str(D/script)],cwd=R,capture_output=True,text=True);assert proc.returncode==0,(script,proc.stdout,proc.stderr);assert not proc.stderr,(script,proc.stderr)
 (D/out).write_text(proc.stdout);rows.append({'script':script,'exit':proc.returncode,'output':out,'output_sha256':H(D/out)})
assert before=={str(p):H(p) for p in inputs}
report={'status':'PASS_INDEPENDENT_EQUATION6_40_AUDIT','inputs_sha256':before,'runs':rows,'scope':'Exact sparse-polynomial comparison of display with 40-variable candidate, both 160-gate presentations, parser controls and byte-identical PDF rebuild; historical proof ancestry and separate Con(ZFC) bridge are not checked.'}
(D/'receipt.json').write_text(json.dumps(report,indent=2,sort_keys=True)+'\n');print(report['status'],len(rows),'checks',H(D/'receipt.json'),flush=True)
