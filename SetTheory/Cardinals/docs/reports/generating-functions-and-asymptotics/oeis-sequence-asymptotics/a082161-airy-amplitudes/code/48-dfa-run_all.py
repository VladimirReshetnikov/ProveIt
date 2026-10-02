#!/usr/bin/env python3
"""Offline replay. Supplied inputs are immutable; new files go under output/."""
from pathlib import Path
import argparse,hashlib,json,shutil,subprocess,sys,time
root=Path(__file__).resolve().parent
ap=argparse.ArgumentParser();ap.add_argument('--pdf',action='store_true',help='also rebuild article using installed TeX');a=ap.parse_args()
manifest={}
for line in (root/'SHA256SUMS').read_text().splitlines():
 digest,name=line.split('  ',1);p=(root/name).resolve()
 if not p.is_relative_to(root) or not p.is_file():raise ValueError('invalid manifest path')
 manifest[name]=digest
 assert hashlib.sha256(p.read_bytes()).hexdigest()==digest,name
out=root/'output';work=out/'checks';work.mkdir(parents=True,exist_ok=True)
for p in (root/'code').glob('*.py'):shutil.copy2(p,work/p.name)
results={};started=time.time()
for name in ['check_exact.py','formal_dfa.py','independent_coefficient_audit.py','check_inverse.py']:
 t=time.time();r=subprocess.run([sys.executable,str(work/name)],cwd=work,text=True,capture_output=True)
 (work/(name+'.log')).write_text(r.stdout+r.stderr)
 if r.returncode:raise RuntimeError(name+' failed; inspect output/checks log')
 results[name]={'passed':True,'seconds':round(time.time()-t,3)}
 if name=='independent_coefficient_audit.py':(work/'independent-coefficient-audit.json').write_text(r.stdout)
exact=json.loads((work/'exact-checks.json').read_text())
assert exact['positive_renewal_cells']==5050 and exact['normalized_recurrence_checks']==5049 and exact['oeis_terms_matched']==20
import sympy as s
formal=json.loads((work/'formal-coefficients.json').read_text());audit=json.loads((work/'independent-coefficient-audit.json').read_text())
assert all(s.simplify(s.sympify(x)-s.sympify(y))==0 for x,y in zip(formal['logforward_n'],audit['logforward_n']))
# Exercise the configurable generator at a distinct lower depth.
r=subprocess.run([sys.executable,str(work/'formal_dfa.py'),'--order','4'],cwd=work,text=True,capture_output=True)
(work/'order4.log').write_text(r.stdout+r.stderr);assert r.returncode==0
low=json.loads((work/'formal-coefficients.json').read_text());assert len(low['logforward_n'])==1
assert s.simplify(s.sympify(low['logforward_n'][0])-s.sympify(formal['logforward_n'][0]))==0
(work/'order4-coefficients.json').write_text(json.dumps(low,indent=2));(work/'formal-coefficients.json').write_text(json.dumps(formal,indent=2))
if a.pdf:
 r=subprocess.run(['bash',str(root/'article'/'build_pdf.sh')],cwd=root,text=True,capture_output=True)
 (out/'pdf-build.log').write_text(r.stdout+r.stderr);assert r.returncode==0
for name,digest in manifest.items():assert hashlib.sha256((root/name).read_bytes()).hexdigest()==digest, 'modified input '+name
report={'status':'PASS','inputs_preserved':True,'manifest_files':len(manifest),'checks':results,'configurable_order4':True,'pdf_rebuilt':a.pdf,'seconds':round(time.time()-started,3),'limitations':'Finite checks supplement analytic proof; amplitude decimals and discrete thresholds are not certified.'}
(out/'replay-report.json').write_text(json.dumps(report,indent=2));print(json.dumps(report,indent=2))
