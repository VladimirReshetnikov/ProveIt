#!/usr/bin/env python3
"""Offline replay preserving every manifested input."""
from pathlib import Path
import argparse,hashlib,json,shutil,subprocess,sys,time
root=Path(__file__).resolve().parent
ap=argparse.ArgumentParser();ap.add_argument('--pdf',action='store_true');args=ap.parse_args()
manifest={}
for line in (root/'SHA256SUMS').read_text().splitlines():
 digest,name=line.split('  ',1);p=(root/name).resolve()
 assert p.is_relative_to(root) and p.is_file(),name
 assert hashlib.sha256(p.read_bytes()).hexdigest()==digest,name
 manifest[name]=digest
out=root/'output';work=out/'checks';work.mkdir(parents=True,exist_ok=True)
checks={};start=time.time()
for source,target in [('verify.py','verification.json'),('exact_checks.py','exact_checks.json'),('check_inverse_and_boundary.py','inverse-boundary-checks.json')]:
 shutil.copy2(root/'code'/source,work/source)
 t=time.time();r=subprocess.run([sys.executable,str(work/source)],cwd=work,text=True,capture_output=True)
 (work/(source+'.log')).write_text(r.stdout+r.stderr)
 assert r.returncode==0,source
 assert json.loads((work/target).read_text())==json.loads((root/'expected'/target).read_text()),target
 checks[source]={'passed':True,'expected_output_matched':True,'seconds':round(time.time()-t,3)}
if args.pdf:
 r=subprocess.run(['bash',str(root/'article'/'build_pdf.sh')],cwd=root,text=True,capture_output=True)
 (out/'pdf-build.log').write_text(r.stdout+r.stderr);assert r.returncode==0
for name,digest in manifest.items():assert hashlib.sha256((root/name).read_bytes()).hexdigest()==digest,name
report={'status':'PASS','inputs_preserved':True,'manifest_files':len(manifest),'checks':checks,'pdf_rebuilt':args.pdf,'seconds':round(time.time()-start,3)}
(out/'replay-report.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2))
