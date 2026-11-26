#!/usr/bin/env python3
"""Run all finite certificate checks; optionally build the PDF with --pdf."""
from pathlib import Path
import argparse,json,subprocess,sys
base=Path(__file__).resolve().parents[1]
p=argparse.ArgumentParser(description=__doc__)
p.add_argument('--pdf',action='store_true')
a=p.parse_args()
results=[]
for name in ['check_frames.py','check_algebra.py','check_source_manifest.py']:
    r=subprocess.run([sys.executable,str(base/'code'/name)],cwd=base,
                     check=True,text=True,capture_output=True)
    results.append({'script':name,'exit_code':r.returncode,'output':json.loads(r.stdout)})
if a.pdf:
    subprocess.run([sys.executable,str(base/'code/build_pdf.py')],cwd=base,check=True)
out={'status':'passed','checks':results,
     'not_performed':['upstream Lean build','kernel replay','new nonabelian GRH proof']}
(base/'certificates/validation_summary.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
