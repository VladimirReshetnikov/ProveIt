#!/usr/bin/env python3
"""Replay the portable finite source and deduction checks, without mutation."""
from pathlib import Path
import argparse,json,subprocess,sys,tempfile
P=Path(__file__).resolve().parent

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--out',type=Path);args=ap.parse_args()
 checks=[]
 with tempfile.TemporaryDirectory(prefix='pa-source-family-')as tmp:
  for mode in ([],['-O']):
   for script,receipt in [('verify_source_family.py','source_receipt.json'),('verify_source_graphs.py','source_graph_receipt.json'),('check_templates.py','template_receipt.json')]:
    dest=Path(tmp)/receipt
    completed=subprocess.run([sys.executable]+mode+[str(P/script),'--out',str(dest)],text=True,capture_output=True)
    if completed.returncode:raise RuntimeError(script+' failed:\n'+completed.stdout+completed.stderr)
    got=json.loads(dest.read_text());want=json.loads((P/receipt).read_text())
    if got!=want:raise ValueError(script+' receipt differs')
    checks.append({'checker':script,'optimized':bool(mode),'ok':True})
 result={'ok':True,'checks':checks,'scope':'Finite expression/stack, source CFG and deduction-template checks only. No sub-195 physical TM is certified here.'}
 if args.out:args.out.write_text(json.dumps(result,indent=2)+'\n')
 print(json.dumps(result,indent=2))
if __name__=='__main__':main()
