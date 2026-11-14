#!/usr/bin/env python3
"""Replay delivered computational certificates; does not prove Con(PA) calibration."""
from pathlib import Path
import argparse,subprocess,sys,json,hashlib,time
ROOT=Path(__file__).resolve().parent

def main():
 p=argparse.ArgumentParser(description=__doc__);p.add_argument('--output',type=Path,required=True);a=p.parse_args()
 if not __debug__ or sys.flags.optimize:raise SystemExit('Run without -O/PYTHONOPTIMIZE.')
 out=a.output.resolve();out.mkdir(parents=True,exist_ok=True)
 checks=[]
 def run(name,args):
  start=time.time();r=subprocess.run([sys.executable,'-B']+[str(x)for x in args],cwd=ROOT,capture_output=True,text=True)
  (out/(name+'.log')).write_text(r.stdout+r.stderr)
  checks.append({'name':name,'exit_code':r.returncode,'seconds':time.time()-start,'log':name+'.log'})
  print(name,'PASS'if r.returncode==0 else'FAIL',flush=True)
  if r.returncode:raise RuntimeError(f'{name} failed; inspect {out/(name+".log")}')
 run('candidate',[ROOT/'candidate/verify.py','--receipt',out/'candidate.json'])
 run('source_macro_binding',[ROOT/'proof/build_macro_plan.py','--candidate',ROOT/'candidate','--output',out/'ax_macro_plan.json'])
 run('outside_ax_binding',[ROOT/'proof/check_outside_ax_rows.py','--primary',ROOT/'baseline/machine/instructions.json','--candidate',ROOT/'candidate/machine/instructions.json','--output',out/'outside_ax_binding.json'])
 run('primary',[ROOT/'baseline/verification/check_literal.py','--output',out/'primary'])
 run('novelty',[ROOT/'comparison/check_novelty.py',ROOT/'candidate/machine/machine.tm','--corpus',ROOT/'comparison/results/representatives','--output',out/'novelty.json'])
 run('restricted_exchange',[ROOT/'proof/check_restricted_exchange.py',ROOT/'proof/RestrictedImplication.lean','--out',out/'restricted_exchange'])
 run('rejected_core_startups',[ROOT/'research/runtime/check_startups.py','--output',out/'startups.json'])
 manifest=ROOT/'SHA256SUMS';checked=0
 if manifest.exists():
  for l in manifest.read_text().splitlines():
   digest,name=l.split('  ',1);f=ROOT/name
   if not f.is_file()or hashlib.sha256(f.read_bytes()).hexdigest()!=digest:raise AssertionError('Manifest mismatch: '+name)
   checked+=1
 report={'status':'PASS','candidate_sha256':hashlib.sha256((ROOT/'candidate/machine/machine.tm').read_bytes()).hexdigest(),'checks':checks,'manifest_files_checked':checked,'source_commit':'1c9524d8bf2e0a27b9a16ff622359927f536e663','states':194,'below194_established':False,'ipra_conpa_calibration_established':False,'proof_assistant_kernel_run':False,'scope':'Computational construction, source/literal contracts, explicit finite proof DAG, corpus novelty, and rejection certificates. The report gives separately stated mathematical arguments and the remaining calibration obligation.'}
 (out/'verification_summary.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2))
if __name__=='__main__':main()
