#!/usr/bin/env python3
"""Rebuild the two composites and audit every current194-state representative.

Python3.10+standardlibrary; no network by default. Work is copied into a
private temporary directory so frozen tables and receipts remain unchanged.
--lc additionally replays the inherited LC source/physical relative proof
certificates. This is not a proof-assistant kernel check of PA calibration.
"""
from pathlib import Path
import argparse,hashlib,json,shutil,subprocess,sys,tempfile
ROOT=Path(__file__).resolve().parent
FAMILIES=('PA194AX11H_SF','PA194LC_AX11H_SF')

def main():
 p=argparse.ArgumentParser(description=__doc__);p.add_argument('--output',type=Path,default=ROOT/'verification/inventory_composites');p.add_argument('--lc',action='store_true');a=p.parse_args()
 if not __debug__:raise RuntimeError('Assertions must be enabled; do not use -O.')
 out=a.output.resolve();out.mkdir(parents=True,exist_ok=True);stages=[];logs=[]
 def run(label,script,*args):
  print('Checking '+label,flush=True)
  r=subprocess.run([sys.executable,'-B',str(script),*map(str,args)],stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
  (out/(label+'.log')).write_text(r.stdout)
  logs.append(label+'\n'+r.stdout)
  if r.returncode:print(r.stdout);raise RuntimeError(label+' failed')
  stages.append({'stage':label,'exit_code':0})
 with tempfile.TemporaryDirectory(prefix='pa194-composite-replay-')as t:
  work=Path(t);shutil.copytree(ROOT/'composites',work/'composites',ignore=shutil.ignore_patterns('__pycache__','*.pyc'))
  (work/'comparison').mkdir();shutil.copytree(ROOT/'comparison/frontier194',work/'comparison/frontier194')
  run('construction',work/'composites/build_composites.py')
  matches=[]
  for family in FAMILIES:
   for name in('machine.tm','machine.native.tm','selector.native.tm','labels.json','construction.json'):
    old=ROOT/'composites/machines'/family/name;new=work/'composites/machines'/family/name
    assert old.read_bytes()==new.read_bytes(),family+'/'+name
    matches.append({'file':'composites/machines/'+family+'/'+name,'sha256':hashlib.sha256(new.read_bytes()).hexdigest()})
  run('literal_finite_premises',work/'composites/verify_composites.py')
  for family in FAMILIES:
   shutil.copy2(work/'composites/machines'/family/'verification.json',out/(family+'.json'))
  run('graph_novelty',work/'composites/check_novelty.py')
  shutil.copy2(work/'composites/novelty.json',out/'novelty.json')
 run('frozen_corpus_audit',ROOT/'comparison/audit.py','--output',out/'census.json')
 expected='93ee082ef035b2d32e71d6af5239b25b4bea1773f03bea4d2c39810a7fe15075'
 assert hashlib.sha256((ROOT/'references/ax11h_calibration.zip').read_bytes()).hexdigest()==expected
 if a.lc:
  run('lc_dependency',ROOT/'references/lc_ax11h/verify_all.py','--output',out/'lc_dependency')
 summary={'status':'PASS','reconstructed_core_files':matches,'stages':stages,'spanning_frontier_classes':139,'additional_nonspanning_diagnostic':1,'calibration_zip_sha256':expected,'inherited_LC_physical_replay_executed':a.lc,'kernel_checked':False,'absolute_arithmetic_derivation_checked_by_this_script':False,'proof_boundary':'Finite table hypotheses for the new direct relative iPRA proof; frozen corpus audit; exact inherited AX11H archive identity. The written absolute calibration is a separate mathematical dependency.'}
 (out/'summary.json').write_text(json.dumps(summary,indent=2)+'\n');(out/'verification.log').write_text('\n\n'.join(logs)+'\n')
 print(json.dumps({k:v for k,v in summary.items()if k!='reconstructed_core_files'},indent=2))
if __name__=='__main__':main()
