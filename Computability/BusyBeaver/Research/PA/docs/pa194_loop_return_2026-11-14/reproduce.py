#!/usr/bin/env python3
"""Portable reconstruction and verification of the delivered194-state tables.
--full also regenerates every independent literal-tape source contract.
"""
from pathlib import Path
import argparse,hashlib,importlib.util,json,subprocess,sys,tempfile
ROOT=Path(__file__).resolve().parent

def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def run(args):subprocess.run([sys.executable,'-B']+[str(a)for a in args],cwd=ROOT,check=True)
def load(name,path):
 spec=importlib.util.spec_from_file_location(name,path);m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m);return m

def main():
 assert __debug__ and not sys.flags.optimize,'Do not use -O.'
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--full',action='store_true');ap.add_argument('--out',type=Path);a=ap.parse_args()
 out=(a.out.resolve() if a.out else Path(tempfile.mkdtemp(prefix='pa194-lcg-replay-')));out.mkdir(parents=True,exist_ok=True)
 manifest=json.loads((ROOT/'MANIFEST.sha256.json').read_text())
 for p,digest in manifest.items():assert sha(ROOT/p)==digest,p
 builder=load('release_builder',ROOT/'build.py')
 constructions=[]
 for name in builder.FAMILIES:
  receipt=builder.build(name,out/'machines',full=True);constructions.append(receipt)
  for file in ['machine.tm','machine.native.tm','labels.json','sites.json','instructions.json','loop_parent.native.tm']:
   assert (out/'machines'/name/file).read_bytes()==(ROOT/'machines'/name/file).read_bytes(),(name,file)
  assert sha(ROOT/'comparison/candidates'/(name+'.tm'))==sha(ROOT/'machines'/name/'machine.tm')
 if a.full:
  for name in builder.FAMILIES:
   run([ROOT/'verification/check_literal.py',out/'machines'/name,'--output',out/'independent'])
   fresh=json.loads((out/'independent'/name/'receipt.json').read_text());saved=json.loads((ROOT/'verification/results'/name/'receipt.json').read_text())
   for key in ['contracts_sha256','dense_sha256','native_sha256','source_outcomes','startup_steps']:
    assert fresh[key]==saved[key],(name,key)
 # Isolate the independent engine from the construction-side module with
 # the same historical Python name, symbolic_runtime.
 run([ROOT/'verification/physical_ipra_audit.py','--bundle',ROOT,'--output',out/'physical_audit.json'])
 clocks=load('release_clock_audit',ROOT/'verification/check_clocks.py').check(out/'clock_audit.json')
 run([ROOT/'comparison/verify_novelty.py','--output',out/'novelty.json'])
 summary={'status':'PASS','machines':list(builder.FAMILIES),'full_independent_contract_replay':a.full,
  'all_parent_child_duration_contracts_checked':sum(m['contracts']for m in clocks['machines']),
  'source_preserved':True,'startup_and_all_local_premises_replayed':True,'artifact_manifest_verified':True,
  'scope':'Finite bindings and new relative-theorem premises; not a proof-assistant or full inherited PA-calibration check.'}
 (out/'summary.json').write_text(json.dumps(summary,indent=2)+'\n');print(json.dumps(summary,indent=2));print('Replay directory:',out)
if __name__=='__main__':main()
