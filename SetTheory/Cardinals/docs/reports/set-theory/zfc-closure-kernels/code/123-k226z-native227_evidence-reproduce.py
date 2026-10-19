#!/usr/bin/env python3
"""Portable reconstruction, source, startup, block and optional universal replay."""
from pathlib import Path
import argparse,hashlib,json,re,subprocess,sys
H=Path(__file__).resolve().parent

def main():
 p=argparse.ArgumentParser(description=__doc__);p.add_argument('--output',type=Path,required=True)
 p.add_argument('--full',action='store_true',help='Reprove every selected native instruction and every H delayed-erasure guard')
 a=p.parse_args();a.output.mkdir(parents=True,exist_ok=True)
 manifest=H/'SHA256SUMS'
 if manifest.exists():
  for line in manifest.read_text().splitlines():
   wanted,name=line.split('  ',1);assert hashlib.sha256((H/name).read_bytes()).hexdigest()==wanted,name
 results={}
 def run(name,args):
  r=subprocess.run([str(x) for x in args],capture_output=True,text=True)
  (a.output/(name+'.log')).write_text(r.stdout+r.stderr)
  assert r.returncode==0,(name,r.returncode,r.stdout[-2000:],r.stderr[-2000:])
  print(name,'PASS',flush=True);return r.stdout+r.stderr
 py=sys.executable
 run('construction',[py,H/'build.py','--output',a.output/'construction'])
 specs=[('direct229','k230_native.tm','k229_native.tm','delayed_blocks.json'),
        ('H_delayed','k229_H_native.tm','k228_H_native.tm','H_delayed_blocks.json')]
 for name,old,new,reference in specs:
  target=a.output/(name+'.json')
  run(name,[py,H/'verification/verify_delayed_fold.py',H/'controls'/old,H/'controls'/new,target])
  assert json.loads(target.read_text())==json.loads((H/'evidence'/reference).read_text())
  results[name]=json.loads(target.read_text())['status']
 target=a.output/'H_fold_blocks.json'
 run('H_native_fold',[py,H/'verification/verify_state_fold.py',H/'controls/k230_H_native.tm',H/'controls/k229_H_native.tm','--keep',72,'--drop',90,'--output',target])
 assert json.loads(target.read_text())==json.loads((H/'evidence/H_fold_blocks.json').read_text())
 run('H_source',[py,H/'verification/independent_h_source.py','--k230-sites',H/'reference/sites230_original.json','--h-sites',H/'reference/sites_H.json','--output',a.output/'H_source.json'])
 run('scanner_counterexample',[py,H/'verification/replay_scanner_witness.py','--output',a.output/'scanner_witness.json'])
 assert json.loads((a.output/'scanner_witness.json').read_text())==json.loads((H/'rejected/scanner_witness.json').read_text())
 finite=a.output/'strict_profile'
 run('compile_finite',['g++','-std=c++17','-O3',H/'verification/strict_profile.cpp','-o',finite])
 log=run('finite_selected',[finite,H/'selected/k227_native.tm',H/'selected/sites.txt',a.output/'finite_profile.txt',H/'reference/boot_support.txt'])
 match=re.search(r'STRICT_FINITE_PASS instructions (\d+) cases_including_boot (\d+) steps (\d+) profile_pairs (\d+)',log)
 assert match and tuple(map(int,match.groups()))==(5121,26625,15422675,26151)
 results['finite']={'instructions':5121,'cases_including_boot':26625,'literal_steps':15422675,'profile_context_pairs':26151}
 cmd=[py,H/'verification/verify_k_protocol.py','--base',H/'runtime_dependency','--table',H/'selected/k227_native.tm',
 '--sites',H/'selected/sites.json','--reference',H/'reference/sites_H.json','--boot-reference',H/'reference/bootstrap_map.json','--output',a.output/'runtime227']
 if a.full:cmd.append('--full')
 run('selected_protocol',cmd)
 selected=json.loads((a.output/'runtime227/verification.json').read_text());results['selected_protocol']=selected['status']
 ref=json.loads((H/'evidence/runtime227/verification.json').read_text())
 for key in ['working_states','transition_rows','table_sha256','canonical_sha256','sites_sha256','reference_sha256','engine_sha256','helper_sha256','source_leaf_occurrences','maximum_path_depth','exact_bootstrap_steps']:
  assert selected[key]==ref[key],key
 if a.full:
  for key in ['cases','symbolic_steps','minimum_actual_steps','blocks','directly_used_rows','rows_outside_runtime_and_boot']:
   assert selected[key]==ref[key],key
  target=a.output/'H_guard169_evidence.json'
  run('H_universal_guard',[py,H/'verification/verify_guard169_evidence.py','--engine',H/'engine','--table',H/'controls/k229_H_native.tm','--sites',H/'reference/sites_H.json','--output',target])
  actual=json.loads(target.read_text());expected=json.loads((H/'evidence/H_guard169_evidence.json').read_text())
  assert {k:v for k,v in actual.items() if k!='seconds'}=={k:v for k,v in expected.items() if k!='seconds'}
  results['H_universal_guard']=actual['status']
 results.update(status='PORTABLE_NATIVE227_REPLAY_PASS',full=a.full)
 (a.output/'verification.json').write_text(json.dumps(results,indent=2)+'\n')
 print(json.dumps(results,indent=2))
if __name__=='__main__':main()
