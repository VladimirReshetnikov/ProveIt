#!/usr/bin/env python3
"""Portable replay of the selected226 extension, using the frozen227 toolkit."""
from pathlib import Path
import argparse,hashlib,json,re,subprocess,sys
H=Path(__file__).resolve().parent

def main():
 p=argparse.ArgumentParser(description=__doc__);p.add_argument('--base',type=Path,required=True,help='Frozen native227_evidence directory')
 p.add_argument('--output',type=Path,required=True);p.add_argument('--full',action='store_true');a=p.parse_args();a.output.mkdir(parents=True,exist_ok=True)
 for root in [H,a.base]:
  if(root/'SHA256SUMS').exists():
   for line in(root/'SHA256SUMS').read_text().splitlines():
    wanted,name=line.split('  ',1);assert hashlib.sha256((root/name).read_bytes()).hexdigest()==wanted,(root,name)
 def run(name,args):
  r=subprocess.run([str(x)for x in args],capture_output=True,text=True);(a.output/(name+'.log')).write_text(r.stdout+r.stderr)
  assert r.returncode==0,(name,r.stdout[-2000:],r.stderr[-2000:]);print(name,'PASS',flush=True);return r.stdout+r.stderr
 py=sys.executable
 run('construction',[py,H/'build.py','--base',a.base,'--output',a.output/'construction'])
 run('duplicate_quotient',[py,H/'verification/verify_duplicate.py',H/'controls/prequotient227_k230labels.tm',H/'controls/postquotient226_k230labels.tm','--output',a.output/'duplicate_quotient.json'])
 assert json.loads((a.output/'duplicate_quotient.json').read_text())==json.loads((H/'evidence/duplicate_quotient.json').read_text())
 run('scanner_counterexample',[py,H/'verification/replay_scanner_witness.py','--base',a.base,'--output',a.output/'scanner_witness.json'])
 assert json.loads((a.output/'scanner_witness.json').read_text())==json.loads((H/'rejected/scanner_witness.json').read_text())
 finite=a.output/'strict_profile';run('compile_finite',['g++','-std=c++17','-O3',a.base/'verification/strict_profile.cpp','-o',finite])
 log=run('finite_selected',[finite,H/'selected/k226_native.tm',H/'selected/sites.txt',a.output/'finite_profile.txt',a.base/'reference/boot_support.txt'])
 m=re.search(r'STRICT_FINITE_PASS instructions (\d+) cases_including_boot (\d+) steps (\d+) profile_pairs (\d+)',log)
 assert m and tuple(map(int,m.groups()))==(5121,26625,15414531,25671)
 cmd=[py,a.base/'verification/verify_k_protocol.py','--base',a.base/'runtime_dependency','--table',H/'selected/k226_native.tm','--sites',H/'selected/sites.json',
 '--reference',a.base/'reference/sites_H.json','--boot-reference',a.base/'reference/bootstrap_map.json','--output',a.output/'runtime226']
 if a.full:cmd.append('--full')
 run('selected_protocol',cmd)
 j=json.loads((a.output/'runtime226/verification.json').read_text());ref=json.loads((H/'evidence/runtime226/verification.json').read_text())
 keys=['working_states','transition_rows','table_sha256','canonical_sha256','sites_sha256','reference_sha256','engine_sha256','helper_sha256','source_leaf_occurrences','maximum_path_depth','exact_bootstrap_steps']
 if a.full:keys+=['cases','symbolic_steps','minimum_actual_steps','blocks','directly_used_rows','rows_outside_runtime_and_boot']
 for k in keys:assert j[k]==ref[k],k
 receipt={'status':'PORTABLE_NATIVE226_EXTENSION_REPLAY_PASS','full':a.full,'selected_protocol':j['status'],
 'quotient_old_rows_checked':454,'finite_instructions':5121,'finite_cases_including_boot':26625,'finite_literal_steps':15414531,'finite_context_pairs':25671}
 (a.output/'verification.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt,indent=2))
if __name__=='__main__':main()
