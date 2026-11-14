#!/usr/bin/env python3
"""Replay the accepted constructions and exact obstruction offline.

Default: rebuild AX11QH5, check independent CFG/command identities, replay
both independent literal symbolic verifiers, check both tables against all
82 reference graphs, and replay the exact nine-trace startup obstruction.
The optional --quick omits only the two independent literal replays and the
construction oracle-based replay. Neither mode proves the missing iPRA
calibration or reruns time-bounded exploratory searches.
"""
from pathlib import Path
import argparse,hashlib,json,os,shutil,subprocess,sys,tempfile,time
ROOT=Path(__file__).resolve().parent
def sha(path):return hashlib.sha256(path.read_bytes()).hexdigest()
def main():
 p=argparse.ArgumentParser(description=__doc__)
 p.add_argument('--quick',action='store_true')
 p.add_argument('--receipt',type=Path)
 a=p.parse_args()
 if not __debug__ or sys.flags.optimize:raise SystemExit('Assertions must remain enabled; do not use Python -O.')
 manifest=ROOT/'MANIFEST.json';integrity=0
 if manifest.exists():
  for name,wanted in json.loads(manifest.read_text()).items():
   assert sha(ROOT/name)==wanted,('integrity mismatch',name)
   integrity+=1
 stages=[];start=time.monotonic()
 with tempfile.TemporaryDirectory(prefix='pa194-replay-')as td:
  tmp=Path(td)
  def run(name,script,*args):
   print(name,flush=True)
   env={**os.environ,'PYTHONDONTWRITEBYTECODE':'1'}
   proc=subprocess.run([sys.executable,'-B',str(script),*map(str,args)],cwd=ROOT,env=env,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
   (tmp/(name+'.log')).write_text(proc.stdout)
   if proc.returncode:
    print(proc.stdout);raise RuntimeError((name,proc.returncode))
   stages.append(name)
  new=tmp/'AX11QH5'
  run('AX11QH5_reconstruction',ROOT/'ax11qh5/construct.py','--output',new,*(['--quick']if a.quick else[]))
  for name in ['machine.tm','machine.native.tm','raw.native.tm','labels.json','nodes.json','grammar.json','folds.json','local_folds.json','sites.json','instructions.json']:
   assert (new/name).read_bytes()==(ROOT/'ax11qh5/AX11QH5'/name).read_bytes(),name
  run('AX11QH5_source_binding',ROOT/'ax11qh5/check_source_binding.py','--machine',new,'--output',tmp/'source_binding.json')
  run('AX11QH5_command_proof',ROOT/'ax11qh5/check_commands.py','--machine',new,'--output',tmp/'commands.json')
  if not a.quick:run('AX11QH5_literal_symbolic_replay',ROOT/'ax11qh5/qh5_reference/verification/check.py',new)
  hx=tmp/'hx194';shutil.copytree(ROOT/'hx194',hx)
  run('PA194HX_reconstruction',hx/'build.py')
  if not a.quick:run('PA194HX_literal_symbolic_replay',hx/'verify_literal.py')
  run('exact_graph_novelty',ROOT/'comparison/check_novelty.py','--reference-dir',ROOT/'comparison/representatives','--output',tmp/'novelty.json',new/'machine.tm',hx/'machine/pa194hx.tm')
  novelty=json.loads((tmp/'novelty.json').read_text())
  assert all(x['distinct_from_all_references'] and x['compared_reference_classes']==82 for x in novelty['results'])
  assert len({x['broad_cosmetic_fingerprint']for x in novelty['results']})==2
  core=tmp/'Runtime193';shutil.copytree(ROOT/'research/Runtime193',core)
  run('nine_trace_allocation_obstruction',core/'allocation193_obstruction.py')
  obstruction=json.loads((core/'evidence/allocation193_obstruction.json').read_text())
  assert obstruction['status']=='PASS'and obstruction['family_size']==362880 and len(obstruction['cases'])==9
  assert (core/'evidence/allocation193_obstruction.json').read_bytes()==(ROOT/'research/Runtime193/evidence/allocation193_obstruction.json').read_bytes()
  result={'status':'PASS','mode':'quick'if a.quick else'full','manifest_files_checked':integrity,'stages':stages,
   'table_hashes':{'AX11QH5':sha(new/'machine.tm'),'PA194HX':sha(hx/'machine/pa194hx.tm')},
   'exact_new_graph_classes':2,'reference_194_graphs':82,'runtime193_allocation_obstruction':{'allocations':362880,'traces':9,'prefix_lengths':[r['transitions']for r in obstruction['cases']]},
   'literal_replays_performed':not a.quick,'unconditional_ipra_calibration_proved':False,'elapsed_seconds':round(time.monotonic()-start,3)}
  if not a.quick:
   result['AX11QH5_literal']=json.loads((new/'independent/receipt.json').read_text())
   result['PA194HX_literal']=json.loads((hx/'evidence/hx_literal_receipt.json').read_text())
 if a.receipt:
  a.receipt.parent.mkdir(parents=True,exist_ok=True);a.receipt.write_text(json.dumps(result,indent=2)+'\n')
 print(json.dumps(result,indent=2))
if __name__=='__main__':main()
