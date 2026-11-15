#!/usr/bin/env python3
"""Replay bounded research searches; these are not state-count lower bounds.

Python3 + C++17 are required. By default use the saved, hash-checked literal
context envelopes. --regenerate-contexts reconstructs them by symbolic literal
execution and includes startup. --fixed-rotations replays the separate fixed
source experiments, including the expected rejection of naive19/29.
"""
from pathlib import Path
import argparse,concurrent.futures,hashlib,json,shutil,subprocess,sys,time
ROOT=Path(__file__).resolve().parent
FAMILIES=['GD_SF','GDH_SF','GDHS_SF']
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def main():
 if not __debug__:raise SystemExit('Verification requires assertions; run without -O.')
 ap=argparse.ArgumentParser(description=__doc__)
 ap.add_argument('--output',type=Path,required=True)
 ap.add_argument('--regenerate-contexts',action='store_true')
 ap.add_argument('--fixed-rotations',action='store_true')
 a=ap.parse_args();out=a.output.resolve();out.mkdir(parents=True,exist_ok=True)
 if out==ROOT or ROOT in out.parents:raise SystemExit('Choose an output directory outside this research source directory.')
 manifest=json.loads((ROOT/'MANIFEST.json').read_text())
 for rel,digest in manifest.items():assert sha(ROOT/rel)==digest,rel
 front=ROOT/'frontier';started=time.monotonic()
 for name in ['joint_return_merge','stutter_merge_contexts','edge_delete_contexts']:
  subprocess.run(['g++','-O3','-std=c++17',str(front/(name+'.cpp')),'-o',str(out/name)],check=True)
 jobs=[]
 for family in FAMILIES:
  table=front/'inputs'/family/'machine.native.tm'
  context=front/(family+'_literal_contexts.tsv')
  if a.regenerate_contexts:
   context=out/(family+'_literal_contexts.tsv')
   with (out/(family+'_envelope.log')).open('w')as log:
    subprocess.run([sys.executable,'-B',str(front/'collect_literal_contexts.py'),str(table.parent),str(front/'reference'),str(context),'--radius','6'],check=True,stdout=log,stderr=subprocess.STDOUT)
   assert sha(context)==manifest['frontier/'+family+'_literal_contexts.tsv']
  for mode,suffix in [('coarse',[]),('literal',[context])]:
   for program,args in [('joint_return_merge',[table,6,100]),('stutter_merge_contexts',[table,6,12,128,74]),('edge_delete_contexts',[table,6,256,74,24])]:
    jobs.append((family,mode,program,args+suffix))
 def run(job):
  family,mode,program,args=job;label=family+'_'+mode+'_'+program
  with (out/(label+'.hits.jsonl')).open('w')as hit,(out/(label+'.log')).open('w')as log:
   subprocess.run([str(out/program),*map(str,args)],stdout=hit,stderr=log,check=True)
  hits=(out/(label+'.hits.jsonl')).read_text().splitlines()
  result={'family':family,'envelope':mode,'program':program,'hits':len(hits)}
  assert not hits,result
  if program=='edge_delete_contexts':assert sum(line.startswith('Q ')for line in(out/(label+'.log')).read_text().splitlines())==193
  else:assert 'DONE pairs 18721 'in(out/(label+'.log')).read_text()
  print(result,flush=True);return result
 with concurrent.futures.ThreadPoolExecutor(max_workers=3)as ex:results=list(ex.map(run,jobs))
 helper=ROOT/'helper_fold'
 subprocess.run(['g++','-O3','-std=c++17',str(helper/'helper_fold.cpp'),'-o',str(out/'helper_fold')],check=True)
 with (out/'helper_fold.hits.jsonl').open('w')as hit,(out/'helper_fold.log').open('w')as log:
  subprocess.run([str(out/'helper_fold'),str(helper/'parent_LCG.native.tm')],stdout=hit,stderr=log,check=True)
 assert not(out/'helper_fold.hits.jsonl').read_text().strip()
 assert 'trials 18318203 cases 256 hits 0'in(out/'helper_fold.log').read_text()
 if a.fixed_rotations:
  dst=out/'fixed_rotations';shutil.copytree(ROOT/'fixed_rotations',dst,dirs_exist_ok=True)
  for script in ['rotate_fixed.py','combine_fixed.py','reject_naive_rotation.py']:
   with(dst/(script+'.replay.log')).open('w')as log:subprocess.run([sys.executable,'-B',str(dst/script)],stdout=log,stderr=subprocess.STDOUT,check=True)
  combined=json.loads((dst/'fixed_combination_results.json').read_text());assert combined['compatible_subsets_checked']==2915 and not combined['hits']
 summary={'status':'PASS','searches':results,'helper_first_actions':772,'helper_joint_trials':18318203,'helper_contexts':256,'helper_hits':0,'envelopes_regenerated':a.regenerate_contexts,'fixed_source_replayed':a.fixed_rotations,'elapsed_seconds':time.monotonic()-started,'scope':'Explicit finite transformation families only; no universal minimality theorem.'}
 (out/'summary.json').write_text(json.dumps(summary,indent=2)+'\n');print(json.dumps(summary,indent=2))
if __name__=='__main__':main()
