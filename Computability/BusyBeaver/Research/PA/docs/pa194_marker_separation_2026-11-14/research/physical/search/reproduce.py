#!/usr/bin/env python3
"""Replay the scoped negative screens. Python 3.10+, C++17 compiler, no network.

Default: rerun source closures, then use the delivered exact window envelopes.
--regenerate: also reconstruct all symbolic envelopes from the source files.
Neither mode enumerates all 193-state machines.
"""
from pathlib import Path
import argparse,hashlib,json,re,subprocess,sys
HERE=Path(__file__).resolve().parent
ap=argparse.ArgumentParser(description=__doc__)
ap.add_argument('--output',type=Path,default=HERE/'reproduced')
ap.add_argument('--regenerate',action='store_true')
ap.add_argument('--compiler',default='g++')
args=ap.parse_args()
OUT=args.output.resolve();OUT.mkdir(parents=True,exist_ok=True)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
for rel,digest in json.loads((HERE/'manifest.json').read_text()).items():
 assert sha(HERE/rel)==digest,('input hash mismatch',rel)
def run(argv,name=None):
 print('Running',name or Path(str(argv[0])).name,flush=True)
 if name:
  with (OUT/(name+'.stdout')).open('w')as out,(OUT/(name+'.stderr')).open('w')as err:
   subprocess.run(list(map(str,argv)),stdout=out,stderr=err,check=True)
 else:subprocess.run(list(map(str,argv)),check=True)
run([sys.executable,HERE/'make_cfg.py',OUT/'lcg_cfg.txt'])
assert sha(OUT/'lcg_cfg.txt')==sha(HERE/'recorded/lcg_cfg.txt')
for source,exe in [('closure_marginals','closure'),('stutter_merge_contexts','stutter'),('edge_delete_contexts','edge_delete')]:
 run([args.compiler,'-O3','-std=c++17',HERE/'cpp'/f'{source}.cpp','-o',OUT/exe])
for radix in (3,4):
 filename='lcg_marginals.json' if radix==3 else 'lcg_marginals4.json'
 run([OUT/'closure',OUT/'lcg_cfg.txt',radix,OUT/filename],f'closure{radix}')
 assert sha(OUT/filename)==sha(HERE/'recorded'/filename)
run([sys.executable,HERE.parent/'build.py','--output',OUT/'machines'],'machines')
contexts={
 'parent':HERE/'input/parent_k6.tsv',
 'guarded':HERE/'recorded/guarded_k6.tsv',
 'guarded4':HERE/'recorded/guarded4_k6.tsv'}
if args.regenerate:
 for name,radix in [('parent',None),('guarded',3),('guarded4',4)]:
  script=HERE/('collect_parent_contexts.py' if radix is None else 'collect_guarded_contexts.py')
  argv=[sys.executable,script,HERE/'input',HERE/'reference',OUT/(name+'_k6.tsv'),'--radius',6]
  if radix:argv+=['--marginals',OUT/('lcg_marginals.json' if radix==3 else 'lcg_marginals4.json')]
  run(argv,'collect_'+name)
  assert sha(OUT/(name+'_k6.tsv'))==sha(contexts[name]),('regenerated envelope mismatch',name)
  contexts[name]=OUT/(name+'_k6.tsv')
summary=[]
for envelope in ('parent','guarded','guarded4'):
 transferred=OUT/(envelope+'_lcgms_k6.tsv')
 run([sys.executable,HERE/'transfer.py',contexts[envelope],transferred],envelope+'_transfer')
 expected=HERE/'recorded'/('parent_lcgms_k6.tsv' if envelope=='parent' else envelope+'_lcgms_k6.tsv')
 assert sha(transferred)==sha(expected)
 variants=('lcgms',)if envelope=='parent'else('lcg','lcgms')
 for variant in variants:
  key=envelope+'_'+variant
  table=HERE/'input/machine.native.tm'if variant=='lcg'else OUT/'machines/PA194LCGMS/machine.native.tm'
  windows=contexts[envelope]if variant=='lcg'else transferred
  run([OUT/'stutter',table,6,24,256,74,windows],key+'_stutter')
  run([OUT/'edge_delete',table,6,512,74,48,windows],key+'_edge_delete')
  assert not(OUT/(key+'_stutter.stdout')).read_text().strip(),('pair hit',key)
  assert not(OUT/(key+'_edge_delete.stdout')).read_text().strip(),('deletion hit',key)
  log=(OUT/(key+'_stutter.stderr')).read_text()
  match=re.search(r'DONE pairs (\d+) trials (\d+) combos (\d+) hits (\d+)',log)
  assert match and int(match[1])==18721 and int(match[4])==0
  deletions=(OUT/(key+'_edge_delete.stderr')).read_text().splitlines()
  assert len(deletions)==193
  summary.append(dict(name=key,windows=sum(1 for _ in windows.open()),pairs=int(match[1]),
                      action_trials=int(match[2]),joint_choices=int(match[3]),
                      deletion_targets=len(deletions),hits=0))
(OUT/'summary.json').write_text(json.dumps(summary,indent=2)+'\n')
print(json.dumps(summary,indent=2))
print('PASS: all recorded finite screens reproduced. No global optimality claim.')
