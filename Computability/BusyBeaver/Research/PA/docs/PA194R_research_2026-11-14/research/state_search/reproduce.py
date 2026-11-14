#!/usr/bin/env python3
"""Reproduce bounded searches without network access. Python3 and a C++17 compiler."""
from pathlib import Path
import argparse,hashlib,json,subprocess,time
HERE=Path(__file__).resolve().parent
p=argparse.ArgumentParser(description=__doc__)
p.add_argument('suite',choices=['positive','quotients','parameters','anneal','layouts'])
p.add_argument('--seconds',type=int,default=360,help='wall-time budget for each anneal')
p.add_argument('--compiler',default='g++')
p.add_argument('--output',type=Path,default=HERE/'replay')
a=p.parse_args();out=a.output.resolve();out.mkdir(parents=True,exist_ok=True);bins=out/'bin';bins.mkdir(exist_ok=True)
def compile(name):
 exe=bins/name
 subprocess.run([a.compiler,'-O3','-std=c++17',str(HERE/(name+'.cpp')),'-o',str(exe)],check=True)
 return exe
compiled={}
def run(name,args,prefix):
 if name not in compiled:compiled[name]=compile(name)
 t=time.monotonic()
 with (out/(prefix+'.stdout')).open('w') as so,(out/(prefix+'.stderr')).open('w') as se:
  subprocess.run([str(compiled[name]),*map(str,args)],stdout=so,stderr=se,check=True,cwd=HERE)
 print(json.dumps({'run':prefix,'seconds':round(time.monotonic()-t,3)}),flush=True)
 return out/(prefix+'.stdout')
for entry in json.loads((HERE/'input_manifest.json').read_text()):
 path=HERE/entry['file']
 assert hashlib.sha256(path.read_bytes()).hexdigest()==entry['sha256'],path
for entry in json.loads((HERE/'context_manifest.json').read_text()):
 assert hashlib.sha256((HERE/entry['file']).read_bytes()).hexdigest()==entry['sha256']
if a.suite=='positive':
 f=run('joint_return_merge',[HERE/'inputs/raw201.native.tm',4,60],'positive')
 hits=[json.loads(l)for l in f.read_text().splitlines()]
 found={tuple(sorted((h['remove'],h['keep'])))for h in hits}
 expected=json.loads((HERE/'joint_positive_control.receipt.json').read_text())['expected_pairs']
 assert all(tuple(pair)in found for pair in expected)
 print(json.dumps({'all_seven_known_fold_pairs_found':True,'row_pair_results':len(hits)}))
elif a.suite=='quotients':
 entries=json.loads((HERE/'input_manifest.json').read_text())
 for e in entries:
  if e['file'].endswith('raw201.native.tm'):continue
  path=HERE/e['file'];run('joint_return_merge',[path,6,200],path.stem+'_joint')
 for filename in ['e0a7397cf213.native.tm','CS_final_zero6.native.tm','CS_both_zero6.native.tm']:
  path=HERE/'inputs'/filename;run('joint_convergence',[path,4,100],path.stem+'_convergence')
 run('joint_encoded_convergence',[HERE/'inputs/CSZ.native.tm',4,100],'CSZ_encoded')
 for table,context in [('e0a7397cf213.native.tm','194_symbolic_patterns_k4.txt'),('b35d80b01ce9.native.tm','194C_symbolic_patterns_k4.txt')]:
  run('joint_return_merge',[HERE/'inputs'/table,4,200,HERE/'inputs'/context],table+'_symbolic')
elif a.suite=='parameters':
 for reg in [3,4,5,6]:
  run('parameter_screen',[HERE/'inputs'/f'parameterZ{reg}.txt',out/f'parameterZ{reg}',2,46656,'compatible'],f'parameterZ{reg}')
elif a.suite=='anneal':
 for reg in [3,4,5]:
  run('search_Z_multi',[HERE/'inputs'/f'seed194CSZZ{reg}_mixed.txt',HERE/'leaf_attrs_Z_multi.txt',out/f'final{reg}',a.seconds,2026111425+reg],f'final{reg}')

if a.suite=='layouts':
 run('layout_screen',[HERE/'inputs/seed194.txt'],'layouts')
