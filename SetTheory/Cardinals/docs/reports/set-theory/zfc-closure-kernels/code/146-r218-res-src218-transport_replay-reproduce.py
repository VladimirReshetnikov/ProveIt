#!/usr/bin/env python3
"""Replay the bounded tagged-transport search from pinned literal inputs."""
from pathlib import Path
import argparse,hashlib,json,re,subprocess,time
ROOT=Path(__file__).resolve().parent
ap=argparse.ArgumentParser();ap.add_argument('--output',type=Path,default=ROOT/'replay');ap.add_argument('--limit',type=int);args=ap.parse_args()
reference=json.loads((ROOT/'reference.json').read_text())
for name,want in reference['sha256'].items():
 assert hashlib.sha256((ROOT/name).read_bytes()).hexdigest()==want,name
args.output.mkdir(parents=True,exist_ok=True);exe=args.output/'transport_search'
subprocess.run(['g++','-O3','-std=c++17',str(ROOT/'portable/register_transport_tagged.cpp'),'-o',str(exe)],check=True)
results=[];begin=time.monotonic()
for index,task in enumerate(reference['tasks']):
 if args.limit is not None and index>=args.limit:break
 table,roles=reference['inputs'][task['input']];folder=args.output/f"{task['input']}_start{task['start']}";folder.mkdir(exist_ok=True)
 with(folder/'stdout.txt').open('w')as of,(folder/'stderr.txt').open('w')as ef:
  subprocess.run([str(exe.resolve()),str(ROOT/table),str(ROOT/roles),str(folder/'candidates'),str(reference['bound']),str(task['start'])],stdout=of,stderr=ef,check=True)
 line=(folder/'stderr.txt').read_text().splitlines()[-1];assert line.startswith('FINAL '),line
 found={k:int(v)for k,v in re.findall(r'(tried|feasible|hits|bounded|rays|cycles|totalsteps) ([0-9]+)',line)}
 assert found==task['expected'],(task,found)
 assert found['hits']==found['bounded']==0 and found['feasible']==found['rays']+found['cycles']
 results.append({'input':task['input'],'start':task['start'],'counts':found});print(task['input'],task['start'],'PASS',flush=True)
receipt={'status':'TAGGED_TRANSPORT_REPLAY_PASS'if len(results)==len(reference['tasks'])else'PARTIAL_TAGGED_TRANSPORT_REPLAY_PASS','completed_tasks':len(results),'expected_tasks':len(reference['tasks']),'initial_configurations':sum(x['counts']['feasible']for x in results),'seconds':time.monotonic()-begin,'results':results,'scope':'Literal negative startup search only. The generated register transports are not claimed to satisfy all primitive interfaces. Every included run closes by an exact cycle or blank-ray loop before the proof-search cap.'}
(args.output/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps({k:v for k,v in receipt.items()if k!='results'},indent=2))
