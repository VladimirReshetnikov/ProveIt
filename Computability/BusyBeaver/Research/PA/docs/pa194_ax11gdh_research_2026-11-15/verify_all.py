#!/usr/bin/env python3
"""Offline reconstruction and audit of the four new 194-state realizations.

Python standard library only. Use --full to rerun all independent symbolic
physical contracts. These checks supplement the explicit written theorem;
they do not claim to be a Lean proof of the PA calibration.
"""
from pathlib import Path
import argparse, concurrent.futures, hashlib, importlib.util, json
import subprocess, sys, tempfile, time

HERE=Path(__file__).resolve().parent
MACHINES={
 'H':HERE/'machine',
 'HS':HERE/'companions/HS/machine',
 'F':HERE/'companions/F/machine',
 'R':HERE/'companions/R/PA194AX11GDHR',
}
EXPECTED={
 'H':'c9a1e42ae042dd7592503f3a55dbb623859a70b2f240a2d4de2a1bacbefce880',
 'HS':'2d5b61572ee6e7dd19e23d7e10181c2f28410cddf0970fd145211c88ebca44cc',
 'F':'495be0f21e9aff11e35002a8909d94da1c0eaee92be37263db79f22f6c5567df',
 'R':'d9ff827eed1bb6a2b0d64cb17525a7613b2d1805eef788f3ac3ccd35b1738f5c',
}
def sha(path):return hashlib.sha256(path.read_bytes()).hexdigest()
def read(path):return json.loads(path.read_text())
def run(args,log):
 with log.open('w') as stream:
  proc=subprocess.run([sys.executable,'-B',*map(str,args)],stdout=stream,stderr=subprocess.STDOUT)
 if proc.returncode:raise RuntimeError(log.read_text()[-16000:])
def bound_receipt(path):
 rec=read(path/'independent/receipt.json')
 assert rec['status']=='PASS' and rec['states']==194 and rec['rows']==388
 assert rec['dense_sha256']==sha(path/'machine.tm')
 assert rec['native_sha256']==sha(path/'machine.native.tm')
 assert rec['contracts_sha256']==sha(path/'independent/contracts.json')
 ins=read(path/'instructions.json');contracts=read(path/'independent/contracts.json')
 expected={(i,b)for i,row in enumerate(ins)for b in([False,True]if row[0]=='dec'else[False])}
 actual={(c['site'],c['positive'])for c in contracts}
 assert expected==actual and len(contracts)==len(actual)==rec['source_outcomes']
 assert all(len(c['duration'])==13 and min(c['duration'])>=0 and c['duration'][0]>=3 for c in contracts)
 assert rec['list_lemmas_from_literal_table']==4 and not rec['box_oracles']
 assert len(read(path/'independent/list_lemmas.json'))==4
 return rec
def verify_one(key,temp,full):
 stored=MACHINES[key];assert sha(stored/'machine.tm')==EXPECTED[key]
 if key in ('H','HS'):
  root=HERE if key=='H' else HERE/'companions/HS'
  args=[root/'verify.py','--output',temp/f'{key}_construction.json']
  if full:args.append('--full')
  run(args,temp/f'{key}_construction.log')
  run([HERE/'source_binding.py','--machine',stored,'--variant',key,'--output',temp/f'{key}_binding'],temp/f'{key}_binding.log')
 else:
  out=temp/f'PA194AX11GDH{key}'
  if key=='F':args=[HERE/'build_fast.py','--parent',MACHINES['H'],'--output',out]
  else:args=[HERE/'companions/R/build_helper.py','--output',out]
  run(args,temp/f'{key}_construction.log')
  for name in ['machine.tm','machine.native.tm','nodes.json','grammar.json','instructions.json','sites.json']:
   assert (out/name).read_bytes()==(stored/name).read_bytes(),(key,name)
  assert read(out/'labels.json')==read(stored/'labels.json')
  if full:
   run([HERE/'independent/check.py',out],temp/f'{key}_literal.log')
   fresh=bound_receipt(out);prior=bound_receipt(stored)
   for field in ['states','rows','source_sites','source_outcomes','symbolic_steps','maximum_symbolic_steps','minimum_positive_duration_constant','startup_steps','dense_sha256','native_sha256','contracts_sha256']:
    assert fresh[field]==prior[field],(key,field)
 receipt=bound_receipt(stored)
 return dict(variant=key,status='PASS',dense_sha256=EXPECTED[key],source_sites=receipt['source_sites'],
             source_outcomes=receipt['source_outcomes'],startup_steps=receipt['startup_steps'],
             independent_symbolic_steps=receipt['symbolic_steps'],full_physical_replay=full)
def novelty():
 spec=importlib.util.spec_from_file_location('graph_novelty',HERE/'comparison/verify_novelty.py')
 mod=importlib.util.module_from_spec(spec);spec.loader.exec_module(mod)
 outcomes=[];parsed={k:mod.parse((v/'machine.tm').read_bytes())for k,v in MACHINES.items()}
 for key,path in MACHINES.items():
  r=mod.check(path/'machine.tm');assert not r['matches']
  outcomes.append({k:v for k,v in r.items()if k not in ('checks','candidate')})
 pairwise=[];keys=list(MACHINES)
 for i,key in enumerate(keys):
  rows,states=parsed[key]
  forms={mod.rooted(rows,states,q,m,f)[0]for q in states if mod.rooted(rows,states,q)[1]==194 for m in(False,True)for f in(False,True)}
  for other in keys[i+1:]:
   rr,ss=parsed[other];rep,n=mod.rooted(rr,ss,0);assert n==194 and rep not in forms,(key,other)
   pairwise.append(dict(left=key,right=other,distinct=True))
 return dict(status='PASS',reference_classes=521,reference_spanning_classes=520,comparisons=outcomes,pairwise=pairwise)
def main():
 assert __debug__,'Run without Python -O.'
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--full',action='store_true')
 ap.add_argument('--jobs',type=int,default=2);ap.add_argument('--output',type=Path)
 a=ap.parse_args();assert 1<=a.jobs<=4
 started=time.monotonic()
 with tempfile.TemporaryDirectory(prefix='pa194-four-realizations-')as raw:
  temp=Path(raw);results=[]
  with concurrent.futures.ThreadPoolExecutor(max_workers=a.jobs)as pool:
   futures={pool.submit(verify_one,key,temp,a.full):key for key in MACHINES}
   for future in concurrent.futures.as_completed(futures):
    result=future.result();results.append(result)
    print(json.dumps(result),flush=True)
  graph=novelty();print('Exact corpus and six pairwise graph comparisons: PASS',flush=True)
  result=dict(status='PASS',machines=sorted(results,key=lambda x:x['variant']),novelty=graph,
              full_physical_replay=a.full,seconds=round(time.monotonic()-started,3),
              scope='Offline construction, source binding, local certificates, exact blank frames and independent symbolic contracts. Absolute calibration is the separately cited written mathematical theorem; no completed Lean proof is claimed.')
  if a.output:
   a.output.parent.mkdir(parents=True,exist_ok=True);a.output.write_text(json.dumps(result,indent=2)+'\n')
  print(json.dumps(result,indent=2))
if __name__=='__main__':main()
