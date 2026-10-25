#!/usr/bin/env python3
"""Portable full coefficient audit and literal deterministic regeneration."""
import argparse,hashlib,json,subprocess,sys,tempfile
from pathlib import Path
HERE=Path(__file__).resolve().parent

def require(x,m):
 if not x:raise ValueError(m)
def child(mode,args):
 prefix=[sys.executable]+(['-O'] if mode=='optimized' else [])
 run=subprocess.run(prefix+[str(HERE/args[0])]+[str(x) for x in args[1:]],capture_output=True,text=True)
 require(run.returncode==0,'Child failure: '+' '.join(map(str,args))+'\n'+run.stdout+'\n'+run.stderr)
 return json.loads(run.stdout)
def main():
 p=argparse.ArgumentParser();p.add_argument('--mode',choices=['normal','optimized','both'],default='both');p.add_argument('--report',type=Path);p.add_argument('--skip-rebuild',action='store_true');a=p.parse_args()
 cfg=json.loads((HERE/'CONFIG.json').read_text());receipts=[];regenerated=[];source_hashes={}
 with tempfile.TemporaryDirectory(prefix='height-one-check-') as td:
  temp=Path(td)
  for mode in ['normal','optimized'] if a.mode=='both' else [a.mode]:
   for sid,src in cfg['sources'].items():
    original=HERE/src['original'];ref=HERE/src['refactored'];source_hashes[sid]=hashlib.sha256(original.read_bytes()).hexdigest()
    receipts.append({'mode':mode,'component':'affine_refactor_'+sid,'receipt':child(mode,['check_factor.py','--original',original,'--directory',ref])})
   for profile in cfg['profiles']:
    endpoint=HERE/'endpoints'/profile['name'];ref=HERE/cfg['sources'][profile['source']]['refactored'];stem=profile['name']+'_'+mode
    receipts.append({'mode':mode,'component':profile['name'],'receipt':child(mode,['check.py','--source',ref/'source.json','--artifact-dir',endpoint,'--mutations'])})
    receipts.append({'mode':mode,'component':profile['name']+'_independent','receipt':child(mode,['independent_audit.py','--source',ref/'source.json','--candidate',endpoint,'--output',temp/(stem+'.json')])})
   if not a.skip_rebuild:
    for sid,src in cfg['sources'].items():
     original=HERE/src['original'];ref=HERE/src['refactored'];f=temp/('source_'+sid+'_'+mode)
     child(mode,['factor_source.py','--source',original,'--out',f,'--selection',ref/'selection.json'])
     for name in ['source.json','factor_certificate.json']:
      require((f/name).read_bytes()==(ref/name).read_bytes(),'Refactor byte regeneration: '+name);regenerated.append(mode+'/refactored'+sid+'/'+name)
    for profile in cfg['profiles']:
     f=temp/('source_'+profile['source']+'_'+mode);out=temp/(profile['name']+'_'+mode)
     child(mode,['contract.py','--source',f/'source.json','--out',out,'--hubs',profile['hubs'],'--seed',profile['seed'],'--rounds',profile['rounds']])
     expected=HERE/'endpoints'/profile['name']
     for name in ['polynomial.json','certificate.json','metrics.json']:
      require((out/name).read_bytes()==(expected/name).read_bytes(),'Endpoint byte regeneration: '+profile['name']+'/'+name);regenerated.append(mode+'/'+profile['name']+'/'+name)
  from literal import render
  for profile in cfg['profiles']:
   endpoint=HERE/'endpoints'/profile['name'];require(render(json.loads((endpoint/'polynomial.json').read_text()))==(endpoint/'polynomial.txt').read_text(),'Literal polynomial rendering')
 result={'status':'pass','mode':a.mode,'checks':receipts,'byte_identical_regeneration':regenerated,'literal_equations_checked':len(cfg['profiles']),'source_sha256':source_hashes,'scope':'Exact finite algebra and deterministic artifact reproduction; unbounded zero-set proof is in report/proof_body.tex, source consistency calibration is supplied by the enclosing direct-source package.'}
 text=json.dumps(result,sort_keys=True,indent=2)+'\n'
 if a.report:a.report.parent.mkdir(parents=True,exist_ok=True);a.report.write_text(text)
 print(text,end='')
if __name__=='__main__':main()
