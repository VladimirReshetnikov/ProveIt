#!/usr/bin/env python3
"""Offline independent checks for the new four-base polynomial circuits."""
import json,importlib.util,pathlib,sys,argparse,copy
ROOT=pathlib.Path(__file__).resolve().parent
def module(name,p):
 s=importlib.util.spec_from_file_location(name,p);m=importlib.util.module_from_spec(s);s.loader.exec_module(m);return m
def load(p):return json.loads(p.read_bytes())
def main():
 a=argparse.ArgumentParser();a.add_argument('--receipt',type=pathlib.Path);args=a.parse_args()
 poolcheck=module('independent_pool',ROOT/'code/verify_pooling.py')
 checker=module('independent_projection',ROOT/'inherited/verify_projections_original.py')
 checker.WEIGHTS={'staged':[([0,1],'base'),([2,3],'one')],'all4':[([0,1,2,3],'base')]}
 pool_results=[poolcheck.check(v)for v in ['staged','all4']];results=[]
 for cp in sorted((ROOT/'certificates').glob('*.json')):
  profile=load(cp);v=profile['variant'];raw=(ROOT/'sources'/v/'equation.json').read_bytes();pool=load(ROOT/'sources'/v/'certificate.json');art=load(ROOT/'equations'/cp.name)
  answer=checker.verify(raw,pool,profile,art,cp.stem);answer['corruption_controls']=checker.corruption_checks(raw,pool,profile,art,cp.stem);results.append(answer)
 receipt={'status':'PASS','scope':'Exact finite coefficient identities, acyclic integer-polynomial restoration, degree and liveness. Unbounded arithmetic calibration is a separate ordinary proof.','pooling':pool_results,'profiles':results}
 if args.receipt:args.receipt.parent.mkdir(parents=True,exist_ok=True);args.receipt.write_text(json.dumps(receipt,sort_keys=True,indent=2)+'\n')
 print(json.dumps({'status':'PASS','pooling':pool_results,'profiles':[{k:v for k,v in o.items()if k not in('variable_occurrence','corruption_controls')}for o in results],'corruptions_rejected':sum(len(o['corruption_controls'])for o in results)},indent=2))
if __name__=='__main__':main()
