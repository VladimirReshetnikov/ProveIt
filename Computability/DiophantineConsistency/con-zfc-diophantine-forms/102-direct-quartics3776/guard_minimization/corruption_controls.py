#!/usr/bin/env python3
"""Adversarial controls for the guard certificate checker."""
from pathlib import Path
from copy import deepcopy
import json,shutil,subprocess,sys,tempfile

HERE=Path(__file__).resolve().parent

def fractional_bound(d):d['bound_derivations'][0]['lower_bound']=0.5
def bad_symmetry(d):
    generator=next(g for g in d['sign_symmetries'] if len(g['flip_variables'])==3)
    generator['flip_variables']=generator['flip_variables'][:-1]
def absent_step(d):del d['bound_derivations'][0]
def bad_core(d):d['residuals'][0]['terms'][0][0]+=1
def bad_expansion(d):d['terms'][0][0]+=1
def wrong_domain(d):d['domain']='nonnegative integers'

def main():
    controls=[('fractional_bound','guard_certificate.json',fractional_bound),
              ('broken_sign_symmetry','guard_certificate.json',bad_symmetry),
              ('deleted_derivation','guard_certificate.json',absent_step),
              ('changed_core_coefficient','equation.json',bad_core),
              ('changed_expansion_coefficient','expanded_polynomial.json',bad_expansion),
              ('changed_domain','equation.json',wrong_domain)]
    results=[]
    for optimized in (False,True):
        for name,filename,mutate in controls:
            with tempfile.TemporaryDirectory(prefix='guard-certificate-control-') as tmp:
                target=Path(tmp)
                for p in (HERE/'candidate').glob('*.json'):shutil.copyfile(p,target/p.name)
                p=target/filename;data=json.loads(p.read_text());mutate(data);p.write_text(json.dumps(data))
                cmd=[sys.executable]+(['-O'] if optimized else [])+[str(HERE/'check.py'),'--candidate',str(target)]
                completed=subprocess.run(cmd,stdout=subprocess.PIPE,stderr=subprocess.PIPE,text=True)
                if completed.returncode==0:raise ValueError(f'accepted corruption: {name}/{optimized}')
                results.append({'control':name,'optimized':optimized,'rejected':True,
                                'reason':completed.stderr.strip().splitlines()[-1]})
    print(json.dumps({'status':'PASS','rejected_controls':len(results),'results':results},sort_keys=True,indent=2))

if __name__=='__main__':main()
