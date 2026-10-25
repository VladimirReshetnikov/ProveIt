#!/usr/bin/env python3
"""Run the portable exact checks for this fixed research packet."""
from pathlib import Path
import argparse, hashlib, json, os, subprocess, sys

ROOT=Path(__file__).resolve().parent

def need(ok,why):
    if not ok:raise ValueError(why)

def read(path):return json.loads(path.read_text())

def run(*args):
    cmd=[sys.executable,*(['-O'] if sys.flags.optimize else []),'-B',*map(str,args)]
    env=os.environ.copy();env['PYTHONDONTWRITEBYTECODE']='1'
    proc=subprocess.run(cmd,cwd=ROOT,env=env,text=True,stdout=subprocess.PIPE,stderr=subprocess.PIPE)
    if proc.returncode:raise RuntimeError('Check failed: '+' '.join(map(str,args))+'\n'+proc.stdout+'\n'+proc.stderr)
    return json.loads(proc.stdout)

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--rebuild',action='store_true');ap.add_argument('--receipt',type=Path)
    args=ap.parse_args()
    cert=run('certificate/verify.py',*(['--rebuild'] if args.rebuild else []))
    pool=run('code/independent_pool_check.py','--base','certificate','--parent','certificate/parent/strict_dimension')
    shears=run('code/independent_shear_check.py','--start','certificate/merged_aggregate_centered/equation.json',
               '--stage','equations/shear_stages/stage1','--stage','equations/shear_stages/stage2',
               '--stage','equations/shear_stages/stage3')
    generated=run('code/generate_principal.py','--check')
    principal=read(ROOT/'equations/principal/equation.json')
    terminal=read(ROOT/'equations/shear_stages/stage3/equation.json')
    need(principal['residuals']==terminal['residuals'],'Principal residuals differ from independently checked endpoint')
    need(principal['domain']=='unrestricted integers' and principal['polynomial']=='sum_of_squares','Principal domain or definition')
    need(len(principal['variables'])==260 and all(v['name']==f'z_{i+1}' and v['kind']=='unrestricted_integer'
        for i,v in enumerate(principal['variables'])),'Principal variable convention')
    histories=[]
    for k in (1,2,3):histories.extend(read(ROOT/f'equations/shear_stages/stage{k}/shears.json')['history'])
    need([{k:h[k] for k in ('i','j','k')} for h in histories]==read(ROOT/'equations/principal/shears.json')['history'],
         'Frozen principal shear certificate differs from independent stages')
    terms=lambda d:{tuple(m):c for c,m in d['terms']}
    need(terms(read(ROOT/'equations/principal/expanded_polynomial.json'))==
         terms(read(ROOT/'equations/shear_stages/stage3/expanded_polynomial.json')),'Principal expanded coefficients')
    out={'status':'PASS','python_optimization':sys.flags.optimize,'principal':generated['metrics'],
         'principal_generation':generated,'source_and_projection':cert,'independent_pool_check':pool,
         'independent_shear_check':shears,'final_interface_identity':True,
         'scope':'Exact finite arithmetic and artifact correspondence; unbounded mathematical proof and retained calibration are identified in the paper.'}
    if args.receipt:
        p=args.receipt if args.receipt.is_absolute() else ROOT/args.receipt
        p.parent.mkdir(parents=True,exist_ok=True);p.write_text(json.dumps(out,sort_keys=True,indent=2)+'\n')
    print(json.dumps({'status':'PASS','python_optimization':sys.flags.optimize,'principal':out['principal'],
                      'parent_files_authenticated':cert['parent_files_authenticated'],
                      'semantic_certificate_corruption_controls':sum(len(v) for v in cert['corruption_controls'].values()),
                      'coordinate_corruption_controls':len(shears['mutations']),
                      'byte_exact_rebuild':bool(args.rebuild)},sort_keys=True))

if __name__=='__main__':main()
