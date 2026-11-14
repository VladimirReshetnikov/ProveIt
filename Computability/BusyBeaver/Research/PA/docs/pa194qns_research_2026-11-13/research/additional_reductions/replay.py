#!/usr/bin/env python3
"""Replay completed bounded local searches; optional symbolic regeneration."""
from pathlib import Path
import argparse,json,shutil,subprocess,sys,tempfile
from check_invariants import check
ROOT=Path(__file__).resolve().parent
def main():
    ap=argparse.ArgumentParser();ap.add_argument('--collect',action='store_true');args=ap.parse_args()
    invariant=check()
    compiler=shutil.which('c++') or shutil.which('g++')
    if not compiler:raise SystemExit('A C++17 compiler is required.')
    results=[]
    with tempfile.TemporaryDirectory(prefix='pa-local-reduction-') as td:
        temp=Path(td)
        specs=[('generic_r8',8,'generic_k8.txt',4877),('abstract_r5',5,'abstract_k5.txt',4875)]
        if args.collect:
            for kind,radius,name,count in specs:
                target=temp/kind
                subprocess.run([sys.executable,'-B',str(ROOT/kind/'collect_contexts.py'),str(ROOT/'inputs/n6.native.tm'),str(ROOT/'inputs/sites.json'),'58320',str(target)],check=True)
                generated=target/f'patterns_k{radius}.txt'
                assert generated.read_bytes()==(ROOT/'inputs'/name).read_bytes()
                assert json.loads((target/'receipt.json').read_text())['source_outcomes']==count
        for name in ['action_merge_all_refined','edge_bypass_refined']:
            exe=temp/name
            subprocess.run([compiler,'-O3','-std=c++17',str(ROOT/(name+'.cpp')),'-o',str(exe)],check=True)
            operator_specs=specs+([('halt_aware_r5',5,'generic_k5.txt',4877)] if name=='action_merge_all_refined' else [])
            for kind,radius,patterns,count in operator_specs:
                run=subprocess.run([str(exe),str(ROOT/'inputs/n6.native.tm'),str(radius),'300',str(ROOT/'inputs'/patterns)],text=True,capture_output=True,check=True)
                assert not run.stdout.strip(),run.stdout
                results.append({'context_family':kind,'operator':name,'radius':radius,'step_bound':300,'candidate_count':0})
    print(json.dumps({'invariant':invariant,'results':results,'scope':'Finite failed searches; no global minimality result.'},indent=2))
if __name__=='__main__':main()
