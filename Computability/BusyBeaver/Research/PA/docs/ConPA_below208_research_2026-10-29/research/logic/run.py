#!/usr/bin/env python3
"""Replay portable logical/source research; no external packages required."""
import argparse,hashlib,json,os,subprocess,sys,time
from pathlib import Path

HERE=Path(__file__).resolve().parent

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--output',type=Path,required=True)
    p.add_argument('--skip-orders',action='store_true')
    args=p.parse_args();out=args.output.resolve();out.mkdir(parents=True,exist_ok=True)
    env=dict(os.environ,LOGIC_RESEARCH_OUTPUT=str(out));started=time.monotonic();steps=[]
    for item in json.loads((HERE/'INPUT_MANIFEST.json').read_text())['inputs']:
        raw=(HERE/item['path']).read_bytes()
        if hashlib.sha256(raw).hexdigest()!=item['sha256']:
            raise ValueError('Input digest mismatch: '+item['path'])
    names=['collision_only','source_invariant','source_relational_invariant',
           'source_intervals','exhaust_axiom_permutations']
    if not args.skip_orders:names.append('row_order_search')
    for name in names:
        r=subprocess.run([sys.executable,str(HERE/(name+'.py'))],cwd=HERE,
                         env=env,capture_output=True,text=True)
        (out/(name+'.log')).write_text(r.stdout+r.stderr)
        if r.returncode:raise RuntimeError(name+' failed; inspect '+str(out/(name+'.log')))
        if name=='collision_only':
            c=json.loads(r.stdout);(out/'collision_only.json').write_text(json.dumps(c,indent=2)+'\n')
            if c!=json.loads((HERE/'evidence/collision_only.json').read_text()):
                raise ValueError('Collision certificate differs')
        steps.append(name);print('PASS',name,flush=True)
    relation=json.loads((out/'source_relational_invariant.json').read_text())
    if relation['reachable_abstract_configurations']!=278384 or len(relation['refined_cases'])!=1649:
        raise ValueError('Relational census differs')
    permutations=json.loads((out/'axiom_permutations_exhaustive/census.json').read_text())
    expected=json.loads((HERE/'evidence/axiom_permutations.json').read_text())
    for key in ('combinations','minimum_dag_nodes','minimizers','histogram','decomposition'):
        if permutations[key]!=expected[key]:raise ValueError('Permutation census differs: '+key)
    if not args.skip_orders:
        orders=json.loads((out/'row_orders/census.json').read_text())
        expected=json.loads((HERE/'evidence/row_order_census.json').read_text())
        for key in ('orders','best_dag','histogram','slot_counts'):
            if orders[key]!=expected[key]:raise ValueError('Row-order census differs: '+key)
    result={'status':'LOGICAL_SOURCE_RESEARCH_REPLAY_PASS','checks':steps,
            'accepted_new_machine':False,'seconds':time.monotonic()-started}
    (out/'replay.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))

if __name__=='__main__':main()
