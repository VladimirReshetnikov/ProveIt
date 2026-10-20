#!/usr/bin/env python3
"""Portable replay of machine-side search methods; no <=218 construction claimed."""
from pathlib import Path
import argparse,hashlib,json,subprocess,sys,shutil
HERE=Path(__file__).resolve().parent
OUT=HERE/'output'
TABLE=HERE/'data/k219/machine/k219.native.tm'
SITES=HERE/'data/k219/machine/sites219.json'
PY=sys.executable

def run(args,key):
    with (OUT/(key+'.log')).open('w') as log:
        result=subprocess.run([str(x) for x in args],cwd=HERE,stdout=log,stderr=subprocess.STDOUT)
    tail=(OUT/(key+'.log')).read_text().splitlines()[-4:]
    print(json.dumps({'step':key,'returncode':result.returncode,'tail':tail}),flush=True)
    if result.returncode:raise SystemExit(result.returncode)
    return tail

def compile_cpp(name):
    compiler=shutil.which('c++') or shutil.which('g++') or shutil.which('clang++')
    if not compiler:raise SystemExit('A C++17 compiler is needed for this replay mode.')
    binary=OUT/name
    run([compiler,'-O3','-std=c++17',HERE/(name+'.cpp'),'-o',binary],'compile_'+name)
    return binary

def source_inputs(sites=SITES,tag='baseline'):
    prefix=OUT/(tag+'_classes')
    run([PY,HERE/'cfg_bisimulation.py',sites,prefix],tag+'_cfg')
    run([PY,HERE/'cfg_liveness.py',sites,prefix],tag+'_liveness')
    run([PY,HERE/'admissible_source.py',sites,OUT/(tag+'_admissible')],tag+'_admissible')
    rows=json.loads(sites.read_text())
    primitive=OUT/(tag+'_sites.in')
    primitive.write_text(''.join(f'{p} {o} {a if a is not None else -1}\n'for p,o,a in rows))
    return primitive,prefix.with_suffix('.in'),prefix.with_name(prefix.name+'_liveness').with_suffix('.in')

def verify_files():
    manifest=json.loads((HERE/'manifest.json').read_text())
    for item in manifest['files']:
        path=HERE/item['path']
        assert path.is_file(),('missing',item['path'])
        assert hashlib.sha256(path.read_bytes()).hexdigest()==item['sha256'],('hash',item['path'])
    assert hashlib.sha256(TABLE.read_bytes()).hexdigest()=='b255f8ee341d394c303d67a7fca7f8288ed9d4c40f075899fa64b13085aaca26'
    assert hashlib.sha256(SITES.read_bytes()).hexdigest()=='0f6d9d991e36dda1a7449edab72a799bb2d8c3de3ff853a26178b89bd1bc8789'
    return len(manifest['files'])

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--mode',choices=['quick','finite','local','equality','permutations','joint'],default='quick')
    parser.add_argument('--screen',choices=['finite_merge','finite_merge_general','weak_choice','bisim_choice','bisim_general','liveness_choice','liveness_general','finite_bypass','finite_merge_admissible'],default='bisim_general')
    parser.add_argument('--seed',choices=['baseline','nop','rho6','nop_rho6','row157','row160','both'],default='baseline')
    parser.add_argument('--local',choices=['fold5','fold7','diamond','double','bypass'],default='fold5')
    args=parser.parse_args();OUT.mkdir(exist_ok=True)
    count=verify_files();print(json.dumps({'manifest_files_verified':count,'mode':args.mode}),flush=True)
    if args.mode=='quick':
        source_inputs()
        compile_cpp('leaf_synth')
        run([PY,HERE/'compile_permutation.py','identity'],'permutation_identity')
        identity=json.loads((OUT/'permutations/summary.json').read_text())
        assert len(identity)==1 and identity[0]['states']==219
        assert identity[0]['table_sha256']==hashlib.sha256(TABLE.read_bytes()).hexdigest()
        report={'status':'PASS; source invariants and exact identity compilation replayed','candidate_status':'No <=218-state construction is established','manifest_files':count,'identity':identity[0],
                'cfg':{k:v for k,v in json.loads((OUT/'baseline_classes.json').read_text()).items()if k not in('site_classes','identity_closure')}}
        (OUT/'quick.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report),flush=True)
    elif args.mode=='finite':
        if args.seed=='baseline':table,sites=TABLE,SITES
        elif args.seed in('row157','row160','both'):table,sites=HERE/(args.seed+'.tm'),SITES
        else:table,sites=HERE/'data/seeds'/args.seed/'native.tm',HERE/'data/seeds'/args.seed/'sites.json'
        primitive,cfg,live=source_inputs(sites,args.seed)
        input_file=live if args.screen.startswith('liveness_') or args.screen=='finite_bypass' else cfg if args.screen.startswith('bisim_') else OUT/(args.seed+'_admissible.in') if args.screen=='finite_merge_admissible' else primitive
        exe=compile_cpp(args.screen)
        run([exe,table,input_file,OUT/(args.seed+'_'+args.screen+'.hits')],args.seed+'_'+args.screen)
    elif args.mode=='local':
        if args.local in('fold5','fold7'):
            radius=5 if args.local=='fold5'else 7
            run([PY,HERE/'search_folds.py',radius],args.local)
        else:
            radius=7 if args.local=='bypass'else 5
            sys.path.insert(0,str(HERE));import search_folds as sf
            path=OUT/f'invariant219_r{radius}.json'
            if not path.exists():path.write_text(json.dumps(sf.inv(radius)))
            name={'diamond':'search_diamonds','double':'search_double','bypass':'search_bypass'}[args.local]
            run([PY,HERE/(name+'.py'),radius],args.local)
    elif args.mode=='equality':
        run([PY,HERE/'compile_eq.py'],'compile_equalities')
        run([PY,HERE/'compile_left.py'],'compile_all_left')
        exe=compile_cpp('eq_left')
        for cost in(6,7):run([exe,HERE/'eqatoms.in',OUT/f'eq_left{cost}_nodes.txt',cost],f'eq_left{cost}')
    elif args.mode=='permutations':
        compile_cpp('leaf_synth')
        run([PY,HERE/'compile_permutation.py','all'],'permutation_all')
        run([PY,HERE/'permutation_matrix.py'],'permutation_matrix')
    elif args.mode=='joint':
        exe=compile_cpp('joint_source')
        run([exe,HERE/'joint_source.in',OUT/'joint219.facts',OUT/'equality_entry_patterns.txt',OUT/'equality_external_patterns.txt'],'joint_source')

if __name__=='__main__':main()
