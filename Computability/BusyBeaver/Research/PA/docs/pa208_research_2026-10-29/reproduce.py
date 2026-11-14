#!/usr/bin/env python3
"""Recheck the accepted results; full symbolic replay is optional."""
from pathlib import Path
import argparse, hashlib, json, os, subprocess, sys, time, zipfile

ROOT=Path(__file__).resolve().parent
def require(ok,message):
    if not ok:raise ValueError(message)

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--full',action='store_true')
    p.add_argument('--finite',action='store_true')
    p.add_argument('--skip-manifest',action='store_true',help='For a deliberately edited research copy only')
    args=p.parse_args()
    require(__debug__,'Do not run under python -O: inherited checkers use assertions.')
    os.chdir(ROOT);started=time.monotonic()
    out=ROOT/'evidence/replay';out.mkdir(parents=True,exist_ok=True)
    if not args.skip_manifest:
        manifest=json.loads((ROOT/'MANIFEST.json').read_text())
        for item in manifest['files']:
            f=ROOT/item['path'];require(f.is_file(),f'Missing {f}')
            require(hashlib.sha256(f.read_bytes()).hexdigest()==item['sha256'],f'Changed {f}')
        print(f"PASS delivered hashes: {len(manifest['files'])} files",flush=True)
    pins=json.loads((ROOT/'sources_manifest.json').read_text())
    for item in pins['files']:
        path=ROOT/'upstream'/item['name'];data=path.read_bytes()
        digest=hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()
        require(len(data)==item['size'] and digest==item['git_blob_sha1'],f'Bad input {path.name}')
        if path.suffix=='.zip':
            dest=ROOT/'upstream'/path.stem
            with zipfile.ZipFile(path) as z:
                for member in z.infolist():
                    require((dest/member.filename).resolve().is_relative_to(dest.resolve()),'Unsafe archive path')
                z.extractall(dest)
    print('PASS pinned inputs; extracted to upstream/',flush=True)
    records=[]
    def run(label,argv,cwd=ROOT):
        t=time.monotonic()
        result=subprocess.run(argv,cwd=cwd,env=dict(os.environ,PYTHONDONTWRITEBYTECODE='1'),
                              capture_output=True,text=True)
        log=out/(label+'.log');log.write_text(result.stdout+result.stderr)
        record={'label':label,'returncode':result.returncode,'seconds':time.monotonic()-t,
                'log':str(log.relative_to(ROOT))};records.append(record)
        require(result.returncode==0,f'{label} failed; inspect {log}')
        print('PASS '+label,flush=True)
    py=[sys.executable,'-B']
    run('new_helper_proofs',py+['code/verify_helper_machines.py','--root',str(ROOT),
        '--output',str(out/'new_helpers.json')])
    run('original_graph_comparison',py+['analysis/comparison/compare_current.py'])
    comparison=json.loads((ROOT/'analysis/comparison/current_comparison.json').read_text())
    require(len(comparison['classes'])==2 and len(comparison['machines'])==9,'Original graph census changed')
    run('directional_reassociation',py+['code/check_directional.py'])
    run('source_zero_invariant',py+['analysis/reduction_search/no_mp_padding/prove_source_zero.py',
        '--certificate','analysis/reduction_search/no_mp_padding/source_zero_certificate.json'])
    run('mp_padding_splice',py+['analysis/reduction_search/remove_mp_padding.py'])
    run('direct_negation_six',py+['analysis/runtime_redesign/finalize_negation_all6.py'])
    if args.finite:
        executable=out/'finite_fast'
        run('compile_finite_screen',['g++','-O3','-std=c++17',
            'analysis/comparison/finite_fast.cpp','-o',str(executable)])
        helper=ROOT/'analysis/comparison/double_helper'
        for label in ('A','B'):
            for item in json.loads((helper/f'augmented_results_{label}.json').read_text()):
                d=ROOT/item['directory']
                run(d.name,[str(executable),str(d/'machine.native.tm'),str(d/'sites.tsv')])
    if args.full:
        research=ROOT/'upstream/u208_research_2026-10-29/u208_research_2026-10-29'
        run('full_original_runtime',py+['verify.py','--full','--output',str(out/'full_runtime.json')],research)
    summary={'status':'PASS','full_requested':args.full,'finite_requested':args.finite,
        'seconds':time.monotonic()-started,'checks':records,'sub208_candidate_established':False}
    (out/'summary.json').write_text(json.dumps(summary,indent=2)+'\n')
    print(json.dumps(summary,indent=2))

if __name__=='__main__':main()
