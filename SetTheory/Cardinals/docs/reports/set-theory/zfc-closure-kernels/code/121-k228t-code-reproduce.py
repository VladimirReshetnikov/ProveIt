#!/usr/bin/env python3
"""Reproduce the K228 construction, initialization, composition and runtime proof.

By default the universal K228 proof is recomputed. --quick instead checks the
recorded runtime evidence and repeats the short exact structural/startup proofs.
--baseline also reconstructs the K230 universal proof. No network is used.
"""
from pathlib import Path
import argparse,json,subprocess,sys,time
from check_recorded_evidence import check
from verify_manifest import verify


def main():
    if not __debug__ or sys.flags.optimize:
        raise RuntimeError('Run with assertions enabled; disable -O and PYTHONOPTIMIZE')
    package=Path(__file__).resolve().parent.parent
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--quick',action='store_true')
    ap.add_argument('--baseline',action='store_true')
    ap.add_argument('--output-dir',type=Path,default=package/'rerun')
    a=ap.parse_args()
    if a.quick and a.baseline:ap.error('--quick and --baseline have different verification scopes')
    a.output_dir=a.output_dir.resolve()
    begin=time.monotonic()
    a.output_dir.mkdir(parents=True,exist_ok=True)
    manifest_count=verify(package) if (package/'SHA256SUMS').exists() else None
    recorded=check(package)
    def run(name,*args):
        subprocess.run([sys.executable,'-B',str(package/'code'/name),*map(str,args)],check=True,cwd=package)
    run('build_k228.py','--check')
    run('check_startup.py','--table',package/'machines/k228_original_labels.tm','--output',a.output_dir/'startup_k228.json')
    run('check_startup_independent.py','--output',a.output_dir/'startup_independent.json')
    run('check_loop_fold.py','--output',a.output_dir/'loop_fold_local.json')
    runtime=package/'evidence/runtime_k228.json'
    if not a.quick:
        runtime=a.output_dir/'runtime_k228.json'
        run('verify_runtime.py','--table',package/'machines/k228_original_labels.tm',
            '--source',package/'machines/sites228.json','--output',runtime)
    if a.baseline:
        run('verify_runtime.py','--table',package/'inputs/k230.tm',
            '--source',package/'inputs/sites230_logical.json','--output',a.output_dir/'runtime_k230.json')
    run('check_composition.py','--package',package,'--runtime',runtime,
        '--boot',a.output_dir/'startup_k228.json','--output',a.output_dir/'composition.json')
    receipt=dict(status='PASS_QUICK_CHECKS_AND_RECORDED_RUNTIME' if a.quick else 'PASS_FULL_K228_REPRODUCTION',
                 universal_k228_recomputed=not a.quick,universal_k230_recomputed=a.baseline,
                 manifested_files_verified=manifest_count,recorded_runtime_identity=recorded,
                 seconds=time.monotonic()-begin,
                 scope='Ordinary mathematical verification; no Rocq compiler or kernel run')
    (a.output_dir/'reproduction.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps(receipt,indent=2),flush=True)


if __name__=='__main__':main()
