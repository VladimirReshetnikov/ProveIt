#!/usr/bin/env python3
"""Offline reconstruction and proof replay of the exact 222-state machine.

The default freshly rederives all 5,956 unbounded runtime cases. --quick
instead checks the stored case file's hash, coverage and positive durations.
Neither mode rebuilds the inherited K230/K224 proof-assistant development.
Python 3.10+ standard library, with assertions enabled; no network required.
"""
from pathlib import Path
import argparse, hashlib, json, os, shutil, subprocess, sys, time

ROOT=Path(__file__).resolve().parent
def need(ok,message):
    if not ok:raise ValueError(message)
def sha(path):return hashlib.sha256(Path(path).read_bytes()).hexdigest()
def dump(path,data):Path(path).write_text(json.dumps(data,indent=2)+'\n')

def inventory():
    manifest=ROOT/'MANIFEST.sha256.json'
    if not manifest.exists():
        raise ValueError('Missing distribution manifest')
    files=json.loads(manifest.read_text())['files']
    seen=set()
    for row in files:
        rel=Path(row['path'])
        need(not rel.is_absolute() and '..' not in rel.parts,'Unsafe manifest path')
        need(row['path'] not in seen,'Duplicate manifest member');seen.add(row['path'])
        p=ROOT/rel
        need(p.is_file() and not p.is_symlink(),'Missing/nonregular file '+row['path'])
        need(p.stat().st_size==row['bytes'] and sha(p)==row['sha256'],
             'Manifest mismatch '+row['path'])
    return dict(status='DISTRIBUTION_HASHES_PASS',files=len(files))

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--output-dir',type=Path,required=True)
    p.add_argument('--quick',action='store_true')
    a=p.parse_args()
    need(__debug__ and not sys.flags.optimize,'Assertions must remain enabled; do not use -O')
    out=a.output_dir.resolve()
    need(out!=ROOT and ROOT not in out.parents,'Output must be outside the supplied packet')
    need(not out.exists() or not any(out.iterdir()),'Choose an empty output directory')
    out.mkdir(parents=True,exist_ok=True);(out/'logs').mkdir()
    receipt=dict(status='IN_PROGRESS',mode='quick' if a.quick else 'full',phases=[])
    begin=time.monotonic()
    def run(name,script,*args):
        print(name,flush=True)
        log=out/'logs'/(name+'.log');tick=time.monotonic()
        with log.open('w') as stream:
            r=subprocess.run([sys.executable,'-B',str(script),*map(str,args)],
                cwd=out,stdout=stream,stderr=subprocess.STDOUT,
                env={**os.environ,'PYTHONDONTWRITEBYTECODE':'1'})
        receipt['phases'].append(dict(name=name,returncode=r.returncode,
            seconds=time.monotonic()-tick,log=log.relative_to(out).as_posix()))
        dump(out/'replay.json',receipt)
        need(r.returncode==0,'Failed phase '+name+'; see '+str(log))
    try:
        receipt['inventory']=inventory()
        run('01_construct_source',ROOT/'code/construct.py','--output',out/'source')
        run('02_emitter_binding',ROOT/'code/check_emitter.py',
            '--sites',out/'source/sites.json','--output',out/'emitter.json')
        run('03_machine_folds_and_bootstrap',ROOT/'code/build_machine.py',
            '--source-dir',out/'source','--output',out/'machine')
        run('04_negative_fold_controls',ROOT/'code/check_negative_controls.py',
            '--parent',out/'source/parent224.k.tm','--output',out/'negative_controls.json')
        run('05_uniform_logic_generation',ROOT/'theory/uniform_g_certificate.py',
            '--output',out/'uniform')
        proof=out/'uniform/uniform_g_proof.json'
        need(proof.read_bytes()==(ROOT/'theory/uniform_g_proof.json').read_bytes(),
             'Regenerated schematic proof differs')
        run('06_independent_uniform_logic',ROOT/'theory/verify_uniform_g.py',proof,
            '--output',out/'uniform/independent_receipt.json')
        run('07_independent_finite_logic',ROOT/'theory/review_finite_logic.py',
            ROOT/'theory/merged_euclidean_helper_proofs.json',
            '--output',out/'finite_logic.json')
        for name in ['candidate222.tm','candidate222.k.tm','candidate222.legacy.tm','sites.json']:
            need((out/'machine'/name).read_bytes()==(ROOT/'machine'/name).read_bytes(),
                 'Rebuilt artifact differs: '+name)
        if a.quick:
            run('08_stored_runtime_audit',ROOT/'code/check_runtime.py',
                '--results',out/'machine','--output',ROOT/'evidence/runtime222.json','--audit-stored')
        else:
            run('08_fresh_unbounded_runtime',ROOT/'code/check_runtime.py',
                '--results',out/'machine','--output',out/'runtime222.json')
            need((out/'runtime222_cases.json').read_bytes()==(ROOT/'evidence/runtime222_cases.json').read_bytes(),
                 'Fresh runtime case records differ')
        receipt.update(status='QUICK_REPLAY_PASS' if a.quick else 'FULL_REPLAY_PASS',
            working_states=222,rows=444,guarded_cases=5956,
            canonical_sha256=sha(out/'machine/candidate222.tm'),
            source_sha256=sha(out/'machine/sites.json'),
            runtime_cases_sha256=sha(ROOT/'evidence/runtime222_cases.json'),
            seconds=time.monotonic()-begin,
            proof_status='Ordinary mathematical construction with fresh executable certificates; '
                         'inherited conditional-K/ZFC calibration; no new Rocq/Lean endpoint.',
            inherited_scope='The pinned K230 formal development and conditional-K equality '
                            'interpretation are documented dependencies, not recompiled here.')
        dump(out/'replay.json',receipt)
        print(json.dumps(receipt,indent=2))
    except Exception as exc:
        receipt.update(status='FAILED',error=repr(exc),seconds=time.monotonic()-begin)
        dump(out/'replay.json',receipt)
        raise

if __name__=='__main__':main()
