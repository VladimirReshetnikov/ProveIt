#!/usr/bin/env python3
"""Offline K223 reconstruction and certificate replay (Python 3.10+).

Default: fresh source, emitter, finite logic, folds and blank-start checks,
then integrity/coverage audit of the retained unbounded runtime derivations.
--full: freshly rederive all 5956 final-table runtime cases.
--full-baseline: also rederive all inherited K224/K225/K226 runtime cases.
No mode downloads files or claims a new proof-assistant kernel build.
"""
from pathlib import Path, PurePosixPath
import argparse, hashlib, json, os, shutil, stat, subprocess, sys, time, zipfile
ROOT=Path(__file__).resolve().parent
BASELINE_SHA='cf5db8d08a34f5661ad1266226809ed1f0099fd38374c66d127e1e06519c6887'
BASELINE_NAME='K224_Construction_2026-10-20'

def need(ok,message):
    if not ok:raise ValueError(message)
def sha(path):return hashlib.sha256(Path(path).read_bytes()).hexdigest()
def dump(path,data):Path(path).write_text(json.dumps(data,indent=2)+'\n')
def same(a,b):
    need(Path(a).read_bytes()==Path(b).read_bytes(),'Reproduced bytes differ: '+str(a));return sha(a)
def relative(name):
    p=PurePosixPath(name)
    need(name and not p.is_absolute() and '\\' not in name and ':' not in name and '\x00' not in name
        and all(x not in ('','.','..') for x in name.rstrip('/').split('/')),'Unsafe relative path')
    return Path(*p.parts)

def manifest():
    data=json.loads((ROOT/'manifest.json').read_text());seen=set()
    need(data['schema_version']==1,'Manifest schema differs')
    for item in data['files']:
        p=ROOT/relative(item['path']);need(p.is_file() and not p.is_symlink(),'Missing/nonregular manifest file')
        need(item['path'] not in seen,'Duplicate manifest member');seen.add(item['path'])
        need(p.stat().st_size==item['size'] and sha(p)==item['sha256'],'Manifest file differs: '+item['path'])
    actual={p.relative_to(ROOT).as_posix() for p in ROOT.rglob('*') if p.is_file() and p.name!='manifest.json'}
    need(actual==seen,'Portable manifest inventory differs')
    return dict(files=len(seen),manifest_sha256=sha(ROOT/'manifest.json'))

def extract(archive,destination):
    need(sha(archive)==BASELINE_SHA,'Pinned baseline archive differs');destination.mkdir()
    with zipfile.ZipFile(archive) as z:
        seen=set()
        for e in z.infolist():
            r=relative(e.filename);need(r not in seen,'Duplicate archive member');seen.add(r)
            mode=stat.S_IFMT((e.external_attr>>16)&0xffff)
            need(mode in (0,stat.S_IFREG,stat.S_IFDIR) and not e.flag_bits&1,'Unsupported archive member')
            p=destination/r
            if e.is_dir():p.mkdir(parents=True,exist_ok=True)
            else:
                p.parent.mkdir(parents=True,exist_ok=True)
                with z.open(e) as source,p.open('xb') as out:shutil.copyfileobj(source,out)
                need(p.stat().st_size==e.file_size,'Incomplete extracted file')
    return destination/BASELINE_NAME

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--output-dir',type=Path,required=True)
    ap.add_argument('--full',action='store_true');ap.add_argument('--full-baseline',action='store_true')
    a=ap.parse_args();need(__debug__ and not sys.flags.optimize,'Assertions must be enabled; do not use -O')
    out=a.output_dir.resolve();need(ROOT.parent!=out and ROOT.parent not in out.parents,'Output must be outside the supplied packet')
    need(not out.exists() or not any(out.iterdir()),'Use an initially empty output directory')
    out.mkdir(parents=True,exist_ok=True);(out/'logs').mkdir()
    start=time.monotonic();receipt=dict(status='IN_PROGRESS',mode='full' if a.full else 'quick',phases=[])
    def run(name,script,*args):
        log=out/'logs'/(name+'.log');cmd=[sys.executable,'-B',str(script),*map(str,args)]
        print(name,flush=True);begin=time.monotonic()
        with log.open('w') as f:
            p=subprocess.run(cmd,stdout=f,stderr=subprocess.STDOUT,cwd=out,env={**os.environ,'PYTHONDONTWRITEBYTECODE':'1'})
        item=dict(name=name,returncode=p.returncode,seconds=time.monotonic()-begin,log=log.relative_to(out).as_posix())
        receipt['phases'].append(item);dump(out/'replay.json',receipt)
        need(p.returncode==0,'Phase failed: '+name+'; see '+str(log))
    try:
        receipt['manifest']=manifest()
        baseline=extract(ROOT/'vendor'/f'{BASELINE_NAME}.zip',out/'baseline-input')
        flags=['--full','--full-baseline'] if a.full_baseline else []
        run('01_baseline224',baseline/'portable/reproduce.py','--output-dir',out/'baseline-replay',*flags)
        br=json.loads((out/'baseline-replay/replay.json').read_text())
        need(br['status'] in ('FULL_REPLAY_PASS','QUICK_REPLAY_PASS'),'Inherited replay failed')
        receipt['baseline']=dict(status=br['status'],archive_sha256=BASELINE_SHA,fresh_runtime=a.full_baseline)
        upstream=out/'baseline-replay/upstream/K225_Construction_2026-10-19/portable/baseline226'
        run('02_construct_source',ROOT/'verification/construct_g226.py','--baseline224',baseline,'--upstream226',upstream,'--output',out/'source')
        same(out/'source/parent226.k.tm',ROOT/'folds/parent226.k.tm')
        same(out/'source/sites226.json',ROOT/'results/sites.json')
        run('03_exact_emitter',ROOT/'verification/check_g_emitter.py','--baseline224',baseline,'--upstream226',upstream,
            '--sites',out/'source/sites226.json','--output',out/'source/emitter_receipt.json')
        td=out/'theory';td.mkdir()
        for name in ['combined_helper_certificate.py','merged_euclidean_helper_certificate.py','review_logic.py']:
            shutil.copyfile(ROOT/'theory'/name,td/name)
        run('04_finite_logic',td/'merged_euclidean_helper_certificate.py')
        same(td/'merged_euclidean_helper_proofs.json',ROOT/'theory/merged_euclidean_helper_proofs.json')
        run('05_independent_logic',td/'review_logic.py',td/'merged_euclidean_helper_proofs.json','--output',td/'independent_review.json')
        run('06_all_tape_folds',ROOT/'folds/check_folds.py','--parent',out/'source/parent226.k.tm',
            '--candidate',ROOT/'folds/candidate223.k.tm','--specification',ROOT/'folds/folds.json','--output',out/'fold_certificate.json')
        run('07_canonical_and_blank',ROOT/'build223.py','--output-dir',out/'machine')
        for name in ['candidate223.tm','candidate223.k.tm','candidate223.legacy.tm','candidate223.csv','state_map.json','bootstrap223.json']:
            same(out/'machine'/name,ROOT/'results'/name)
        shutil.copyfile(ROOT/'results/sites.json',out/'machine/sites.json')
        if a.full:
            run('08_unbounded_runtime',ROOT/'runtime223.py','--results',out/'machine','--output',out/'machine/runtime223.json')
            same(out/'machine/runtime223_cases.json',ROOT/'results/runtime223_cases.json')
        else:
            run('08_stored_runtime_audit',ROOT/'runtime223.py','--results',ROOT/'results','--audit-stored')
        receipt.update(status='FULL_REPLAY_PASS' if a.full else 'QUICK_REPLAY_PASS',working_states=223,rows=446,
            guarded_runtime_cases=5956,canonical_table_sha256=sha(ROOT/'results/candidate223.tm'),
            source_sha256=sha(ROOT/'results/sites.json'),proof_sha256=sha(td/'merged_euclidean_helper_proofs.json'),
            seconds=time.monotonic()-start,
            proof_status='Ordinary mathematics with finite and unbounded executable certificates; inherited K224/ZFC calibration; no new Rocq or Lean endpoint.')
        dump(out/'replay.json',receipt);print(json.dumps(receipt,indent=2))
    except Exception as e:
        receipt.update(status='FAILED',error=repr(e),seconds=time.monotonic()-start);dump(out/'replay.json',receipt);raise

if __name__=='__main__':main()
