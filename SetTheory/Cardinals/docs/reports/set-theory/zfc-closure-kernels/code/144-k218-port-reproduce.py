#!/usr/bin/env python3
"""Offline construction, calibration replay and exact runtime proof of K218.

Default regenerates the final unbounded proof. --quick audits its stored
receipt. --full-baseline also regenerates predecessor runtime proofs.
The proof boundary is ordinary mathematics plus executable certificates,
not a new proof-assistant kernel theorem for these exact machine bytes.
"""
from pathlib import Path, PurePosixPath
import argparse, hashlib, json, os, shutil, stat, subprocess, sys, time, zipfile

ROOT=Path(__file__).resolve().parent
BASE_SHA='04813567f393b6c4015a96aba092159e9021703b4b662c7be69bd2a86497e31b'

def need(condition,message):
    if not condition:raise ValueError(message)
def sha(path):return hashlib.sha256(path.read_bytes()).hexdigest()
def dump(path,value):path.write_text(json.dumps(value,indent=2,sort_keys=True)+'\n')
def safe(name):
    p=PurePosixPath(name)
    need(isinstance(name,str) and name and not p.is_absolute() and
         all(x not in ('','.','..') for x in name.rstrip('/').split('/')) and
         '\\'not in name and ':'not in name and '\x00'not in name,'Unsafe path')
    return p

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--output-dir',type=Path,required=True)
    ap.add_argument('--quick',action='store_true')
    ap.add_argument('--full-baseline',action='store_true')
    args=ap.parse_args()
    need(__debug__ and not sys.flags.optimize and not os.environ.get('PYTHONOPTIMIZE'),'Assertions must remain enabled')
    out=args.output_dir.resolve()
    need(out!=ROOT and ROOT not in out.parents,'Output must be outside the portable directory')
    need(not out.exists() or not any(out.iterdir()),'Output directory must initially be empty')
    out.mkdir(parents=True,exist_ok=True);(out/'logs').mkdir()
    started=time.monotonic()
    receipt=dict(status='RUNNING',mode='stored_runtime_integrity'if args.quick else'fresh_final_unbounded_runtime',
                 full_baseline=args.full_baseline,phases=[])
    def save():receipt['seconds']=time.monotonic()-started;dump(out/'replay.json',receipt)
    def phase(name,arguments):
        print(name,flush=True);begin=time.monotonic();log=out/'logs'/(name+'.log')
        with log.open('w')as f:
            r=subprocess.run([sys.executable,'-B',*map(str,arguments)],stdout=f,stderr=subprocess.STDOUT,
                env={**os.environ,'PYTHONDONTWRITEBYTECODE':'1'})
        receipt['phases'].append(dict(name=name,returncode=r.returncode,seconds=time.monotonic()-begin,log=str(log.relative_to(out))))
        save();need(r.returncode==0,'Failed '+name+'; see '+str(log))
    try:
        manifest=json.loads((ROOT/'manifest.json').read_text())
        need(manifest['schema_version']==1,'Manifest format')
        names=set()
        for e in manifest['files']:
            name=e['path'];need(name not in names and name!='manifest.json','Duplicate/self manifest member');names.add(name)
            p=ROOT/safe(name)
            need(p.is_file()and not p.is_symlink()and ROOT in p.resolve().parents,'Missing/nonregular manifest member')
            need(p.stat().st_size==e['size']and sha(p)==e['sha256'],'Manifest mismatch: '+name)
        actual=set()
        for p in ROOT.rglob('*'):
            need(not p.is_symlink(),'Symlink in portable inventory')
            if p.is_file()and p!=ROOT/'manifest.json':actual.add(p.relative_to(ROOT).as_posix())
        need(actual==names,'Manifest does not cover exact portable inventory')
        receipt['manifest_files']=len(names);save()
        archive=ROOT/'vendor/K219_Construction_2026-10-20.zip'
        need(sha(archive)==BASE_SHA,'Pinned parent archive differs')
        with zipfile.ZipFile(archive)as z:
            members=set()
            for info in z.infolist():
                p=safe(info.filename)
                need(p.parts[0]=='K219_Construction_2026-10-20'and p.as_posix()not in members,'Unexpected/duplicate archive member')
                members.add(p.as_posix());mode=stat.S_IFMT(info.external_attr>>16)
                need(mode in(0,stat.S_IFREG,stat.S_IFDIR)and not info.flag_bits&1,'Nonregular/encrypted archive member')
                target=out/'baseline'/p
                need(out in target.resolve().parents,'Escaping archive member')
                if info.is_dir():target.mkdir(parents=True,exist_ok=True)
                else:
                    target.parent.mkdir(parents=True,exist_ok=True)
                    with z.open(info)as src,target.open('xb')as dst:shutil.copyfileobj(src,dst)
                    need(target.stat().st_size==info.file_size,'Truncated archive member')
        baseline=out/'baseline/K219_Construction_2026-10-20'
        flags=['--full-baseline']if args.full_baseline else['--quick']
        phase('01_parent219_calibration_and_construction',[baseline/'portable/reproduce.py',*flags,'--output-dir',out/'parent_replay'])
        parent221=out/'parent_replay/parent_replay/baseline/K221_Construction_2026-10-20'
        phase('02_source_and_literal218_construction',[ROOT/'build218.py','--parent',baseline,'--output',out/'construction'])
        phase('02b_independent_source_and_alias',[ROOT/'check_classical218.py',
            '--parent-sites',baseline/'machine/sites219.json',
            '--old-sites',out/'construction/intermediate_sites205.json',
            '--new-sites',out/'construction/sites.json',
            '--old-table',out/'construction/intermediate219.tm',
            '--unfolded-table',out/'construction/unfolded219.tm',
            '--new-table',out/'construction/candidate.tm',
            '--out',out/'independent_source_and_alias.json'])
        phase('03_canonical_and_whole_blank',[ROOT/'canonicalize218.py','--table',out/'construction/candidate.tm','--sites',out/'construction/sites.json','--output',out/'canonical'])
        phase('04_separate_blank_audit',[ROOT/'check_blank_startup.py',out/'construction/candidate.tm','--output',out/'independent_blank_startup.json'])
        if args.quick:
            shutil.copytree(ROOT/'reference_results',out/'runtime')
        else:
            phase('05_fresh_unbounded_runtime',[ROOT/'check_runtime218.py','--baseline',parent221,'--table',out/'construction/candidate.tm','--sites',out/'construction/sites.json','--output',out/'runtime'])
        phase('06_independent_runtime_audit',[ROOT/'audit_runtime218.py','--baseline',parent221,'--table',out/'construction/candidate.tm','--sites',out/'construction/sites.json','--runtime',out/'runtime','--driver',ROOT/'check_runtime218.py','--canonical',out/'canonical/canonicalization.json','--output',out/'runtime_audit.json'])
        published=ROOT.parent/'machine'
        for built,name in [(out/'construction/candidate.tm','k218.native.tm'),
                           (out/'construction/sites.json','sites218.json'),
                           (out/'canonical/k218.tm','k218.tm')]:
            need(built.read_bytes()==(published/name).read_bytes(),'Published artifact differs: '+name)
        receipt.update(status='QUICK_K218_REPLAY_PASS'if args.quick else'FULL_K218_REPLAY_PASS',
            native_table_sha256=sha(out/'construction/candidate.tm'),canonical_table_sha256=sha(out/'canonical/k218.tm'),
            source_sha256=sha(out/'construction/sites.json'),
            theorem_scope='ZFC proves blank nonhalting equivalent to Con(ZFC): exact ordinal source-control equivalence, all-natural exact-table primitive simulation, complete blank initialization, and pinned K219 finite-refutation calibration compose.',
            verification_boundary='Ordinary mathematical proofs plus executable symbolic certificates. No newly compiled proof-assistant endpoint. Default rederives the final unbounded runtime; quick audits its stored receipt. Parent construction and calibration replay offline in every mode.')
        save();print(receipt['status'],flush=True)
    except Exception as e:
        receipt.update(status='FAILED',error=repr(e));save();raise

if __name__=='__main__':main()
