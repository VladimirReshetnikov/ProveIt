#!/usr/bin/env python3
"""Offline reconstruction and verification of the exact K219 construction.

Default: replay the pinned parent construction/calibration, rebuild K219,
recompute its canonical table and complete blank initialization, freshly prove
all 6,167 unbounded primitive interfaces, and independently audit the results.
--quick checks the stored final runtime receipt instead of rederiving it.
--full-baseline additionally requests fresh inherited runtime proofs.
No mode claims a newly compiled proof-assistant kernel theorem.
"""
from pathlib import Path, PurePosixPath
import argparse, hashlib, json, os, shutil, stat, subprocess, sys, time, zipfile

ROOT=Path(__file__).resolve().parent
BASE_SHA='132cbb326fcbf6e54957a03095c5f790e207f4ed8ebfb6ceb6e272f329e4ee00'

def need(x,message):
    if not x:raise ValueError(message)
def sha(path):return hashlib.sha256(path.read_bytes()).hexdigest()
def dump(path,obj):path.write_text(json.dumps(obj,indent=2,sort_keys=True)+'\n')
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
        archive=ROOT/'vendor/K220_Construction_2026-10-20.zip'
        need(sha(archive)==BASE_SHA,'Pinned parent archive differs')
        with zipfile.ZipFile(archive)as z:
            members=set()
            for info in z.infolist():
                p=safe(info.filename)
                need(p.parts[0]=='K220_Construction_2026-10-20'and p.as_posix()not in members,'Unexpected/duplicate archive member')
                members.add(p.as_posix());mode=stat.S_IFMT(info.external_attr>>16)
                need(mode in(0,stat.S_IFREG,stat.S_IFDIR)and not info.flag_bits&1,'Nonregular/encrypted archive member')
                target=out/'baseline'/p
                need(out in target.resolve().parents,'Escaping archive member')
                if info.is_dir():target.mkdir(parents=True,exist_ok=True)
                else:
                    target.parent.mkdir(parents=True,exist_ok=True)
                    with z.open(info)as src,target.open('xb')as dst:shutil.copyfileobj(src,dst)
                    need(target.stat().st_size==info.file_size,'Truncated archive member')
        baseline=out/'baseline/K220_Construction_2026-10-20'
        flags=['--full-baseline']if args.full_baseline else['--quick']
        phase('01_parent220_calibration_and_construction',[baseline/'portable/reproduce.py',*flags,'--output-dir',out/'parent_replay'])
        parent221=out/'parent_replay/baseline/K221_Construction_2026-10-20'
        phase('02_exact_source_replacement',[ROOT/'build_source219.py','--sites220',baseline/'machine/sites220.json','--out',out/'source'])
        phase('03_literal219_construction',[ROOT/'build219.py','--baseline',baseline,'--sites',out/'source/sites.json','--output',out/'construction'])
        phase('04_independent_canonical_and_blank',[ROOT/'canonicalize219.py','--table',out/'construction/candidate.tm','--sites',out/'construction/sites.json','--output',out/'canonical'])
        if args.quick:
            shutil.copytree(ROOT/'reference_results',out/'runtime')
        else:
            phase('05_fresh_unbounded_runtime',[ROOT/'check_runtime219.py','--baseline',parent221,'--table',out/'construction/candidate.tm','--sites',out/'construction/sites.json','--output',out/'runtime'])
        phase('06_independent_runtime_audit',[ROOT/'audit_runtime219.py','--baseline',parent221,'--table',out/'construction/candidate.tm','--sites',out/'construction/sites.json','--runtime',out/'runtime','--driver',ROOT/'check_runtime219.py','--canonical',out/'canonical/canonicalization.json','--output',out/'runtime_audit.json'])
        published=ROOT.parent/'machine'
        for built,name in [(out/'construction/candidate.tm','k219.native.tm'),
                           (out/'construction/sites.json','sites219.json'),
                           (out/'canonical/k219.tm','k219.tm')]:
            need(built.read_bytes()==(published/name).read_bytes(),'Published artifact differs: '+name)
        receipt.update(status='QUICK_K219_REPLAY_PASS'if args.quick else'FULL_K219_REPLAY_PASS',
            native_table_sha256=sha(out/'construction/candidate.tm'),
            canonical_table_sha256=sha(out/'canonical/k219.tm'),source_sha256=sha(out/'construction/sites.json'),
            theorem_scope='Blank nonhalting is equivalent in ZFC to Con(ZFC): exact source replacement, the proved terminating old/new equality contract, final primitive-runtime induction, exact blank initialization and pinned K220 calculus calibration compose.',
            verification_boundary='Executable ordinary mathematical certificates plus the written macro proof. No newly compiled exact-K219 proof-assistant endpoint. Quick mode audits a stored induction result; default freshly rederives it. Parent constructions/calibration replay offline in every mode.')
        save();print(receipt['status'],flush=True)
    except Exception as e:
        receipt.update(status='FAILED',error=repr(e));save();raise

if __name__=='__main__':main()
