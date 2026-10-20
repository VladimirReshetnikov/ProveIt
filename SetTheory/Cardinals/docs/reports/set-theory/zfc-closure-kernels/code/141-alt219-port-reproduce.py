#!/usr/bin/env python3
"""Offline reconstruction, source transport, full startup and unbounded refinement.

Default freshly rederives all three variant runtimes and replays the baseline
construction/calibration with its stored runtime. --quick audits stored variant
runtime certificates (not fresh symbolic proof). --full-baseline freshly proves
the upstream219 runtime too; --deep-baseline rederives ancestor runtimes as well.
All modes are executable mathematical checking, not proof-assistant endpoints.
"""
from pathlib import Path,PurePosixPath
import argparse,hashlib,json,os,shutil,stat,subprocess,sys,time,zipfile
ROOT=Path(__file__).resolve().parents[1]
BASE_NAME='K219_Construction_2026-10-20'
BASE_SHA='04813567f393b6c4015a96aba092159e9021703b4b662c7be69bd2a86497e31b'
VARIANTS=('zero_terminal','retagged','composed')
def need(x,message):
    if not x:raise ValueError(message)
def sha(path):return hashlib.sha256(path.read_bytes()).hexdigest()
def dump(path,obj):path.write_text(json.dumps(obj,indent=2,sort_keys=True)+'\n')
def safe(name):
    need(isinstance(name,str) and name and not '\\'in name and not ':'in name and not '\0'in name,'Unsafe path')
    p=PurePosixPath(name)
    need(not p.is_absolute() and all(x not in ('','.','..')for x in name.rstrip('/').split('/')),'Unsafe path')
    return p

def verify_manifest():
    manifest=json.loads((ROOT/'manifest.json').read_text());need(manifest['schema_version']==1,'Manifest format')
    seen=set()
    for item in manifest['files']:
        name=item['path'];need(name not in seen and name not in('manifest.json','SHA256SUMS'),'Duplicate/self member')
        seen.add(name);p=ROOT/safe(name)
        need(p.is_file() and not p.is_symlink() and ROOT in p.resolve().parents,'Missing/nonregular member')
        need(p.stat().st_size==item['size']and sha(p)==item['sha256'],'Manifest mismatch: '+name)
    actual=set()
    for p in ROOT.rglob('*'):
        need(not p.is_symlink(),'Symlink member')
        if p.is_file() and p.name not in ('manifest.json','SHA256SUMS') or p.is_file() and p.parent!=ROOT:
            actual.add(p.relative_to(ROOT).as_posix())
    need(actual==seen,'Manifest does not cover exact inventory')
    sums=''.join(f'{sha(ROOT/n)}  {n}\n'for n in sorted(seen|{'manifest.json'}))
    need((ROOT/'SHA256SUMS').read_text()==sums,'SHA256SUMS differs from complete inventory')
    return len(seen)

def extract(archive,out):
    need(sha(archive)==BASE_SHA,'Pinned upstream archive mismatch')
    with zipfile.ZipFile(archive)as zipped:
        names=set()
        for member in zipped.infolist():
            relative=safe(member.filename)
            need(relative.parts[0]==BASE_NAME and str(relative)not in names,'Unexpected/duplicate ZIP member')
            names.add(str(relative));mode=stat.S_IFMT(member.external_attr>>16)
            need(mode in(0,stat.S_IFREG,stat.S_IFDIR)and not member.flag_bits&1,'Nonregular/encrypted ZIP member')
            target=out/'vendor'/relative;need(out in target.resolve().parents,'Escaping ZIP member')
            if member.is_dir():target.mkdir(parents=True,exist_ok=True)
            else:
                target.parent.mkdir(parents=True,exist_ok=True)
                with zipped.open(member)as src,target.open('xb')as dst:shutil.copyfileobj(src,dst)
                need(target.stat().st_size==member.file_size,'Truncated ZIP member')
    return out/'vendor'/BASE_NAME

def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--output-dir',type=Path,required=True)
    ap.add_argument('--quick',action='store_true');ap.add_argument('--full-baseline',action='store_true');ap.add_argument('--deep-baseline',action='store_true');args=ap.parse_args()
    need(__debug__ and not sys.flags.optimize and not os.environ.get('PYTHONOPTIMIZE'),'Assertions must remain enabled')
    out=args.output_dir.resolve();need(out!=ROOT and ROOT not in out.parents,'Output must be outside this packet')
    need(not out.exists()or not any(out.iterdir()),'Output must initially be empty')
    out.mkdir(parents=True,exist_ok=True);(out/'logs').mkdir();started=time.monotonic()
    receipt=dict(status='RUNNING',mode='stored_variant_runtime_audit'if args.quick else'fresh_three_variant_unbounded_runtime',full_baseline=args.full_baseline,deep_baseline=args.deep_baseline,phases=[])
    def save():receipt['seconds']=time.monotonic()-started;dump(out/'replay.json',receipt)
    def phase(name,command):
        print(name,flush=True);t=time.monotonic();log=out/'logs'/(name+'.log')
        with log.open('w')as stream:
            r=subprocess.run([sys.executable,'-B',*map(str,command)],stdout=stream,stderr=subprocess.STDOUT,env={**os.environ,'PYTHONDONTWRITEBYTECODE':'1'})
        receipt['phases'].append(dict(name=name,returncode=r.returncode,seconds=time.monotonic()-t,log=str(log.relative_to(out))))
        save();need(r.returncode==0,'Failed phase '+name+'; inspect '+str(log))
    try:
        receipt['manifest_files']=verify_manifest();save()
        base=extract(ROOT/'vendor'/(BASE_NAME+'.zip'),out)
        flags=[]if args.full_baseline or args.deep_baseline else['--quick']
        if args.deep_baseline:flags.append('--full-baseline')
        phase('01_pinned_baseline_calibration',[base/'portable/reproduce.py',*flags,'--output-dir',out/'baseline_replay'])
        prior=json.loads((ROOT/'verification/baseline_full_replay.json').read_text())
        need(prior['status']=='FULL_K219_REPLAY_PASS'and prior['mode']=='fresh_final_unbounded_runtime'and len(prior['phases'])==6 and all(p['returncode']==0 for p in prior['phases']),'Historical baseline receipt incomplete')
        parent221=out/'baseline_replay/parent_replay/baseline/K221_Construction_2026-10-20'
        vendor=parent221/'portable/runtime/vendor';mapping=parent221/'portable/runtime/reference_results/legacy_mapping.json'
        phase('02_literal_reconstruction',[ROOT/'portable/construct.py','--baseline',base,'--output',out/'machine'])
        phase('02b_independent_source_composition',[
            ROOT/'verification/independent_source_check.py',
            '--original-source',base/'machine/sites219.json',
            '--zero-source',out/'machine/zero_terminal/sites.json',
            '--retagged-source',out/'machine/retagged/sites.json',
            '--retagged-seed-source',out/'machine/retagged/sites.json',
            '--combined-source',out/'machine/composed/sites.json',
            '--original-table',base/'machine/k219.native.tm',
            '--zero-table',out/'machine/zero_terminal/k219.native.tm',
            '--retagged-table',out/'machine/retagged/k219.native.tm',
            '--retagged-seed-table',out/'machine/composition_seed.tm',
            '--combined-table',out/'machine/composed/k219.native.tm',
            '--combined-native-table',ROOT/'machine/composed/k219.upstream-labels.tm',
            '--output-dir',out/'independent_source'])
        summaries=[]
        for name in VARIANTS:
            machine=out/'machine'/name;cert=out/'certificates'/name;cert.mkdir(parents=True,exist_ok=True)
            phase('03_source_'+name,[ROOT/'portable/check_source.py','--baseline',base,'--source',machine/'sites.json','--variant',name,'--output',cert/'source.json'])
            phase('04_canonical_startup_'+name,[ROOT/'portable/canonicalize.py','--variant',name,'--table',machine/'k219.native.tm','--source',machine/'sites.json','--output',machine])
            runtime_args=[ROOT/'portable/check_runtime.py','--variant',name,'--table',machine/'k219.native.tm','--source',machine/'sites.json','--vendor',vendor,'--mapping',mapping,'--out',cert]
            if args.quick:
                for filename in('runtime.json','cases.json'):
                    shutil.copy2(ROOT/'certificates'/name/filename,cert/filename)
                phase('05_fresh_startup_'+name,[*runtime_args,'--preflight-only'])
                phase('06_stored_runtime_audit_'+name,[*runtime_args,'--audit-only'])
            else:
                phase('05_fresh_unbounded_'+name,runtime_args)
            for filename in('k219.native.tm','k219.tm','k219.upstream-labels.tm','sites.json','canonicalization.json'):
                need((machine/filename).read_bytes()==(ROOT/'machine'/name/filename).read_bytes(),'Delivered artifact differs: '+name+'/'+filename)
            need((cert/'source.json').read_bytes()==(ROOT/'certificates'/name/'source.json').read_bytes(),'Delivered source certificate differs: '+name)
            need((cert/'canonical.tm').read_bytes()==(machine/'k219.tm').read_bytes(),'Independent canonical tables differ')
            record=json.loads((machine/'canonicalization.json').read_text());audit=json.loads((cert/'integrity.json').read_text())
            summaries.append(dict(variant=name,normalized_table_sha256=record['table_sha256'],upstream_labels_sha256=record['upstream_labels_sha256'],canonical_table_sha256=record['canonical_sha256'],source_sha256=record['source_sha256'],working_states=219,rows=438,startup_steps=record['startup']['steps'],generic_cases=audit['generic_cases'],generic_cases_excluded=0))
        phase('07_negative_controls',[ROOT/'verification/negative_controls.py','--baseline',base,'--vendor',vendor,'--output',out/'negative_controls.json','--certificates',out/'certificates'])
        need(len({s['canonical_table_sha256']for s in summaries})==3,'Canonical alternatives are not distinct')
        receipt.update(status='QUICK_THREE_ALTERNATIVES_AUDIT_PASS'if args.quick else'SELF_CONTAINED_THREE_ALTERNATIVES_REPLAY_PASS',variants=summaries,baseline_zip_sha256=BASE_SHA,baseline_runtime_fresh_this_run=bool(args.full_baseline or args.deep_baseline),variant_runtimes_fresh_this_run=not args.quick,
            verification_boundary='Full-source all-natural transport, exact complete blank initialization, and complete unbounded generic primitive refinement compose with the pinned upstream logical calibration. Ordinary executable mathematical checking; no new exact-byte proof-assistant endpoint, unconditional nonhalting, minimality, or <=218 result.')
        save();print(receipt['status'],flush=True)
    except Exception as error:
        receipt.update(status='FAILED',error=repr(error));save();raise
if __name__=='__main__':main()
