#!/usr/bin/env python3
"""Offline exact K218 reconstruction, all-natural source proof and physical refinement.

Default freshly rederives all 6,167 unbounded K218 runtime cases and replays
inherited construction/calibration using stored ancestral runtime evidence.
--quick audits stored K218 runtime evidence; --full-baseline freshly proves
upstream K219 too; --deep-baseline also requests ancestor runtime derivations.
The separate supplementary research ZIP is not part of the machine theorem.
"""
from pathlib import Path,PurePosixPath
import argparse,hashlib,json,os,shutil,stat,subprocess,sys,time,zipfile
ROOT=Path(__file__).resolve().parents[1]
BASE_NAME='K219_Construction_2026-10-20'
BASE_SHA='04813567f393b6c4015a96aba092159e9021703b4b662c7be69bd2a86497e31b'
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
    receipt=dict(status='RUNNING',mode='stored_final_runtime_audit'if args.quick else'fresh_final_unbounded_runtime',full_baseline=args.full_baseline,deep_baseline=args.deep_baseline,phases=[])
    def save():receipt['seconds']=time.monotonic()-started;dump(out/'replay.json',receipt)
    def phase(name,command):
        print(name,flush=True);t=time.monotonic();log=out/'logs'/(name+'.log')
        with log.open('w')as stream:
            r=subprocess.run([sys.executable,'-B',*map(str,command)],stdout=stream,stderr=subprocess.STDOUT,env={**os.environ,'PYTHONDONTWRITEBYTECODE':'1'})
        receipt['phases'].append(dict(name=name,returncode=r.returncode,seconds=time.monotonic()-t,log=str(log.relative_to(out))))
        save();need(r.returncode==0,'Failed phase '+name+'; inspect '+str(log))
    try:
        receipt['manifest_files']=verify_manifest();save()
        supplementary=ROOT/'supplementary/Membership_Fourth_Parameter_Obstruction_2026-10-20.zip'
        need(sha(supplementary)=='4b662ddec7eb9af7493f9ddec7b81c377097fedd9290eb4820ac60ef218fc6f3','Supplementary archive mismatch')
        with zipfile.ZipFile(supplementary)as z:need(z.testzip()is None,'Supplementary ZIP CRC failed')
        base=extract(ROOT/'vendor'/(BASE_NAME+'.zip'),out)
        flags=[]if args.full_baseline or args.deep_baseline else['--quick']
        if args.deep_baseline:flags.append('--full-baseline')
        phase('01_pinned_baseline_calibration',[base/'portable/reproduce.py',*flags,'--output-dir',out/'baseline_replay'])
        prior=json.loads((ROOT/'verification/baseline_full_replay.json').read_text())
        need(prior['status']=='FULL_K219_REPLAY_PASS'and prior['mode']=='fresh_final_unbounded_runtime'and len(prior['phases'])==6 and all(p['returncode']==0 for p in prior['phases']),'Historical baseline receipt incomplete')
        parent221=out/'baseline_replay/parent_replay/baseline/K221_Construction_2026-10-20'
        vendor=parent221/'portable/runtime/vendor';mapping=parent221/'portable/runtime/reference_results/legacy_mapping.json'
        source=out/'source';source.mkdir()
        for filename in('reconstruct_source.py','dag_recipe.json'):
            shutil.copy2(ROOT/'portable/source'/filename,source/filename)
        shutil.copy2(base/'machine/sites219.json',source/'baseline_sites219.json')
        shutil.copy2(ROOT/'machine/sites218.json',source/'candidate_sites218.json')
        phase('02_all_natural_source_bisimulation',[source/'reconstruct_source.py'])
        phase('03_full_upstream_table_lineage',[ROOT/'portable/construct.py','--baseline',base,'--output',out/'construction'])
        table=out/'construction/candidate.tm';sites=out/'construction/candidate.sites.json'
        need(sites.read_bytes()==(source/'reconstructed_sites218.json').read_bytes(),'Independent source reconstructions differ')
        phase('04_canonical_labels_and_complete_blank',[ROOT/'portable/canonicalize.py','--table',table,'--source',sites,'--output',out/'canonical'])
        runtime=out/'runtime';runtime.mkdir()
        runtime_args=[ROOT/'portable/check_runtime.py','--variant','candidate218','--table',table,'--source',sites,'--vendor',vendor,'--mapping',mapping,'--out',runtime]
        if args.quick:
            for filename in('runtime.json','cases.json'):
                shutil.copy2(ROOT/'certificates/runtime'/filename,runtime/filename)
            phase('05_fresh_whole_blank_startup',[*runtime_args,'--preflight-only'])
            phase('06_stored_runtime_audit',[*runtime_args,'--audit-only'])
        else:
            phase('05_fresh_unbounded_runtime',runtime_args)
        for built,name in[(table,'k218.normalized.tm'),(sites,'sites218.json'),(out/'canonical/k218.native.tm','k218.native.tm'),(out/'canonical/k218.tm','k218.tm'),(out/'canonical/canonicalization.json','canonicalization.json')]:
            need(built.read_bytes()==(ROOT/'machine'/name).read_bytes(),'Distributed artifact differs: '+name)
        need((runtime/'canonical.tm').read_bytes()==(out/'canonical/k218.tm').read_bytes(),'Independent canonical exports differ')
        for filename in('verification.json','ordinal_correspondence.json'):
            need((source/filename).read_bytes()==(ROOT/'certificates/source'/filename).read_bytes(),'Source proof differs: '+filename)
        phase('07_negative_controls',[ROOT/'verification/negative_controls.py','--baseline',base,'--vendor',vendor,'--runtime',runtime,'--output',out/'negative_controls.json'])
        audit=json.loads((runtime/'integrity.json').read_text());canonical=json.loads((out/'canonical/canonicalization.json').read_text())
        receipt.update(status='QUICK_K218_REPLAY_PASS'if args.quick else'FULL_K218_REPLAY_PASS',working_states=218,rows=436,normalized_table_sha256=sha(table),native_table_sha256=sha(out/'canonical/k218.native.tm'),canonical_table_sha256=sha(out/'canonical/k218.tm'),source_sha256=sha(sites),startup_steps=312701,generic_cases=audit['generic_cases'],generic_cases_excluded=0,source_bisimulation=True,full_upstream_lineage=True,baseline_zip_sha256=BASE_SHA,baseline_runtime_fresh_this_run=bool(args.full_baseline or args.deep_baseline),final_runtime_fresh_this_run=not args.quick,supplementary_checked='Pinned bytes and ZIP CRC only; separate research theorem, not a premise of the machine theorem.',
            verification_boundary='Complete all-natural source bisimulation, exact complete blank initialization and full unbounded generic primitive refinement compose with the pinned upstream logical calibration. Executable ordinary mathematical checking, not a newly compiled exact-byte proof-assistant endpoint. No unconditional nonhalting or minimality claim.')
        save();print(receipt['status'],flush=True)
    except Exception as error:
        receipt.update(status='FAILED',error=repr(error));save();raise
if __name__=='__main__':main()
