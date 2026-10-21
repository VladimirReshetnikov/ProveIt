#!/usr/bin/env python3
"""Offline replay of the two new 219-state MP-return variants.

No 218-state result is claimed. Default freshly proves all primitive runtime
cases for both tables. --quick audits the packaged runtime receipts instead.
The written command/calculus proofs are a separate mathematical dependency;
this driver is not a proof-assistant kernel.
"""
from pathlib import Path,PurePosixPath
import argparse,hashlib,json,os,shutil,stat,subprocess,sys,time,zipfile

ROOT=Path(__file__).resolve().parents[1]
def need(value,message):
    if not value:raise ValueError(message)
def sha(path):return hashlib.sha256(path.read_bytes()).hexdigest()
def dump(path,obj):path.write_text(json.dumps(obj,indent=2,sort_keys=True)+'\n')

def extract(archive,out,prefix):
    seen=set()
    with zipfile.ZipFile(archive) as z:
        for info in z.infolist():
            name=info.filename;p=PurePosixPath(name)
            need(name and not p.is_absolute() and '\\'not in name and ':'not in name
                 and all(x not in('','.','..')for x in name.rstrip('/').split('/')),'Unsafe zip path')
            need(p.parts[0]==prefix and name not in seen,'Unexpected/duplicate archive member')
            seen.add(name)
            need(stat.S_IFMT(info.external_attr>>16)in(0,stat.S_IFREG,stat.S_IFDIR)
                 and not(info.flag_bits&1),'Unsupported archive entry')
            dst=out/Path(*p.parts)
            need(out.resolve()in dst.resolve().parents,'Escaping archive entry')
            if info.is_dir():dst.mkdir(parents=True,exist_ok=True)
            else:
                dst.parent.mkdir(parents=True,exist_ok=True)
                with z.open(info) as src,dst.open('xb')as f:shutil.copyfileobj(src,f)
                need(dst.stat().st_size==info.file_size,'Truncated extraction')
    return out/prefix

def audit_runtime(receipt,cases,table,source,driver):
    r=json.loads(receipt.read_text());ss=json.loads(source.read_text());cc=json.loads(cases.read_text())
    expected=[(i,pos)for i,(_,op,_)in enumerate(ss)for pos in((False,True)if op=='CD'else(False,))]
    need(r['status']=='UNIVERSAL_MATHEMATICAL_PASS','Runtime proof did not pass')
    need(r['table_sha256']==sha(table)and r['sites_sha256']==sha(source),'Runtime input identity')
    need(r['driver_sha256']==sha(driver),'Runtime driver identity')
    need([(c['site_index'],c['positive'])for c in cc]==expected,'Runtime guard coverage')
    need(r['cases']==r['expected_cases']==len(expected),'Runtime case census')
    need(r['symbolic_steps']==sum(c['symbolic_steps']for c in cc),'Runtime proof-step census')
    need(all(len(c['duration'])==13 and c['duration'][0]>0 and all(x>=0 for x in c['duration'])for c in cc),'Positive all-natural progress')
    need(r['minimum_actual_steps']==min(c['duration'][0]for c in cc),'Runtime minimum duration')
    need(len(r['directly_used_legacy_rows'])==438,'Unexpected transition coverage')
    return {k:r[k]for k in('status','working_states','cases','symbolic_steps','minimum_actual_steps','table_sha256','sites_sha256')}

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--output-dir',type=Path,required=True)
    ap.add_argument('--quick',action='store_true')
    ap.add_argument('--full-baseline',action='store_true')
    args=ap.parse_args();out=args.output_dir.resolve()
    need(__debug__ and not sys.flags.optimize and not os.environ.get('PYTHONOPTIMIZE'),'Keep assertions enabled')
    need(out!=ROOT and ROOT not in out.parents,'Output must be outside the packet')
    need(not out.exists()or not any(out.iterdir()),'Output directory must initially be empty')
    out.mkdir(parents=True,exist_ok=True);(out/'logs').mkdir()
    start=time.monotonic();r={'status':'RUNNING','target':218,'new_variant_states':219,'quick':args.quick,'phases':[]}
    def save():r['seconds']=time.monotonic()-start;dump(out/'replay.json',r)
    def phase(name,argv):
        begin=time.monotonic();log=out/'logs'/(name+'.log')
        print(name,flush=True)
        with log.open('w')as f:p=subprocess.run([sys.executable,'-B',*map(str,argv)],stdout=f,stderr=subprocess.STDOUT)
        r['phases'].append({'name':name,'returncode':p.returncode,'seconds':time.monotonic()-begin,'log':str(log.relative_to(out))});save()
        need(p.returncode==0,'Failed '+name+'; see '+str(log))
    try:
        manifest=json.loads((ROOT/'MANIFEST.json').read_text())
        for e in manifest['files']:
            p=ROOT/e['path'];need(p.is_file()and not p.is_symlink()and ROOT in p.resolve().parents,'Bad manifest path')
            need(p.stat().st_size==e['size']and sha(p)==e['sha256'],'Manifest mismatch: '+e['path'])
        r['manifest_files']=len(manifest['files'])
        prov=json.loads((ROOT/'PROVENANCE.json').read_text());archive=ROOT/prov['baseline_archive']
        need(sha(archive)==prov['baseline_archive_sha256'],'Pinned baseline archive differs')
        base=extract(archive,out/'vendor','K219_Construction_2026-10-20')
        phase('01_inherited219_replay',[base/'portable/reproduce.py',*(['--full-baseline']if args.full_baseline else['--quick']),'--output-dir',out/'baseline_replay'])
        b221=out/'baseline_replay/parent_replay/baseline/K221_Construction_2026-10-20'
        need(b221.is_dir(),'Inherited K221 runtime was not extracted')
        phase('02_construct',[ROOT/'portable/construct.py','--baseline219',base,'--baseline221',b221,'--output',out/'construction'])
        r['variants']={}
        for short,name in [('copy','no_push_copy'),('cache','no_push_cache')]:
            folder=out/'construction'/name
            phase('03_canonical_'+short,[ROOT/'portable/canonicalize.py','--variant',name,'--table',folder/'candidate.native.tm','--source',folder/'sites.json','--output',out/'canonical'/name])
            runtime=out/'runtime';runtime.mkdir(exist_ok=True)
            report=runtime/('runtime_'+short+'.json');cases=runtime/('runtime_'+short+'_cases.json')
            if args.quick:
                shutil.copy2(ROOT/'receipts'/report.name,report);shutil.copy2(ROOT/'receipts'/cases.name,cases)
            else:
                phase('04_fresh_runtime_'+short,[ROOT/'portable/verify_runtime.py','--baseline',b221,'--table',folder/'candidate.native.tm','--sites',folder/'sites.json','--output',report])
            verified=audit_runtime(report,cases,folder/'candidate.native.tm',folder/'sites.json',ROOT/'portable/verify_runtime.py')
            published=ROOT/'machine'/name
            for src,dst in [(folder/'candidate.native.tm',published/'candidate.native.tm'),(folder/'sites.json',published/'sites.json'),(out/'canonical'/name/'candidate.tm',published/'canonical/candidate.tm')]:
                need(src.read_bytes()==dst.read_bytes(),'Published artifact differs: '+str(dst))
            r['variants'][name]=verified;save()
        r['status']='QUICK_219_VARIANTS_REPLAY_PASS'if args.quick else'FRESH_219_VARIANTS_REPLAY_PASS'
        r['scope']='Exact 219-state tables/source, complete blank startup, and all-natural primitive interfaces. Written command/calculus calibration must also be read. No 218-state construction and no new proof-assistant kernel theorem.'
        save();print(r['status'],flush=True)
    except Exception as exc:
        r.update(status='FAILED',error=repr(exc));save();raise
if __name__=='__main__':main()
