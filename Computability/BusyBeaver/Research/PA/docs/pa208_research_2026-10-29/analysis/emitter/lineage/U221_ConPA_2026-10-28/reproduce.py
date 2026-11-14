#!/usr/bin/env python3
"""Offline U221 reproduction and independent reduction checks.

Python 3.10+, standard library only. All generated work stays in a temporary
folder. --full repeats every arbitrary-register symbolic proof case; it is
not a proof-assistant kernel invocation. --report writes only the requested
receipt. The exact parent U222 archive is included and re-audited offline.
"""
from pathlib import Path, PurePosixPath
import argparse, collections, hashlib, json, os, stat, subprocess, sys, tempfile, time, zipfile

ROOT=Path(__file__).resolve().parent
sys.dont_write_bytecode=True
sys.path.insert(0,str(ROOT/'code'))
from build_u221 import build, PARENT_ARCHIVE_SHA256, U222_SHA256, SOURCE_SHA256, U221_NATIVE_SHA256

def require(ok,why):
    if not ok:raise RuntimeError(why)

def sha(path):return hashlib.sha256(path.read_bytes()).hexdigest()

def load(path):return json.loads(path.read_text())

def command(script,args,cwd,label):
    env=dict(os.environ,PYTHONDONTWRITEBYTECODE='1')
    print(label+' ...',flush=True)
    p=subprocess.run([sys.executable,'-B',str(script),*map(str,args)],cwd=cwd,env=env,
                     stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
    if p.returncode:
        print(p.stdout,end='');raise RuntimeError(label+' failed with exit '+str(p.returncode))
    print(label+': PASS',flush=True)
    return p.stdout

def manifest_check():
    p=ROOT/'SHA256SUMS'
    require(p.is_file(),'Missing release SHA256SUMS manifest')
    seen=set()
    for line in p.read_text().splitlines():
        if not line:continue
        digest,name=line.split('  ',1);rel=PurePosixPath(name)
        require(not rel.is_absolute() and '..'not in rel.parts and '\\'not in name,'Unsafe manifest path')
        require(name not in seen,'Repeated manifest path');seen.add(name)
        require(sha(ROOT/name)==digest,'Hash mismatch: '+name)
    require({'machine/u221.native.tm','machine/u221.tm','machine/sites.json',
             'inputs/U222_ConU_2026-10-28.zip','inputs/u222.native.tm','reproduce.py',
             'paper/report.tex','paper/report.pdf'}<=seen,'Manifest omits a principal deliverable')
    return {'status':'PASS','files_checked':len(seen)}

def extract_parent(archive,dest):
    require(sha(archive)==PARENT_ARCHIVE_SHA256,'Wrong parent archive bytes')
    seen=set()
    with zipfile.ZipFile(archive) as z:
        for info in z.infolist():
            name=info.filename;rel=PurePosixPath(name)
            require(bool(rel.parts) and not rel.is_absolute() and '..'not in rel.parts and '\\'not in name,'Unsafe archive path')
            require(rel.parts[0]=='u222_consistency_machine','Unexpected parent root')
            require(name not in seen,'Duplicate ZIP member');seen.add(name)
            mode=(info.external_attr>>16)&0xffff
            require(not stat.S_ISLNK(mode),'Archive symlink not allowed')
            target=dest.joinpath(*rel.parts)
            if info.is_dir():target.mkdir(parents=True,exist_ok=True)
            else:
                target.parent.mkdir(parents=True,exist_ok=True)
                with z.open(info) as source,target.open('wb') as output:
                    while True:
                        chunk=source.read(1048576)
                        if not chunk:break
                        output.write(chunk)
    parent=dest/'u222_consistency_machine'
    require((parent/'reproduce.py').is_file(),'Missing parent reproduction')
    return parent

def runtime_check(report,sites,parent,summary):
    expected=sum(2 if x[1]=='CD' else 1 for x in sites)
    require(report['status']=='UNIVERSAL_MATHEMATICAL_PASS','Runtime status failed')
    require(report['table_sha256']==summary['native_sha256']==U221_NATIVE_SHA256,'Runtime table differs')
    require(report['sites_sha256']==summary['source_sha256']==SOURCE_SHA256,'Runtime source differs')
    require(report['working_states']==221 and report['site_count']==len(sites)==3891,'Runtime census differs')
    require(report['expected_cases']==report['proved_cases']==expected==5060,'Runtime coverage incomplete')
    require(not report.get('failures'),'Runtime failures present')
    require(report['startup_status']=='CALIBRATED_DIRTY_ROOT_SEED','Wrong runtime bootstrap status')
    require(report['checker_sha256']==sha(parent/'code/runtime/symbolic_runtime.py'),'Runtime checker differs')
    require(report['helper_sha256']==sha(parent/'code/runtime/independent_runtime.py'),'Runtime helper differs')
    return expected

def bootstrap_lockstep(old,new):
    require(old['steps']==new['steps']==95714,'Wrong bootstrap length')
    require(len(old['trace'])==len(new['trace'])==95714,'Wrong bootstrap trace length')
    rho=lambda q:209 if q==200 else q
    visits=0
    for x,y in zip(old['trace'],new['trace']):
        q,h,b,w,d,z=x;require(y==[rho(q),h,b,w,d,rho(z)],'Bootstrap lockstep differs');visits+=q==200
    for key in ('state','head','one_cells','registers','spares','gap'):
        require(old[key]==new[key],'Bootstrap frame differs: '+key)
    return {'status':'PASS','steps':95714,'old_state_200_visits':visits,
            'same_head':True,'same_tape':True,'same_registers':True}

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--full',action='store_true',help='Rerun all 5,060 arbitrary-register symbolic cases')
    ap.add_argument('--report',type=Path,help='Write the final receipt at this explicit path')
    args=ap.parse_args();started=time.monotonic();manifest=manifest_check()
    summary=load(ROOT/'machine/machine_summary.json');sites=load(ROOT/'machine/sites.json')
    require(sha(ROOT/'inputs/u222.native.tm')==U222_SHA256,'Convenience baseline differs')
    with tempfile.TemporaryDirectory(prefix='u221-reproduce-') as folder:
        tmp=Path(folder);parent=extract_parent(ROOT/'inputs/U222_ConU_2026-10-28.zip',tmp/'parent')
        require((parent/'machine/u.native.tm').read_bytes()==(ROOT/'inputs/u222.native.tm').read_bytes(),'Parent baseline mismatch')
        generated=tmp/'machine'
        rebuilt=build(parent/'machine/u.native.tm',parent/'machine/sites.json',generated)
        for name in ('u221.native.tm','u221.tm','sites.json','state_map.json','machine_summary.json'):
            require((generated/name).read_bytes()==(ROOT/'machine'/name).read_bytes(),'Reconstruction differs: '+name)
        require(rebuilt==summary,'Summary differs')
        old=parent/'machine/u.native.tm';new=generated/'u221.native.tm'
        steps=[
          ('certify_u221.py',[old,tmp/'lockstep.json','--candidate',new],'lockstep.json','u221_lockstep_certificate.json','Source-independent lockstep certificate'),
          ('check_fold_invariant.py',[old,new,'--output',tmp/'local.json'],'local.json','fold_invariant.json','Independent exhaustive local invariant'),
          ('check_fold_negative_controls.py',[old,new,'--output',tmp/'controls.json'],'controls.json','fold_negative_controls.json','Eleven negative controls'),
          ('analyze_local_folds.py',[old,new,'--output',tmp/'search.json'],'search.json','local_search.json','Finite local search scope')]
        for script,params,temporary,published,label in steps:
            command(ROOT/'code'/script,params,tmp,label)
            require(load(tmp/temporary)==load(ROOT/'evidence'/published),'Saved certificate differs: '+published)
        command(parent/'reproduce.py',['--report',tmp/'parent_receipt.json'],parent,'Inherited U222 source and bootstrap audit')
        parent_receipt=load(tmp/'parent_receipt.json')
        require(parent_receipt['status']=='U222_RECONSTRUCTION_AUDIT_PASS','Parent audit failed')
        require(parent_receipt['native_sha256']==U222_SHA256 and parent_receipt['source_sha256']==SOURCE_SHA256,'Parent audit binding differs')
        command(ROOT/'experimental/source202/reproduce_source.py',
                ['--output',tmp/'source202.json'],tmp,'Supplementary 202-node source audit')
        source202=load(tmp/'source202.json')
        require(source202['status']=='EXACT_SOURCE_RECONSTRUCTION_AND_INDEPENDENT_AUDIT_PASS'
                and source202['metrics']['dag_nodes']==202,'Supplementary source audit failed')
        startup=load(ROOT/'evidence/startup.json')
        lockstep=bootstrap_lockstep(load(parent/'evidence/startup.json'),startup)
        require(lockstep==load(ROOT/'evidence/bootstrap_lockstep.json'),'Published startup correspondence differs')
        command(parent/'code/review_native_bootstrap.py',
                ['--table',new,'--sites',generated/'sites.json','--startup',ROOT/'evidence/startup.json','--out',tmp/'bootstrap.json'],
                tmp,'Independent literal U221 bootstrap replay')
        bootstrap=load(tmp/'bootstrap.json')
        require(bootstrap['status']=='INDEPENDENT_LITERAL_STARTUP_PASS' and bootstrap['working_states']==221 and bootstrap['startup_steps']==95714,'New bootstrap audit failed')
        require(bootstrap['table_sha256']==summary['native_sha256'] and bootstrap['sites_sha256']==summary['source_sha256'],'New bootstrap binding differs')
        saved=load(ROOT/'evidence/runtime.json');cases=runtime_check(saved,sites,parent,summary)
        published_cases=load(ROOT/'evidence/runtime_cases.json')
        expected_pairs={(i,positive)for i,x in enumerate(sites)for positive in((False,True)if x[1]=='CD'else(False,))}
        require(len(published_cases)==cases and {(x['site_index'],x['positive'])for x in published_cases}==expected_pairs,'Saved case enumeration differs')
        if args.full:
            command(parent/'code/validate_native.py',[new,generated/'sites.json',tmp/'runtime'],tmp,'All arbitrary-register symbolic cases')
            full=load(tmp/'runtime/runtime.json');runtime_check(full,sites,parent,summary)
            require(load(tmp/'runtime/runtime_cases.json')==published_cases,'Regenerated symbolic cases differ')
            require(load(tmp/'runtime/startup.json')==startup,'Regenerated startup differs')
            require(full['blocks']==saved['blocks'],'Regenerated block lemmas differ')
        report={
          'status':'U221_FULL_REPRODUCTION_PASS'if args.full else'U221_RECONSTRUCTION_AND_PROOF_AUDIT_PASS',
          'manifest':manifest,'working_states':221,'transition_rows':442,'source_occurrences':len(sites),
          'source_operations':dict(collections.Counter(x[1]for x in sites)),
          'exact_source_and_tables_reconstructed':True,'native_dense_bijection_checked':True,
          'source_independent_lockstep_certificate':True,'independent_local_invariant_certificate':True,
          'negative_controls_rejected':11,'inherited_U222_reconstruction_and_source_audit':True,
          'supplementary_202_node_source_audit':True,
          'independent_literal_U221_bootstrap_replayed':True,'startup_steps':95714,
          'saved_symbolic_cases_checked':cases,'all_symbolic_cases_rerun':args.full,
          'native_sha256':summary['native_sha256'],'dense_sha256':summary['dense_sha256'],
          'source_sha256':summary['source_sha256'],'parent_archive_sha256':PARENT_ARCHIVE_SHA256,
          'seconds':round(time.monotonic()-started,3),
          'scope':'Exact reconstruction; a finite inductive proof of U222/U221 lockstep equivalence; inherited U222 source and bootstrap audit; optional arbitrary-register symbolic rederivation. No new proof-assistant kernel endpoint.'}
    if args.report:
        args.report.parent.mkdir(parents=True,exist_ok=True)
        args.report.write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))
if __name__=='__main__':main()
