#!/usr/bin/env python3
"""Offline reconstruction and verification of the exact U218 release.

Python 3.10+, standard library only. No synthesis solver or network is used.
All generated work is temporary, apart from an explicitly requested --report.
--full rederives every arbitrary-register symbolic primitive case. These are
executable mathematical checks; no new proof-assistant endpoint is claimed.
"""
from pathlib import Path, PurePosixPath
import argparse, collections, hashlib, json, os, stat, subprocess, sys, tempfile, time, zipfile
ROOT=Path(__file__).resolve().parent
sys.dont_write_bytecode=True
sys.path.insert(0,str(ROOT/'code'))
from build_u218 import build, K215_SHA256, U222_SHA256, SOURCE_SHA256, NATIVE_SHA256, DENSE_SHA256, PARENT_ARCHIVE_SHA256

def require(ok,why):
    if not ok:raise RuntimeError(why)

def sha(path):return hashlib.sha256(path.read_bytes()).hexdigest()
def load(path):return json.loads(path.read_text())

def command(script,args,cwd,label):
    print(label+' ...',flush=True)
    env=dict(os.environ,PYTHONDONTWRITEBYTECODE='1')
    p=subprocess.run([sys.executable,'-B',str(script),*map(str,args)],cwd=cwd,env=env,
                     stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
    if p.returncode:
        print(p.stdout,end='');raise RuntimeError(label+' failed: '+str(p.returncode))
    print(label+': PASS',flush=True)

def manifest_check():
    p=ROOT/'SHA256SUMS'
    require(p.is_file(),'Release manifest SHA256SUMS is missing')
    seen=set()
    for line in p.read_text().splitlines():
        if not line:continue
        digest,name=line.split('  ',1);rel=PurePosixPath(name)
        require(not rel.is_absolute()and '..'not in rel.parts and '\\'not in name,'Unsafe manifest path')
        require(name not in seen,'Duplicate manifest path');seen.add(name)
        require(sha(ROOT/name)==digest,'Hash mismatch: '+name)
    require({'machine/u218.native.tm','machine/u218.tm','machine/sites.json','inputs/U222_ConU_2026-10-28.zip',
             'inputs/k215.native.tm','inputs/source_recipe.json','inputs/table_recipe.json','paper/report.tex','paper/report.pdf','reproduce.py'}<=seen,'Manifest omits a principal deliverable')
    return {'status':'PASS','files_checked':len(seen)}

def extract_parent(dest):
    archive=ROOT/'inputs/U222_ConU_2026-10-28.zip'
    require(sha(archive)==PARENT_ARCHIVE_SHA256,'Wrong parent archive bytes')
    seen=set()
    with zipfile.ZipFile(archive)as z:
        for info in z.infolist():
            name=info.filename;rel=PurePosixPath(name)
            require(bool(rel.parts)and not rel.is_absolute()and '..'not in rel.parts and '\\'not in name,'Unsafe archive member')
            require(rel.parts[0]=='u222_consistency_machine','Unexpected archive root')
            require(name not in seen,'Duplicate archive member');seen.add(name)
            require(not stat.S_ISLNK((info.external_attr>>16)&0xffff),'Archive symlink rejected')
            p=dest.joinpath(*rel.parts)
            if info.is_dir():p.mkdir(parents=True,exist_ok=True)
            else:
                p.parent.mkdir(parents=True,exist_ok=True)
                with z.open(info)as src,p.open('wb')as out:
                    while True:
                        chunk=src.read(1048576)
                        if not chunk:break
                        out.write(chunk)
    parent=dest/'u222_consistency_machine'
    require((parent/'reproduce.py').is_file(),'Parent reproduction missing')
    return parent

def runtime_check(r,sites,parent):
    require(r['status']=='UNIVERSAL_MATHEMATICAL_PASS','Runtime proof failed')
    require(r['table_sha256']==NATIVE_SHA256 and r['sites_sha256']==SOURCE_SHA256,'Runtime binding differs')
    require(r['working_states']==218 and r['site_count']==len(sites)==3891,'Runtime census differs')
    expected=sum(2 if x[1]=='CD'else 1 for x in sites)
    require(r['expected_cases']==r['proved_cases']==expected==5060 and not r.get('failures'),'Incomplete runtime coverage')
    require(r['startup_status']=='CALIBRATED_DIRTY_ROOT_SEED','Uncalibrated runtime startup')
    require(r['checker_sha256']==sha(parent/'code/runtime/symbolic_runtime.py'),'Wrong symbolic checker')
    require(r['helper_sha256']==sha(parent/'code/runtime/independent_runtime.py'),'Wrong runtime helper')
    return expected

def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--full',action='store_true');p.add_argument('--report',type=Path);a=p.parse_args()
    began=time.monotonic();manifest=manifest_check();summary=load(ROOT/'machine/machine_summary.json');sites=load(ROOT/'machine/sites.json')
    with tempfile.TemporaryDirectory(prefix='u218-reproduce-')as name:
        tmp=Path(name);parent=extract_parent(tmp/'parent');candidate=tmp/'machine';candidate.mkdir()
        require(sha(ROOT/'inputs/k215.native.tm')==K215_SHA256 and (ROOT/'inputs/k215.native.tm').read_bytes()==(parent/'inputs/k215.native.tm').read_bytes(),'Pinned K215 input differs')
        require(sha(ROOT/'inputs/u222.native.tm')==U222_SHA256 and (ROOT/'inputs/u222.native.tm').read_bytes()==(parent/'machine/u.native.tm').read_bytes(),'Pinned U222 input differs')
        command(parent/'code/build_source.py',['--baseline',parent/'inputs/k215_sites.json','--recipe',ROOT/'inputs/source_recipe.json','--output',candidate/'sites.json'],tmp,'Exact 202-node source reconstruction')
        built=build(parent/'inputs/k215.native.tm',candidate/'sites.json',ROOT/'inputs/table_recipe.json',candidate)
        require(built==summary,'Machine summary differs')
        require(load(candidate/'table_deltas.json')==load(ROOT/'evidence/table_deltas.json'),'Literal stage deltas differ')
        for f in('u218.native.tm','u218.tm','sites.json','state_map.json','machine_summary.json'):
            require((candidate/f).read_bytes()==(ROOT/'machine'/f).read_bytes(),'Exact reconstruction differs: '+f)
        for f in('provisional219.native.tm','repaired220.native.tm','tagged219.native.tm','untagged219.native.tm'):
            require((candidate/f).read_bytes()==(ROOT/'inputs'/f).read_bytes(),'Intermediate reconstruction differs: '+f)
        command(ROOT/'code/check_commuted_source.py',[parent/'inputs/k215_sites.json',parent/'machine/sites.json',candidate/'sites.json',ROOT/'inputs/source_recipe.json','--output',tmp/'source_audit.json'],tmp,'Independent source syntax and control-flow audit')
        require(load(tmp/'source_audit.json')==load(ROOT/'evidence/source_audit.json'),'Source audit differs')
        jobs=[
          ('check_rejected_counterexample.py',[candidate/'provisional219.native.tm',candidate/'sites.json','--output',tmp/'counterexample.json'],'counterexample.json','provisional219_counterexample.json','Concrete rejected-table primitive counterexample'),
          ('check_routing_split.py',[candidate/'provisional219.native.tm',candidate/'repaired220.native.tm',candidate/'sites.json','--output',tmp/'routing.json'],'routing.json','routing_split.json','Three-row routing repair audit'),
          ('verify_guarded_folds.py',[candidate/'repaired220.native.tm',candidate/'tagged219.native.tm',candidate/'u218.native.tm',tmp/'guarded.json'],'guarded.json','guarded_folds.json','Combined guarded folds and four controls'),
          ('check_zero_fold.py',[candidate/'repaired220.native.tm',candidate/'untagged219.native.tm','--output',tmp/'zero1.json'],'zero1.json','zero_fold_220_219.json','Independent known-zero fold 220 to 219'),
          ('check_zero_fold.py',[candidate/'tagged219.native.tm',candidate/'u218.native.tm','--output',tmp/'zero2.json'],'zero2.json','zero_fold_219_218.json','Independent known-zero fold 219 to 218'),
          ('check_tagged_fold.py',[candidate/'untagged219.native.tm',candidate/'u218.native.tm','--output',tmp/'tagged.json'],'tagged.json','tagged_fold_independent.json','Independent exhaustive tag invariant and stuttering proof'),
          ('check_zero_fold_controls.py',[candidate/'tagged219.native.tm',candidate/'u218.native.tm','--output',tmp/'controls.json'],'controls.json','zero_fold_controls.json','Eleven independent known-zero negative controls'),
          ('check_tagged_fold_controls.py',[candidate/'untagged219.native.tm',candidate/'u218.native.tm','--output',tmp/'tagcontrols.json'],'tagcontrols.json','tagged_fold_controls.json','Ten independent tag-fold negative controls')]
        for script,params,temporary,published,label in jobs:
            command(ROOT/'code'/script,params,tmp,label)
            require(load(tmp/temporary)==load(ROOT/'evidence'/published),'Certificate differs: '+published)
        # The rejected provisional table is preserved as a failed construction,
        # and cannot silently acquire the final machine's acceptance status.
        failure=load(ROOT/'evidence/provisional219_runtime_failure.json')
        require(failure['status']=='NOT_PROVED'and failure['table_sha256']==sha(candidate/'provisional219.native.tm')and failure['sites_sha256']==SOURCE_SHA256,'Rejected-stage record differs')
        require(failure['proved_cases']==3901 and failure['failures'][0]['site_index']==3004,'Rejected-stage counterexample location differs')
        command(parent/'reproduce.py',['--report',tmp/'parent.json'],parent,'Inherited U222 source and bootstrap audit')
        old=load(tmp/'parent.json');require(old['status']=='U222_RECONSTRUCTION_AUDIT_PASS'and old['native_sha256']==U222_SHA256,'Inherited audit failed')
        command(parent/'code/review_native_bootstrap.py',['--table',candidate/'u218.native.tm','--sites',candidate/'sites.json','--startup',ROOT/'evidence/startup.json','--out',tmp/'bootstrap.json'],tmp,'Independent literal U218 blank startup')
        bootstrap=load(tmp/'bootstrap.json');require(bootstrap==load(ROOT/'evidence/bootstrap_independent.json'),'Independent bootstrap differs')
        require(bootstrap['working_states']==bootstrap['graph_reachable_working_states']==218 and bootstrap['startup_steps']==95726,'Wrong startup census')
        require(bootstrap['startup_registers']==[4,0,0,0,0,0,0,0,0]and bootstrap['startup_gap']==1 and bootstrap['spare_count']==40 and bootstrap['spare_values']=={'1':40},'Wrong enumeration seed')
        saved=load(ROOT/'evidence/runtime.json');n=runtime_check(saved,sites,parent);cases=load(ROOT/'evidence/runtime_cases.json')
        expected={(i,b)for i,x in enumerate(sites)for b in((False,True)if x[1]=='CD'else(False,))}
        require(len(cases)==n and{(x['site_index'],x['positive'])for x in cases}==expected,'Saved case coverage differs')
        if a.full:
            command(parent/'code/validate_native.py',[candidate/'u218.native.tm',candidate/'sites.json',tmp/'runtime'],tmp,'All 5060 arbitrary-register symbolic cases')
            full=load(tmp/'runtime/runtime.json');runtime_check(full,sites,parent)
            require(load(tmp/'runtime/runtime_cases.json')==cases,'Regenerated symbolic case records differ')
            require(load(tmp/'runtime/startup.json')==load(ROOT/'evidence/startup.json'),'Regenerated literal startup differs')
            require(full['blocks']==saved['blocks'],'Regenerated block lemmas differ')
        result={'status':'U218_FULL_REPRODUCTION_PASS'if a.full else'U218_RECONSTRUCTION_AND_PROOF_AUDIT_PASS',
          'manifest':manifest,'working_states':218,'transition_rows':436,'source_occurrences':3891,'source_dag_nodes':202,
          'source_operations':dict(collections.Counter(x[1]for x in sites)),
          'exact_native_dense_source_and_stages_reconstructed':True,'independent_source_CFG_audit':True,
          'routing_prefixes_checked':3891,'routing_entries_repaired':4,'concrete_rejected_stage_counterexample':True,'guarded_folds_checked':True,
          'independent_zero_and_tag_certificates_checked':True,'negative_controls_rejected':25,
          'inherited_U222_source_and_bootstrap_audit':True,'independent_U218_blank_replay':True,
          'startup_steps':95726,'symbolic_cases_checked':n,'symbolic_cases_rerun':a.full,
          'native_sha256':NATIVE_SHA256,'dense_sha256':DENSE_SHA256,'source_sha256':SOURCE_SHA256,
          'parent_archive_sha256':PARENT_ARCHIVE_SHA256,'seconds':round(time.monotonic()-began,3),
          'scope':'Exact reconstruction and executable mathematical verification; source-equivalence proof and consistency transport are in the report. No new proof-assistant kernel theorem of the complete U218 endpoint.'}
    if a.report:
        a.report.parent.mkdir(parents=True,exist_ok=True);a.report.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))
if __name__=='__main__':main()
