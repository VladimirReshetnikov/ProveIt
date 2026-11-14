#!/usr/bin/env python3
"""Offline exact reconstruction and mathematical certificate replay.
Python 3.10+, standard library only. --full rederives all symbolic cases.
No new proof-assistant kernel certificate of the consistency endpoint is claimed.
"""
from pathlib import Path,PurePosixPath
import argparse,hashlib,json,os,stat,subprocess,sys,tempfile,time,zipfile
ROOT=Path(__file__).resolve().parent
sys.dont_write_bytecode=True
sys.path.insert(0,str(ROOT/'code'))
from build_machines import build,sha,need

def load(p):return json.loads(p.read_text())
def command(script,args,work,label):
    print(label+' ...',flush=True)
    env=dict(os.environ,PYTHONDONTWRITEBYTECODE='1');env.pop('PYTHONOPTIMIZE',None)
    result=subprocess.run([sys.executable,'-B',str(script),*map(str,args)],cwd=work,env=env,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
    if result.returncode:
        print(result.stdout,end='');raise RuntimeError(label+' failed')
    print(label+': PASS',flush=True)

def manifest():
    seen=set()
    for line in (ROOT/'SHA256SUMS').read_text().splitlines():
        digest,name=line.split('  ',1);p=PurePosixPath(name)
        need(not p.is_absolute()and '..'not in p.parts and '\\'not in name,'unsafe manifest path')
        need(name not in seen,'duplicate manifest member');seen.add(name)
        need(sha(ROOT/name)==digest,'digest mismatch: '+name)
    need({'paper/report.tex','paper/report.pdf','machine/u214.tm','machine/u214.native.tm','machine/sites.json','reproduce.py','inputs/U218_ConPA_2026-10-28.zip'}<=seen,'principal files omitted')
    return len(seen)

def safe_extract(archive,dest):
    with zipfile.ZipFile(archive)as z:
        seen=set()
        for info in z.infolist():
            p=PurePosixPath(info.filename)
            need(not p.is_absolute()and '..'not in p.parts and '\\'not in info.filename,'unsafe archive path')
            need(info.filename not in seen and not stat.S_ISLNK((info.external_attr>>16)&0xffff),'duplicate member or symlink')
            seen.add(info.filename);target=dest.joinpath(*p.parts)
            if info.is_dir():target.mkdir(parents=True,exist_ok=True)
            else:
                target.parent.mkdir(parents=True,exist_ok=True)
                with z.open(info)as src,target.open('wb')as dst:
                    while True:
                        data=src.read(1048576)
                        if not data:break
                        dst.write(data)

def runtime_audit(table,source,folder,count,cases_expected):
    summary=load(folder/'runtime.json');cases=load(folder/'runtime_cases.json');sites=load(source)
    need(summary['status']=='UNIVERSAL_MATHEMATICAL_PASS'and not summary['failures'],'runtime not proved')
    need(summary['working_states']==count and summary['table_sha256']==sha(table)and summary['sites_sha256']==sha(source),'runtime binding differs')
    need(summary['checker_sha256']==sha(ROOT/'code/runtime/symbolic_runtime.py')and summary['helper_sha256']==sha(ROOT/'code/runtime/independent_runtime.py'),'runtime checker bytes differ')
    need(summary['proved_cases']==summary['expected_cases']==len(cases)==cases_expected,'incomplete runtime census')
    expected={(i,b)for i,x in enumerate(sites)for b in((False,True)if x[1]=='CD'else(False,))}
    need({(x['site_index'],x['positive'])for x in cases}==expected and len(expected)==cases_expected,'missing/duplicate symbolic case')
    need(summary['startup_status']=='CALIBRATED_DIRTY_ROOT_SEED','uncalibrated startup')
    return summary

def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--full',action='store_true');p.add_argument('--report',type=Path);a=p.parse_args();began=time.monotonic();files=manifest()
    with tempfile.TemporaryDirectory(prefix='u214-replay-')as name:
        temp=Path(name);out=temp/'build';out.mkdir()
        command(ROOT/'code/build_source.py',['--baseline',ROOT/'inputs/k215_sites.json','--recipe',ROOT/'inputs/source_recipe.json','--output',out/'sites.json'],temp,'Reconstruct 198-subtree source')
        need((out/'sites.json').read_bytes()==(ROOT/'machine/sites.json').read_bytes(),'source reconstruction differs')
        construction=build(ROOT/'inputs/u218.native.tm',out/'sites.json',ROOT/'inputs/table_recipe.json',out)
        for f in['u214.native.tm','u214.tm','u214_state_map.json','u217_reentry.native.tm','u217_reentry.tm','u217_state_map.json']:
            need((out/f).read_bytes()==(ROOT/'machine'/f).read_bytes(),'machine reconstruction differs: '+f)
        need((out/'role215.native.tm').read_bytes()==(ROOT/'inputs/role215.native.tm').read_bytes(),'intermediate reconstruction differs')
        jobs=[
          ('audit_role_source.py',[out/'sites.json',ROOT/'inputs/u218_sites.json',ROOT/'inputs/k215_sites.json',ROOT/'inputs/tokens.json'],'source_audit.json','Exact emitter/exterior source audit'),
          ('bind_role_macros.py',[ROOT/'inputs/k215_sites.json',ROOT/'inputs/DagPerm.v'],'macro_bindings.json','All seven arithmetic proof-node bindings'),
          ('check_fold214_exhaustive.py',[out/'role215.native.tm',out/'u214.native.tm'],'fold214_exhaustive.json','Exhaustive 215 to 214 local proof and controls'),
          ('check_fold214_independent.py',[out/'role215.native.tm',out/'u214.native.tm'],'fold214_independent.json','Independent opaque-exterior 214 proof and controls'),
          ('check_reentry217.py',[ROOT/'inputs/u218.native.tm',out/'u217_reentry.native.tm'],'reentry217.json','Three-case direct 218 to 217 proof'),
          ('check_reentry217_independent.py',[ROOT/'inputs/u218.native.tm',out/'u217_reentry.native.tm'],'reentry217_independent.json','Independent exhaustive 217 local proof')]
        for script,args,receipt,label in jobs:
            command(ROOT/'code'/script,[*args,'--output',temp/receipt],temp,label)
            need(load(temp/receipt)==load(ROOT/'evidence'/receipt),'certificate replay differs: '+receipt)
        native=[('u214',out/'u214.native.tm',out/'sites.json',214,5109),('u217',out/'u217_reentry.native.tm',ROOT/'inputs/u218_sites.json',217,5060),('role215',out/'role215.native.tm',out/'sites.json',215,5109)]
        for label,table,source,count,total in native:
            saved=runtime_audit(table,source,ROOT/'evidence'/label,count,total)
            command(ROOT/'code/review_native_bootstrap.py',['--table',table,'--sites',source,'--startup',ROOT/'evidence'/label/'startup.json','--out',temp/(label+'_bootstrap.json')],temp,'Independent blank startup '+label)
            boot=load(temp/(label+'_bootstrap.json'))
            need(boot['working_states']==boot['graph_reachable_working_states']==count,'graph census differs')
            need(boot['startup_steps']==95726 and boot['startup_registers']==[4,0,0,0,0,0,0,0,0]and boot['startup_gap']==1 and boot['spare_count']==40,'startup frame differs')
            if a.full and label in('u214','u217'):
                fresh=temp/('runtime_'+label)
                command(ROOT/'code/validate_native.py',[table,source,fresh],temp,'Rederive all '+str(total)+' arbitrary-register cases for '+label)
                actual=runtime_audit(table,source,fresh,count,total)
                need(actual['blocks']==saved['blocks'],'block induction certificate differs')
                need(load(fresh/'runtime_cases.json')==load(ROOT/'evidence'/label/'runtime_cases.json'),'symbolic case records differ')
                need(load(fresh/'startup.json')==load(ROOT/'evidence'/label/'startup.json'),'literal startup trace differs')
        # Pin the complete primary predecessor, then replay its inexpensive audit.
        archive=ROOT/'inputs/U218_ConPA_2026-10-28.zip'
        need(sha(archive)=='73c7d0774d955c9b003eec0e9e0876e280f028f653a127c7518d132b914c8bc9','parent archive differs')
        safe_extract(archive,temp/'parent');parent=temp/'parent/U218_ConPA_2026-10-28'
        need((parent/'machine/u218.native.tm').read_bytes()==(ROOT/'inputs/u218.native.tm').read_bytes(),'parent native bytes differ')
        need((parent/'machine/sites.json').read_bytes()==(ROOT/'inputs/u218_sites.json').read_bytes(),'parent source bytes differ')
        command(parent/'reproduce.py',['--report',temp/'parent_replay.json'],parent,'Inherited U218 reconstruction and proof audit')
        need(load(temp/'parent_replay.json')['status']=='U218_RECONSTRUCTION_AND_PROOF_AUDIT_PASS','parent audit failed')
        report={'status':'U214_FULL_REPRODUCTION_PASS'if a.full else'U214_RECONSTRUCTION_AND_PROOF_AUDIT_PASS','manifest_files':files,'construction':construction,'source_dag_nodes':198,'source_occurrences':3928,'source_and_macro_audits':True,'both_independent_214_fold_checks':True,'both_independent_217_reentry_checks':True,'symbolic_cases_primary':5109,'symbolic_cases_companion':5060,'symbolic_cases_rederived':10169 if a.full else 0,'primary_startup_steps':95726,'companion_startup_steps':95726,'inherited_U218_audit':True,'seconds':round(time.monotonic()-began,3),'scope':'Exact reconstruction, full finite local proofs, and whole-tape symbolic mathematical verification. Ordinary logical proof translations and inherited U/W/PA interpretations are stated in the paper. No newly compiled Lean, Rocq, MM0, or exported PA endpoint certificate.'}
    if a.report:a.report.parent.mkdir(parents=True,exist_ok=True);a.report.write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))
if __name__=='__main__':main()
