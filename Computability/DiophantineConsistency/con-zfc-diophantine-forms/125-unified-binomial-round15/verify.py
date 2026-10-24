#!/usr/bin/env python3
"""Offline finite replay; explicit checks remain active under python -O.
Requires Python 3.10+ and SymPy. No network or original workspace is used.
Builders run only in a new temporary copy. Unbounded proofs and inherited
calibration are not claimed to be established by these finite checks.
"""
from pathlib import Path
import argparse,hashlib,json,os,shutil,subprocess,sys,tempfile,time
ROOT=Path(__file__).resolve().parent

def require(ok,message):
    if not ok:raise ValueError(message)
def digest(path):return hashlib.sha256(path.read_bytes()).hexdigest()
def main():
    ap=argparse.ArgumentParser();ap.add_argument('--report',type=Path);ap.add_argument('--mode',choices=['both','normal','optimized'],default='both');a=ap.parse_args()
    begin=time.monotonic();r={'status':'RUNNING','scope':'Finite exact algebra, source binding, negative controls and byte-exact reconstruction; not a proof of Con(ZFC) or a new kernel calibration.','python':sys.version.split()[0],'mode':a.mode,'checks':[],'byte_equalities':[]}
    files=json.loads((ROOT/'MANIFEST_SHA256.json').read_text())['files']
    for name,record in files.items():
        path=ROOT/name;require(path.is_file(),'Missing manifest file: '+name)
        require(path.stat().st_size==record['bytes'] and digest(path)==record['sha256'],'Manifest mismatch: '+name)
    r['manifest_files']=len(files)
    modes=[False,True] if a.mode=='both' else [a.mode=='optimized']
    with tempfile.TemporaryDirectory(prefix='conzfc_round15_') as td:
        temp=Path(td);work=temp/'packet';shutil.copytree(ROOT,work,ignore=shutil.ignore_patterns('__pycache__','*.pyc'))
        out=temp/'outputs';out.mkdir()
        env=os.environ.copy();env.update(PYTHONDONTWRITEBYTECODE='1',PYTHONHASHSEED='0',PYTHONPATH='')
        def run(label,args,opt=False):
            cmd=[sys.executable]+(['-O'] if opt else [])+[str(x) for x in args]
            start=time.monotonic();p=subprocess.run(cmd,cwd=work,env=env,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
            require(p.returncode==0,label+' failed:\n'+p.stdout[-20000:])
            r['checks'].append({'name':label,'optimized':opt,'exit_code':0,'seconds':round(time.monotonic()-start,3),'stdout_sha256':hashlib.sha256(p.stdout.encode()).hexdigest()})
            print('PASS '+label+(' [-O]' if opt else ''),flush=True);return p.stdout
        def same(actual,expected,label):
            require(actual.is_file() and expected.is_file(),'Missing rebuilt file: '+label)
            require(actual.read_bytes()==expected.read_bytes(),'Byte-different rebuilt file: '+label)
            r['byte_equalities'].append({'artifact':label,'sha256':digest(actual),'bytes':actual.stat().st_size})
        # Run the inherited finite recipe in its supported checked mode only.
        run('all six coefficient recipes',['scalar/verify_coefficients.py'])
        r['coefficient_recipe_ports_rebuilt']=6
        r['recipe_mode']='Checked normal Python once; independent payload checks run in every selected mode.'
        for opt in modes:
            tag='optimized' if opt else 'normal';o=out/tag;o.mkdir()
            run('scalar semantic regressions',['scalar/verify_semantics.py','--output',o/'semantics.json'],opt)
            run('fixed-pair interpolation controls',['scalar_audit/check_interpolation.py'],opt)
            run('baseline norm rebuild',['norm/build_norm.py'],opt)
            for name in ['integral_direct','integral_centered','integral_centered_expandedcut','integral_direct_paired','integral_centered_paired']:
                same(work/'norm'/(name+'.json'),ROOT/'norm'/(name+'.json'),'norm/'+name+' '+tag)
            run('baseline norm degree and identities',['norm/check_norm.py'],opt)
            run('independent baseline register cuts',['scalar_audit/independent_audit.py','--out',o/'scalar-audit.json'],opt)
            run('split carrier norm rebuild',['norm_weak/build_norm.py'],opt)
            for name in ['weak_integral_direct_paired','weak_integral_centered_paired']:
                same(work/'norm_weak'/(name+'.json'),ROOT/'norm_weak'/(name+'.json'),'norm_weak/'+name+' '+tag)
            run('split carrier degree and identities',['norm_weak/check_norm.py'],opt)
            run('independent split carrier register cuts',['scalar_audit/audit_crt_graphs.py','--out',o/'crt-audit.json'],opt)
            run('architecture literal and semantic controls',['architecture/check_unified_product.py','--output',o/'architecture-check.json'],opt)
            run('six architecture reconstructions',['architecture/reproduce_unified_product.py','--output',o/'architecture-replay.json'],opt)
            ar=json.loads((o/'architecture-replay.json').read_text());require(ar['verified'] and len(ar['variants'])==6,'Architecture replay coverage')
            for name,item in ar['variants'].items():
                require(item['files_identical']==12,'Architecture rebuild inventory')
                r['byte_equalities'].extend({'artifact':'architecture/'+name+'/'+str(i)+' '+tag,'scope':'Exact file equality checked by architecture reproducer'} for i in range(item['files_identical']))
            stages=o/'signed-stages';final=o/'integer442'
            run('selectively even signed compiler',['direct/build_residue.py','architecture/unified_derived_shell/raw',stages,'--reparam'],opt)
            for f in (ROOT/'direct/unified_reparam_derived_shell').glob('*.json'):
                same(stages/f.name,f,'direct/unified_reparam_derived_shell/'+f.name+' '+tag)
            run('integer 442 centering',['direct/center_integer.py',stages,final],opt)
            for f in (ROOT/'direct/integer442').glob('*.json'):
                same(final/f.name,f,'direct/integer442/'+f.name+' '+tag)
            run('independent direct and six natural certificates',['direct_audit/check_direct.py','--variant','unified_reparam_derived_shell','--raw','unified_derived_shell','--endpoint','integer442','--output',o/'direct-audit.json'],opt)
            run('independent reported endpoint metrics',['report_audit/check_report_metrics.py'],opt)
            run('incoming literal payload review',['review/replay_incoming.py','--output',o/'incoming.json'],opt)
        r.update(status='PASS',temporary_copy_replay=True,commands_passed=len(r['checks']),byte_equalities_passed=len(r['byte_equalities']),elapsed_seconds=round(time.monotonic()-begin,3))
    text=json.dumps(r,indent=2)+'\n'
    if a.report:a.report.parent.mkdir(parents=True,exist_ok=True);a.report.write_text(text)
    print(text)
if __name__=='__main__':main()
