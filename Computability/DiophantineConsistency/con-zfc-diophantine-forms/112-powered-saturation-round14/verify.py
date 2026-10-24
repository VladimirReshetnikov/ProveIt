#!/usr/bin/env python3
"""Offline round14 replay. Explicit checks remain active under python -O.

Requires Python 3.10+ and SymPy for the independent scalar resultant audit.
No network, original workspace, or installed ProveIt checkout is used.
All builders and mutating checkers run only inside a fresh temporary copy.
"""
from pathlib import Path
import argparse, gzip, hashlib, json, os, shutil, subprocess, sys, tempfile, time
ROOT=Path(__file__).resolve().parent

def require(test,message):
    if not test: raise ValueError(message)
def digest(path): return hashlib.sha256(path.read_bytes()).hexdigest()
def main():
    p=argparse.ArgumentParser();p.add_argument('--report',type=Path);p.add_argument('--mode',choices=['both','normal','optimized'],default='both');a=p.parse_args()
    start=time.monotonic();report={'status':'RUNNING','scope':'Exact finite algebra, source binding, negative controls, and deterministic reconstruction; not a proof of inherited calibration or Con(ZFC).','python':sys.version.split()[0],'mode':a.mode,'checks':[],'byte_equalities':[]}
    m=json.loads((ROOT/'MANIFEST_SHA256.json').read_text())['files']
    for relative,data in m.items():
        f=ROOT/relative
        require(f.is_file(), 'missing manifest file: '+relative)
        require(f.stat().st_size==data['bytes'] and digest(f)==data['sha256'],'manifest mismatch: '+relative)
    report['manifest_files']=len(m)
    modes=[False,True] if a.mode=='both' else [a.mode=='optimized']
    with tempfile.TemporaryDirectory(prefix='conzfc_round14_') as td:
        work=Path(td)/'packet';shutil.copytree(ROOT,work,ignore=shutil.ignore_patterns('__pycache__','*.pyc'))
        out=Path(td)/'outputs';out.mkdir()
        env=os.environ.copy();env['PYTHONDONTWRITEBYTECODE']='1';env['PYTHONPATH']='';env['PYTHONHASHSEED']='0'
        def run(label,args,opt=False):
            cmd=[sys.executable]+(['-O'] if opt else [])+[str(x) for x in args]
            t=time.monotonic();r=subprocess.run(cmd,cwd=work,env=env,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
            require(r.returncode==0,label+' failed:\n'+r.stdout[-12000:])
            report['checks'].append({'name':label,'optimized':opt,'exit_code':r.returncode,'seconds':round(time.monotonic()-t,3),'stdout_sha256':hashlib.sha256(r.stdout.encode()).hexdigest()})
            print('PASS '+label+(' [-O]' if opt else ''),flush=True)
            return r.stdout
        def same(actual,expected,label):
            require(actual.is_file() and expected.is_file(), 'missing rebuild: '+label)
            require(actual.read_bytes()==expected.read_bytes(),'nonidentical rebuild: '+label)
            report['byte_equalities'].append({'artifact':label,'sha256':digest(actual),'bytes':actual.stat().st_size})
        # The retained coefficient recipe intentionally rejects -O. Run its
        # checked mode, then independently bind all four reconstructed ports.
        coeff=out/'coefficients'
        run('coefficient recipe',['norm/coefficients/recipe/source34_builder.py','--output',coeff])
        for old,new in [('beta','beta'),('K','K0'),('MC','MC'),('MF_source','MF')]:
            raw=(coeff/(old+'.bin')).read_bytes();bound=gzip.decompress((work/'norm/coefficients'/(new+'.bin.gz')).read_bytes())
            require(raw==bound,'coefficient recipe mismatch: '+new)
        report['coefficient_recipe_ports_rebuilt']=4
        for opt in modes:
            tag='optimized' if opt else 'normal';o=out/tag;o.mkdir()
            run('arithmetic identities',['radicals/verify_arithmetic.py'],opt)
            run('norm graph rebuild',['norm/build.py'],opt)
            for name in ['equation.json','equation_reduced.json']:same(work/'norm'/name,ROOT/'norm'/name,'norm/'+name+' '+tag)
            run('norm universal identities',['norm/check.py'],opt)
            run('independent resultant and interpolation audit',['radicals_audit/audit_independent.py'],opt)
            run('architecture finite semantic regressions',['architecture/check_semantics.py','--output',o/'semantics.json'],opt)
            run('independent natural contraction',['direct_audit/audit_literal_independent.py','architecture/derived16_cantor','--output',o/'natural.json'],opt)
            run('independent natural 350 tradeoff',['direct_audit/audit_literal_independent.py','architecture/factorial16_cantor','--output',o/'natural350.json'],opt)
            for raw,signed,factored,center,label in [
                ('architecture/carrier_hybrid_shell/raw','direct/hybrid_noguard_signed_shell','direct/integer519','direct/integer519_centered','519'),
                ('architecture/derived16_shell/raw','direct/derived16_signed_shell','direct/derived16_factored_shell','direct/derived16_centered_shell','517')]:
                run('independent signed '+label,['direct_audit/audit_signed_independent.py',raw,signed,factored,'--output',o/('signed'+label+'.json')],opt)
                run('independent translation '+label,['direct_audit/audit_translation_independent.py',factored,center,'--output',o/('translation'+label+'.json')],opt)
            run('all final quartic coefficients',['report_audit/check_final_metrics.py'],opt)
            run('pinned baseline quartics',['review/audit_literal_polynomials.py'],opt)
            baseline=json.loads((work/'review/LITERAL_AUDIT.json').read_text())
            require(len(baseline['results'])==7,'baseline coverage must be seven equations')
            run('pinned baseline circuit counts',['review/audit_circuit_counts.py'],opt)
            # Rebuild all three principal endpoints from the bundled source.
            natural=o/'derived349';shell=o/'derived_shell';hybrid=o/'hybrid_shell'
            run('rebuild natural 349',['architecture/build_derived_label_range.py','--output',natural],opt)
            for sub in ['raw','natural']:
                for f in (ROOT/'architecture/derived16_cantor'/sub).glob('*.json'):
                    same(natural/sub/f.name,f,'derived349/'+sub+'/'+f.name+' '+tag)
            same(natural/'SUMMARY.json',ROOT/'architecture/derived16_cantor/SUMMARY.json','derived349/SUMMARY.json '+tag)
            slack=o/'factorial350'
            run('rebuild natural 350 tradeoff',['architecture/build_factorial_carrier.py','--horizon-minimum','16','--output',slack],opt)
            for sub in ['raw','natural']:
                for f in (ROOT/'architecture/factorial16_cantor'/sub).glob('*.json'):
                    same(slack/sub/f.name,f,'factorial350/'+sub+'/'+f.name+' '+tag)
            same(slack/'SUMMARY.json',ROOT/'architecture/factorial16_cantor/SUMMARY.json','factorial350/SUMMARY.json '+tag)
            run('rebuild derived shell source',['architecture/build_derived_label_range.py','--syntax','xx0','--output',shell],opt)
            run('rebuild hybrid shell source',['architecture/build_hybrid.py','--syntax','xx0','--output',hybrid],opt)
            for produced,frozen in [(shell,'derived16_shell'),(hybrid,'carrier_hybrid_shell')]:
                for name in ['equation.json','raw_audit_input.json']:
                    same(produced/'raw'/name,ROOT/'architecture'/frozen/'raw'/name,frozen+'/raw/'+name+' '+tag)
            z519=o/'integer519'
            run('rebuild centered 519',['direct/reproduce_integer519.py','--raw',hybrid/'raw','--output',z519],opt)
            for generated,frozen in [('signed','hybrid_noguard_signed_shell'),('factored','integer519'),('final','integer519_centered')]:
                for f in (z519/generated).glob('*.json'):
                    same(f,ROOT/'direct'/frozen/f.name,frozen+'/'+f.name+' '+tag)
            z517=o/'integer517'
            run('rebuild signed 517',['direct/build_signed.py',shell/'raw',z517/'signed','--drop-u-guard'],opt)
            run('rebuild factored 517',['direct/factor_horn.py',z517/'signed/guarded.json',z517/'factored'],opt)
            run('rebuild centered 517',['direct/translate_coordinates.py',z517/'factored/equation.json',z517/'final'],opt)
            for generated,frozen in [('signed','derived16_signed_shell'),('factored','derived16_factored_shell'),('final','derived16_centered_shell')]:
                for f in (z517/generated).glob('*.json'):
                    same(f,ROOT/'direct'/frozen/f.name,frozen+'/'+f.name+' '+tag)
        report['status']='PASS';report['temporary_copy_replay']=True;report['commands_passed']=len(report['checks']);report['byte_equalities_passed']=len(report['byte_equalities']);report['elapsed_seconds']=round(time.monotonic()-start,3)
    data=json.dumps(report,indent=2)+'\n'
    if a.report:a.report.parent.mkdir(parents=True,exist_ok=True);a.report.write_text(data)
    print(data)
if __name__=='__main__':main()
