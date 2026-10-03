#!/usr/bin/env python3
"""Standard-library, offline, non-mutating release replay. Run from any directory."""
import hashlib,json,os,pathlib,shutil,subprocess,sys,tempfile,time
ROOT=pathlib.Path(__file__).resolve().parent

def require(condition, message):
    if not condition: raise RuntimeError(message)

def verify_manifest():
    records={}
    for line in (ROOT/'SHA256SUMS').read_text().splitlines():
        digest,name=line.split('  ',1);records[name]=digest
        p=ROOT/name
        require(p.is_file(),f'missing file: {name}')
        require(hashlib.sha256(p.read_bytes()).hexdigest()==digest,f'hash mismatch: {name}')
    actual={str(p.relative_to(ROOT)) for p in ROOT.rglob('*') if p.is_file()
            and not any(q in {'.build','build','__pycache__'} for q in p.relative_to(ROOT).parts)
            and p.name!='SHA256SUMS'}
    # A nested byte-preserved companion manifest is a manifested payload itself.
    actual.add('companion-report12/COMPANION_SHA256SUMS')
    require(actual==set(records),f'unmanifested or missing payload: {sorted(actual^set(records))}')
    return len(records)

def main():
    start=time.time(); n=verify_manifest(); completed=[]
    env=dict(os.environ,PYTHONDONTWRITEBYTECODE='1')
    with tempfile.TemporaryDirectory(prefix='report15-replay-') as td:
        work=pathlib.Path(td)/'release'
        shutil.copytree(ROOT,work,ignore=shutil.ignore_patterns('.build','build','__pycache__'))
        def run(label,args,cwd='.'):
            print(label,flush=True)
            cp=subprocess.run([sys.executable]+args,cwd=work/cwd,env=env,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
            if cp.returncode:
                print(cp.stdout);raise RuntimeError(f'{label} exited {cp.returncode}')
            completed.append(label)
        def same(name):
            require((work/name).read_bytes()==(ROOT/name).read_bytes(),f'fixture mismatch: {name}')
        run('Independent full-shift lemma ring check',['checks/exhaustive_audit.py'],'compiler')
        run('Independent compiler geometry stress',['checks/compiler_stress.py'],'compiler')
        run('Independent original raw fixture reconstruction',['checks/verify_original_fixture.py'],'compiler')
        run('Independent clean raw fixture reconstruction',['checks/verify_clean_fixture.py'],'compiler')
        run('Compiler selected edge and inverse checks',['test_compiler.py'],'compiler')
        run('Compiler full reflection cycles',['full_cycle_test.py'],'compiler')
        run('Compiler decrement, stuck and malformed checks',['additional_tests.py'],'compiler')
        for opt in (False,True):
            flags=['-O'] if opt else []
            run('Independent compiler API '+('optimized' if opt else 'normal'),flags+['audits/audit_api.py','--receipt','audit-ca.json'])
            require(json.loads((work/'audit-ca.json').read_text())['status']=='passed','CA audit failed')
        run('Regenerate every original CA frame',['sample_orbit.py'],'compiler')
        for f in ['sample-orbit.json','sample-receipt.json','sample-boundary-demonstration.json']:same('compiler/'+f)
        run('Regenerate every clean-target CA frame',['clean_target_sample.py'],'compiler')
        for f in ['clean-target-sample-orbit.json','clean-target-sample-receipt.json']:same('compiler/'+f)
        for opt in (False,True):
            flags=['-O'] if opt else []
            run('Producer certificate suite '+('optimized' if opt else 'normal'),flags+['test_certificate.py'],'certificates')
            for base in ['sample','sample-real','clean-target','clean-target-real']:
                same('certificates/'+base+'-certificate.json');same('certificates/'+base+'-witness.json')
            run('Independent certificate audit '+('optimized' if opt else 'normal'),flags+['audits/audit_certificate.py','--receipt','audit-cert.json'])
            require(json.loads((work/'audit-cert.json').read_text())['status']=='passed','certificate audit failed')
        for base,src,h,real in [('sample','sample-source.json',1,False),('sample-real','sample-source.json',1,True),('clean-target','clean-target-sample-source.json',4,False),('clean-target-real','clean-target-sample-source.json',4,True)]:
            args=['certificate.py',src,str(h),'--clock','--output','cli.json']+(['--real'] if real else [])
            run('Exact CLI '+base,args,'certificates')
            require((work/'certificates/cli.json').read_bytes()==(ROOT/f'certificates/{base}-certificate.json').read_bytes(),'CLI polynomial differs')
            require((work/'certificates/cli.json.witness.json').read_bytes()==(ROOT/f'certificates/{base}-witness.json').read_bytes(),'CLI witness differs')
        run('Deterministic raw-trace vector regeneration',['tools/render_trace.py'])
        same('figures/accepting-orbit.pdf');same('figures/accepting-orbit.svg')
        for line in (ROOT/'companion-report12/COMPANION_SHA256SUMS').read_text().splitlines():
            h,name=line.split(None,1);name=name.lstrip('* ')
            require(hashlib.sha256((ROOT/'companion-report12'/name).read_bytes()).hexdigest()==h,'companion not byte-preserved')
    verify_manifest()
    print(json.dumps(dict(status='passed',manifested_files=n,stages=len(completed),ordinary_frames=1394,clean_frames=5670,compiler_sha256=hashlib.sha256((ROOT/'compiler/reversible_binary.py').read_bytes()).hexdigest(),certificate_sha256=hashlib.sha256((ROOT/'certificates/certificate.py').read_bytes()).hexdigest(),seconds=round(time.time()-start,3)),indent=2))

if __name__=='__main__':main()
