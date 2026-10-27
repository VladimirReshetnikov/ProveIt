"""Replay authored checks from a release ZIP, without retiming benchmarks."""
from pathlib import Path
import hashlib,json,subprocess,sys,tempfile,zipfile

def main(archive,output):
    archive=Path(archive).resolve();records=[]
    with tempfile.TemporaryDirectory(prefix='eth-iteration2-replay-') as td:
        td=Path(td)
        with zipfile.ZipFile(archive) as z:
            for name in z.namelist():
                if not (td/name).resolve().is_relative_to(td):raise ValueError('unsafe ZIP path')
            if z.testzip():raise ValueError('CRC failure')
            z.extractall(td)
        root=td/'eth_iteration2'
        def run(args,fail=False):
            p=subprocess.run([sys.executable,'-B']+args,cwd=root,text=True,capture_output=True)
            records.append({'args':args,'exit':p.returncode,'stdout':p.stdout,'stderr':p.stderr})
            if (p.returncode==0)==fail:raise RuntimeError(records[-1])
        run(['code/verify_bundle.py'])
        for opt in ([],['-O']):
            mode='opt' if opt else 'normal'
            for name in ('check_balancing.py','cauchy_checks.py','verify_cache_schedule.py','verify_comparison.py','verify_fused_cauchy.py'):
                run(opt+['code/'+name,str(td/(mode+'-'+name+'.json'))])
            run(opt+['qa/performance_audit_checks.py',str(td/(mode+'-audit.json'))])
            run(opt+['qa/fused_audit_checks.py',str(td/(mode+'-fused-audit.json'))])
            for name in ('verify_late_cache.py','verify_lowmemory_companion.py'):
                run(opt+['late_cache_checks/'+name,str(td/(mode+'-'+name+'.json'))])
            # Three positives and six deliberate failures internally, per mode;
            # aggregate driver exercises both Python modes itself.
            run(opt+['asym_schedule_checks/verify_all_certificates.py',str(td/(mode+'-certificates.json'))])
        run(['code/verify_bundle.py'])
        target=root/'README.txt';saved=target.read_bytes()
        target.write_bytes(saved+b'\nchanged\n');run(['code/verify_bundle.py'],True);target.write_bytes(saved)
        target.rename(root/'README.missing');run(['code/verify_bundle.py'],True);(root/'README.missing').rename(target)
        src=root/'sources/prior/08_build_quantitative-contraction.tex';old=src.read_bytes();sums=root/'SHA256SUMS';sm=sums.read_text()
        src.write_bytes(old+b'\n')
        sums.write_text('\n'.join((hashlib.sha256(src.read_bytes()).hexdigest()+'  '+str(src.relative_to(root))) if line.endswith('  '+str(src.relative_to(root))) else line for line in sm.splitlines())+'\n')
        run(['code/verify_bundle.py'],True);src.write_bytes(old);sums.write_text(sm)
        run(['code/verify_bundle.py'])
    result={'success':True,'archive':archive.name,'sha256':hashlib.sha256(archive.read_bytes()).hexdigest(),
            'positive_top_level_stages':23,'negative_integrity_controls':3,
            'certificate_controls':'Each aggregate run includes eight positive and sixteen negative child-process checks; run twice.',
            'scope':'Finite authored component/certificate replay and integrity; not full SAT validation. Historical timing samples are checked, not remeasured.',
            'records':records}
    Path(output).write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k!='records'},indent=2))
if __name__=='__main__':
    if len(sys.argv)!=3:raise SystemExit('usage: replay_archive.py ARCHIVE.zip OUTPUT.json')
    main(sys.argv[1],sys.argv[2])
