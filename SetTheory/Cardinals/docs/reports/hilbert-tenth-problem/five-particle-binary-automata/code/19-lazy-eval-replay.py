"""Offline replay in fresh workdirs without changing packaged evidence."""
import argparse
import gzip
from hashlib import sha256
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import time
sys.dont_write_bytecode=True
from verify_release import verify,CORE,SOURCE

ROOT=Path(__file__).resolve().parent
BASE=ROOT/'reproducibility'

def require(ok,detail):
    if not ok:raise RuntimeError(detail)

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--out',type=Path,default=Path('replay-output'))
    args=parser.parse_args()
    require(sys.version_info>=(3,12),'Python 3.12 or later required')
    integrity=verify()
    out=args.out.resolve()
    if out.is_relative_to(ROOT):
        require(out==ROOT/'replay-output','Inside the release, only the documented replay-output directory is allowed')
    require(not out.exists(),'Output directory must not already exist')
    out.mkdir(parents=True)
    source=gzip.decompress((BASE/'source.json.gz').read_bytes())
    require(sha256(source).hexdigest()==SOURCE,'source pin before staging')
    entries=[]
    begin=time.perf_counter()
    for optimized in (False,True):
        label='optimized' if optimized else 'normal'
        work=out/label;work.mkdir()
        for name in ('lazy_reversible.py','frozen_reversible_binary.py','test_lazy.py','audit_checks.py','addendum_checks.py','package_checks.py','benchmark_universal.py','check_startup_geometry.py'):
            shutil.copy2(BASE/name,work/name)
        (work/'source.json').write_bytes(source)
        env=dict(os.environ);env.pop('PYTHONPATH',None);env['PYTHONDONTWRITEBYTECODE']='1'
        mode=['-O'] if optimized else []
        for name in ('test_lazy.py','audit_checks.py','addendum_checks.py','package_checks.py','benchmark_universal.py','check_startup_geometry.py'):
            started=time.perf_counter()
            command=[sys.executable,*mode,'-E','-s','-B',name]
            run=subprocess.run(command,cwd=work,env=env,capture_output=True,text=True)
            (work/(Path(name).stem+'.log')).write_text(run.stdout+run.stderr)
            require(run.returncode==0,'Failed '+label+' '+name+'; inspect its replay log')
            entries.append(dict(mode=label,script=name,status='passed',seconds=time.perf_counter()-started))
            print(label,name,'passed',flush=True)
        suffix='-optimized' if optimized else ''
        for name in ('test','audit','addendum','package','universal','startup-geometry'):
            if name in ('audit','addendum'):
                filename=name+'-receipt'+suffix+'.json'
            else:filename=name+suffix+'-receipt.json' if name in ('test','universal') else name+'-receipt'+suffix+'.json'
            record=json.loads((work/filename).read_text())
            require(record['status']=='passed','receipt status '+filename)
            require(record.get('evaluator_sha256',record.get('lazy_sha256'))==CORE,'receipt core linkage '+filename)
        # Deterministic differential counts and universal supports must reproduce.
        for name,oldname in [('test'+suffix+'-receipt.json','test'+suffix+'-receipt.json'),('audit-receipt'+suffix+'.json','audit-receipt'+suffix+'.json'),('addendum-receipt'+suffix+'.json','addendum-receipt'+suffix+'.json')]:
            fresh=json.loads((work/name).read_text());old=json.loads((BASE/'evidence'/oldname).read_text())
            require(fresh['counts']==old['counts'],'deterministic counts '+name)
        for name in ('universal-startup-trace.json','universal-malformed-trace.json'):
            require((work/name).read_bytes()==(BASE/'evidence'/name).read_bytes(),'deterministic universal trace '+name)
        require(sha256((work/'lazy_reversible.py').read_bytes()).hexdigest()==CORE,'core unchanged after tests')
        # The source is already preserved compressed in the release, so omit the
        # expanded working copy from final replay evidence to avoid duplication.
        (work/'source.json').unlink()
    receipt=dict(status='passed',python_version=sys.version.split()[0],modes=['normal','optimized'],integrity=integrity,
                 evaluator_sha256=CORE,source_sha256=SOURCE,steps=entries,total_seconds=time.perf_counter()-begin,
                 exact_trace_comparison=True,external_sibling_dependencies=False,network_required=False)
    (out/'replay-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps(receipt,indent=2))

if __name__=='__main__':main()
