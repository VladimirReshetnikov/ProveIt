#!/usr/bin/env python3
"""Offline, non-mutating reconstruction and verification of this release."""
import argparse, gzip, hashlib, json, os, subprocess, sys, tempfile, time, zipfile
from pathlib import Path

ROOT=Path(__file__).resolve().parent

def need(ok,message):
    if not ok:raise ValueError(message)

def sha(path):return hashlib.sha256(Path(path).read_bytes()).hexdigest()

def verify_manifest():
    rows=(ROOT/'SHA256SUMS').read_text().splitlines()
    seen=set()
    for row in rows:
        digest,name=row.split('  ',1)
        rel=Path(name)
        need(not rel.is_absolute() and '..' not in rel.parts,'Unsafe manifest path')
        need(name not in seen,'Duplicate manifest entry');seen.add(name)
        need(sha(ROOT/rel)==digest,'Release hash mismatch: '+name)
    actual={p.relative_to(ROOT).as_posix() for p in ROOT.rglob('*') if p.is_file()
            and '__pycache__' not in p.parts and p.name!='SHA256SUMS'}
    need(seen==actual,'Manifest inventory mismatch')
    return len(rows)

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--quick',action='store_true',help='Explicitly skip full symbolic runtime rederivation')
    p.add_argument('--output',type=Path,help='Save the combined receipt outside this sealed release')
    a=p.parse_args();start=time.monotonic()
    need(__debug__ and not sys.flags.optimize,'Run the driver without -O')
    need(not os.environ.get('PYTHONOPTIMIZE'),'Unset PYTHONOPTIMIZE')
    if a.output:
        need(ROOT not in a.output.resolve().parents and a.output.resolve()!=ROOT,'Receipt output must be outside release')
    count=verify_manifest();commands=[]
    with tempfile.TemporaryDirectory(prefix='u208-replay-') as scratch:
        tmp=Path(scratch);env=dict(os.environ);env['PYTHONDONTWRITEBYTECODE']='1'
        def run(script,args=(),optimized=False):
            command=[sys.executable,'-B']+(['-O']if optimized else[])+[str(ROOT/'code'/script)]+list(map(str,args))
            print('CHECK',script,('(optimized)'if optimized else''),flush=True)
            result=subprocess.run(command,cwd=ROOT,env=env,text=True,capture_output=True)
            print(result.stdout,end='',flush=True)
            if result.returncode:print(result.stderr,file=sys.stderr)
            need(result.returncode==0,'Failed '+script)
            commands.append({'script':script,'optimized':optimized,'exit_code':result.returncode})
        run('build.py',['--output',tmp/'machine'])
        for name in ('u208.native.tm','u208.tm','state_map.json','construction.json'):
            need((tmp/'machine'/name).read_bytes()==(ROOT/'machine'/name).read_bytes(),'Rebuilt bytes differ: '+name)
        parent=ROOT/'baseline/u209.native.tm';child=tmp/'machine/u208.native.tm'
        for optimized in (False,True):
            run('check_fold.py',[parent,'--child',child,'--helper',217,'--output',tmp/('local_opt'if optimized else'local')],optimized)
        run('check_fold_independent.py',[parent,child,'--output',tmp/'independent_fold.json'])
        run('compare_proposals.py',['--output',tmp/'comparison.json'])
        need(json.loads((tmp/'comparison.json').read_text())==json.loads((ROOT/'evidence/comparison.json').read_text()),'Comparison changed')
        run('check_startup.py',['--parent',parent,'--machine',child,'--sites',ROOT/'machine/sites.json','--output',tmp/'startup.json'])
        need(json.loads((tmp/'startup.json').read_text())==json.loads((ROOT/'evidence/startup.json').read_text()),'Startup receipt changed')
        # Bind the selected parent, source, and borrowed engines to the exact
        # retained archive, rather than only to this package's own manifest.
        with zipfile.ZipFile(ROOT/'reference/U209_ConPA_Joint_2026-10-29.zip') as z:
            prefix='U209_ConPA_Joint_2026-10-29/'
            for here,there in [('baseline/u209.native.tm','machine/u209.native.tm'),
                               ('machine/sites.json','machine/sites.json'),
                               ('baseline/legacy_mapping.json','baseline/legacy_mapping.json'),
                               ('code/symbolic_runtime.py','code/symbolic_runtime.py'),
                               ('code/independent_runtime.py','code/independent_runtime.py')]:
                need((ROOT/here).read_bytes()==z.read(prefix+there),'Reference binding: '+here)
        if not a.quick:
            run('check_runtime.py',['--machine',child,'--sites',ROOT/'machine/sites.json',
                '--mapping',ROOT/'baseline/legacy_mapping.json','--output',tmp/'runtime'])
            with gzip.open(tmp/'runtime/runtime_cases.json.gz','rt')as f:fresh=json.load(f)
            with gzip.open(ROOT/'evidence/runtime_cases.json.gz','rt')as f:saved=json.load(f)
            need(fresh==saved,'Fresh universal case records differ from saved records')
        else:print('SKIPPED: fresh full symbolic runtime derivation (--quick)',flush=True)
    need(verify_manifest()==count,'Release changed during replay')
    receipt={'status':'U208_RELEASE_REPLAY_PASS','quick':a.quick,'manifest_files':count,
      'commands':commands,'full_symbolic_runtime_rederived':not a.quick,
      'native_sha256':sha(ROOT/'machine/u208.native.tm'),'dense_sha256':sha(ROOT/'machine/u208.tm'),
      'seconds':time.monotonic()-start,'scope':'New finite machine equivalence and literal runtime evidence; inherited PA calibration is not a new kernel certificate.'}
    if a.output:
        a.output.parent.mkdir(parents=True,exist_ok=True);a.output.write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps(receipt,indent=2))

if __name__=='__main__':main()
