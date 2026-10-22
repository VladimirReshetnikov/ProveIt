#!/usr/bin/env python3
"""Fresh kernel build and independent recursive check of the K215 affine core.

Requires Coq 8.18; source_deps/RMEquiv includes a proved compatibility import.
Every project prerequisite is compiled from the delivered sources.  This is a
focused source/graph/core proof, not a new rebuild of the full TM/ZFC endpoint.
"""
from pathlib import Path
import argparse,contextlib,fcntl,hashlib,json,os,shutil,subprocess,time
ROOT=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--skip-recursive',action='store_true')
    ap.add_argument('--batch-lock',action='store_true',
                    help='Hold the shared compiler lock across the entire focused build')
    args=ap.parse_args()
    out=ROOT/'verification';logs=out/'logs';logs.mkdir(parents=True,exist_ok=True)
    coqc=shutil.which('coqc');coqchk=shutil.which('coqchk')
    if not coqc or (not args.skip_recursive and not coqchk):
        raise SystemExit('coqc and coqchk are required')
    order=['source_deps/Compat818.v','source_deps/K230/RM.v','source_deps/K230/RMEquiv.v',
           'source_deps/K230/Prog230.v','source_deps/K230P/Bisim230.v',
           'source_deps/K215F/Prog215.v','source_deps/K215F/DagPerm.v',
           'source_deps/PathCodec.v','source_deps/BisimMirror.v','source_deps/NormalizedBisim.v',
           'DrainCore.v','CoreContraction.v','K215DrainData.v','SourceGraphBridge.v',
           'K215GraphBinding.v','source_deps/K215F/Source215.v','EndpointClient.v']
    flags=['-Q','source_deps','']
    receipt={'schema':'K215-checked-affine-core-v1',
       'scope':'Exact p215 and dagPerm to367-core; exact public source equivalence; no whole TM/ZFC rebuild',
       'toolchain':subprocess.check_output([coqc,'--version'],text=True).strip(),
       'coqc_sha256':sha(coqc),'coqchk_sha256':sha(coqchk) if coqchk else None,
       'project_modules':len(order),'checks':[],'complete':False,
       'lock_policy':'whole_build' if args.batch_lock else 'per_compiler',
       'source_sha256':{name:sha(ROOT/name) for name in order}}
    target=out/'build.json'
    def save():
        target.write_text(json.dumps(receipt,indent=2)+'\n')
    batch_lock=None
    def run(name,cmd,source=None):
        log=logs/(name+'.log')
        # Other active proof-assistant jobs use this advisory machine-wide lock.
        receipt['active']={'name':name,'status':'ready' if batch_lock else 'waiting_for_lock','driver_pid':os.getpid(),
                           'command':cmd}
        save()
        print('WAITING '+name,flush=True)
        with (contextlib.nullcontext(batch_lock) if batch_lock else
              open('/tmp/proveit-k215-proof-build.lock','a')) as lock:
            if not batch_lock:
                fcntl.flock(lock,fcntl.LOCK_EX)
            start=time.monotonic()
            if source:
                # Explicitly remove this module's prior object before rebuilding.
                for ext in ['.vo','.vos','.vok','.glob']:
                    (ROOT/source).with_suffix(ext).unlink(missing_ok=True)
            with log.open('w') as stream:
                p=subprocess.Popen(cmd,cwd=ROOT,stdout=stream,stderr=subprocess.STDOUT)
                receipt['active'].update(status='running',compiler_pid=p.pid)
                save()
                print('RUNNING '+name+' pid='+str(p.pid),flush=True)
                _,status,usage=os.wait4(p.pid,0)
                p.returncode=os.waitstatus_to_exitcode(status)
            elapsed=time.monotonic()-start
            if not batch_lock:
                fcntl.flock(lock,fcntl.LOCK_UN)
        text=log.read_text()
        row={'name':name,'command':cmd,'exit_code':p.returncode,
             'seconds':round(elapsed,3),'max_rss_kib':usage.ru_maxrss,
             'log_sha256':sha(log),'closed_reports':text.count('Closed under the global context')}
        if source and p.returncode==0:
            row['object_sha256']=sha((ROOT/source).with_suffix('.vo'))
        receipt['checks'].append(row)
        receipt.pop('active',None)
        save()
        print(json.dumps(row),flush=True)
        if p.returncode:
            print(text);raise SystemExit(p.returncode)
        if 'Axioms:' in text:
            raise SystemExit('Unexpected nonclosed assumption report')
    if args.batch_lock:
        receipt['active']={'name':'whole_build','status':'waiting_for_lock','driver_pid':os.getpid()}
        save()
        print('WAITING whole_build',flush=True)
        batch_lock=open('/tmp/proveit-k215-proof-build.lock','a')
        fcntl.flock(batch_lock,fcntl.LOCK_EX)
        print('LOCKED whole_build',flush=True)
    for name in order:
        run(name.replace('/','_'),[coqc,*flags,name],name)
    if not args.skip_recursive:
        run('coqchk_EndpointClient',[coqchk,*flags,'-silent','EndpointClient'])
    receipt['complete']=True
    receipt['recursive_check']='omitted' if args.skip_recursive else 'passed'
    receipt['total_compile_and_check_seconds']=round(sum(x['seconds'] for x in receipt['checks']),3)
    receipt['peak_rss_kib']=max(x['max_rss_kib'] for x in receipt['checks'])
    receipt['build_driver_sha256']=sha(__file__)
    target.write_text(json.dumps(receipt,indent=2)+'\n')
    print('PASS_COMPILED_CLOSED'+('' if args.skip_recursive else '_RECURSIVE'),flush=True)
    if batch_lock:
        batch_lock.close()

if __name__=='__main__':main()
