#!/usr/bin/env python3
"""Fresh focused build and recursive kernel audit of normalized K215 source proof.

This does not rebuild the complete K215-to-ZFC endpoint. It checks exact source
programs, a shared 1,426-entry certificate, and the generic normalized checker.
"""
from pathlib import Path
import argparse, hashlib, json, os, shutil, subprocess, time
ROOT=Path(__file__).resolve().parent

def sha(path): return hashlib.sha256(Path(path).read_bytes()).hexdigest()

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--output',type=Path,default=ROOT/'verification')
    ap.add_argument('--skip-recursive',action='store_true',help='Only compiler kernel checking; omit separate coqchk')
    args=ap.parse_args();out=args.output.resolve();out.mkdir(parents=True,exist_ok=True)
    work=out/'work';logs=out/'logs';work.mkdir(exist_ok=True);logs.mkdir(exist_ok=True)
    coqc=shutil.which('coqc');coqchk=shutil.which('coqchk')
    if not coqc or not coqchk:raise SystemExit('coqc and coqchk are required')
    version=subprocess.check_output([coqc,'--version'],text=True).strip()
    compat='version 8.18.' in version
    if not (compat or 'version 9.1.' in version):raise SystemExit('Use Coq 8.18 or Rocq 9.1; see README')
    order=(['Compat818.v'] if compat else [])+[
        'deps/K230/RM.v','deps/K230/RMEquiv.v','deps/K230/Prog230.v',
        'deps/K230P/Bisim230.v','deps/K215F/Prog215.v','deps/K215F/DagPerm.v',
        'PathCodec.v','BisimMirror.v','NormalizedBisim.v','NormalizedCert215.v','NormalizedSource215.v',
        'deps/K215F/Source215.v','EndpointClient.v']
    flags=['-Q','deps/K230','K230','-Q','deps/K230P','K230P','-Q','deps/K215F','K215F']
    receipt={'schema':'K215-normalized-rocq-source-v1','toolchain':version,
      'coqc_sha256':sha(coqc),'coqchk_sha256':sha(coqchk),
      'scope':'Exact all-register source equivalence; not a fresh whole-machine ZFC endpoint build',
      'entries':1426,'branch_obligations':2851,'complete':False,'sources':[],'checks':[]}
    for rel in order:
        src=ROOT/({'deps/K230/RMEquiv.v':'deps/K230/RMEquiv.rocq91.v',
                  'deps/K215F/Source215.v':'integration/Source215.v',
                  'EndpointClient.v':'integration/EndpointClient.v'}.get(rel,rel))
        data=src.read_bytes()
        if rel=='deps/K230/RMEquiv.v' and compat:
            needle=b'From K230 Require Import RM.'
            if data.count(needle)!=1:raise SystemExit('Unexpected RMEquiv import')
            data=data.replace(needle,needle+b'\nRequire Import Compat818.')
        dst=work/rel;dst.parent.mkdir(parents=True,exist_ok=True);dst.write_bytes(data)
        receipt['sources'].append({'module':rel,'delivered_sha256':sha(src),'compiled_sha256':sha(dst)})
    path=out/'result.json'
    def run(name,cmd):
        log=logs/(name+'.log');start=time.monotonic()
        with log.open('w') as stream:
            p=subprocess.Popen(cmd,cwd=work,stdout=stream,stderr=subprocess.STDOUT)
            _,status,usage=os.wait4(p.pid,0);p.returncode=os.waitstatus_to_exitcode(status)
        text=log.read_text();row={'name':name,'command':cmd,'exit_code':p.returncode,
          'seconds':round(time.monotonic()-start,3),'max_rss_kib':usage.ru_maxrss,
          'closed_reports':text.count('Closed under the global context'),
          'log_sha256':sha(log)}
        receipt['checks'].append(row);path.write_text(json.dumps(receipt,indent=2)+'\n')
        print(json.dumps(row),flush=True)
        if p.returncode:print(text);raise SystemExit(p.returncode)
    for rel in order:run(rel.replace('/','_'),[coqc,*flags,rel])
    if not args.skip_recursive:
        run('coqchk_EndpointClient',[coqchk,*flags,'-silent','EndpointClient'])
    for name in ['NormalizedBisim.v','NormalizedSource215.v']:
        row=next(x for x in receipt['checks'] if x['name']==name)
        if row['closed_reports']!=2 or 'Axioms:' in (logs/(name+'.log')).read_text():
            raise SystemExit('Unexpected assumption boundary: '+name)
    receipt['complete']=True
    receipt['recursive_source_check']='omitted' if args.skip_recursive else 'passed'
    receipt['total_seconds']=round(sum(x['seconds'] for x in receipt['checks']),3)
    receipt['peak_rss_kib']=max(x['max_rss_kib'] for x in receipt['checks'])
    receipt['driver_sha256']=sha(__file__)
    path.write_text(json.dumps(receipt,indent=2)+'\n')
    print('PASS_COMPILED_CLOSED'+('' if args.skip_recursive else '_RECURSIVE_SOURCE'),flush=True)

if __name__=='__main__':main()
