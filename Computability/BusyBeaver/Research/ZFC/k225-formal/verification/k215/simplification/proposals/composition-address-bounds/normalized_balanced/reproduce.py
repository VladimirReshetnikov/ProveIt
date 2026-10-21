#!/usr/bin/env python3
"""Fresh normalized-balanced K215 source proof. No full ZFC endpoint rebuild."""
import argparse,hashlib,json,os,shutil,subprocess,time
from pathlib import Path
ROOT=Path(__file__).resolve().parent
ORDER=['Compat818.v','deps/K230/RM.v','deps/K230/RMEquiv.v','deps/K230/Prog230.v',
'deps/K230P/Bisim230.v','deps/K215F/Prog215.v','deps/K215F/DagPerm.v',
'PathCodec.v','BisimMirror.v','NormalizedBisim.v','NormalizedCert215.v',
'BalancedBisim.v','NormalizedBalanced.v','NormalizedTree215.v','Source215NormalizedBalanced.v']
FLAGS=['-Q','deps/K230','K230','-Q','deps/K230P','K230P','-Q','deps/K215F','K215F']
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def main():
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--out',type=Path,required=True);ap.add_argument('--recursive',action='store_true');a=ap.parse_args()
 out=a.out.resolve();work=out/'work';logs=out/'logs';work.mkdir(parents=True,exist_ok=True);logs.mkdir(exist_ok=True)
 coqc=shutil.which('coqc');coqchk=shutil.which('coqchk');version=subprocess.check_output([coqc,'--version'],text=True).strip()
 if 'version 8.18.' not in version:raise SystemExit('This reproduction route is tested with Coq 8.18.0; production Rocq 9.1 port is separate.')
 receipt={'toolchain':version,'coqc_sha256':sha(coqc),'scope':'Exact all-register source equivalence, not complete binary-to-ZFC endpoint','sources':[],'checks':[],'complete':False}
 for rel in ORDER:
  src=ROOT/('deps/K230/RMEquiv.rocq91.v' if rel=='deps/K230/RMEquiv.v' else rel);data=src.read_bytes()
  if rel=='deps/K230/RMEquiv.v':
   needle=b'From K230 Require Import RM.'
   if data.count(needle)!=1:raise SystemExit('Unexpected RMEquiv source')
   data=data.replace(needle,needle+b'\nRequire Import Compat818.')
  dst=work/rel;dst.parent.mkdir(parents=True,exist_ok=True);dst.write_bytes(data)
  receipt['sources'].append({'module':rel,'source_sha256':sha(src),'compiled_source_sha256':sha(dst)})
 def run(name,cmd):
  log=logs/(name+'.log');t=time.monotonic()
  with log.open('w') as stream:
   p=subprocess.Popen(cmd,cwd=work,stdout=stream,stderr=subprocess.STDOUT)
   _,status,usage=os.wait4(p.pid,0);p.returncode=os.waitstatus_to_exitcode(status)
  contents=log.read_text();row={'name':name,'command':cmd,'exit_code':p.returncode,'seconds':round(time.monotonic()-t,3),'max_rss_kib':usage.ru_maxrss,'closed_reports':contents.count('Closed under the global context'),'log_sha256':sha(log)}
  receipt['checks'].append(row);(out/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(row),flush=True)
  if p.returncode:print(contents);raise SystemExit(p.returncode)
  if 'Axioms:' in contents:raise SystemExit('Unexpected open assumption report')
 for rel in ORDER:run(rel.replace('/','_'),[coqc,*FLAGS,rel])
 (work/'deps/K215F/Source215.v').write_text('From Coq Require Import List.\nFrom K230 Require Import RM.\nFrom K215F Require Import Prog215 DagPerm.\nRequire Import Source215NormalizedBalanced.\nImport ListNotations.\nTheorem p215_dagPerm R : rm_halts p215 ([],R) <-> rm_halts dagPerm ([],R).\nProof. exact (p215_dagPerm_normalized_balanced R). Qed.\nPrint Assumptions p215_dagPerm.\n')
 run('public_facade',[coqc,*FLAGS,'deps/K215F/Source215.v'])
 (work/'EndpointClient.v').write_text('From Coq Require Import List.\nFrom K230 Require Import RM.\nFrom K215F Require Import Prog215 DagPerm Source215.\nImport ListNotations.\nDefinition public_client : forall R, rm_halts p215 ([],R) <-> rm_halts dagPerm ([],R) := K215F.Source215.p215_dagPerm.\nPrint Assumptions public_client.\n')
 run('typed_client',[coqc,*FLAGS,'EndpointClient.v'])
 if a.recursive:run('coqchk_concrete',[coqchk,*FLAGS,'-silent','EndpointClient'])
 receipt['complete']=True;receipt['recursive_check']='passed' if a.recursive else 'not run';receipt['driver_sha256']=sha(__file__);receipt['total_seconds']=round(sum(r['seconds'] for r in receipt['checks']),3)
 receipt['objects']=[{'module':str(p.relative_to(work)),'sha256':sha(p)} for p in sorted(work.rglob('*.vo'))]
 (out/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n');print('PASS_NORMALIZED_BALANCED_SOURCE',flush=True)
if __name__=='__main__':main()
