from pathlib import Path
import hashlib,json,os,subprocess,time
import reproduce
root=Path(__file__).resolve().parent;out=root/'build';work=out/'work';logs=out/'logs';receipt=json.loads((out/'receipt.json').read_text())
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
receipt['initial_failed_import_check']=receipt['checks'].pop()
for s in receipt['sources']:
 if s['module']=='Source215NormalizedBalanced.v':s['source_sha256']=sha(root/s['module']);s['compiled_source_sha256']=sha(work/s['module'])
def run(name,cmd):
 log=logs/(name+'.log');t=time.monotonic()
 with log.open('w') as stream:
  p=subprocess.Popen(cmd,cwd=work,stdout=stream,stderr=subprocess.STDOUT);_,status,usage=os.wait4(p.pid,0);p.returncode=os.waitstatus_to_exitcode(status)
 text=log.read_text();row={'name':name,'command':cmd,'exit_code':p.returncode,'seconds':round(time.monotonic()-t,3),'max_rss_kib':usage.ru_maxrss,'closed_reports':text.count('Closed under the global context'),'log_sha256':sha(log)}
 receipt['checks'].append(row);(out/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(row),flush=True)
 if p.returncode:print(text);raise SystemExit(p.returncode)
 if 'Axioms:' in text:raise SystemExit('Unexpected open assumption report')
run('Source215NormalizedBalanced_fixed',['coqc',*reproduce.FLAGS,'Source215NormalizedBalanced.v'])
(work/'deps/K215F/Source215.v').write_text('From Coq Require Import List.\nFrom K230 Require Import RM.\nFrom K215F Require Import Prog215 DagPerm.\nRequire Import Source215NormalizedBalanced.\nImport ListNotations.\nTheorem p215_dagPerm R : rm_halts p215 ([],R) <-> rm_halts dagPerm ([],R).\nProof. exact (p215_dagPerm_normalized_balanced R). Qed.\nPrint Assumptions p215_dagPerm.\n')
run('public_facade',['coqc',*reproduce.FLAGS,'deps/K215F/Source215.v'])
(work/'EndpointClient.v').write_text('From Coq Require Import List.\nFrom K230 Require Import RM.\nFrom K215F Require Import Prog215 DagPerm Source215.\nImport ListNotations.\nDefinition public_client : forall R, rm_halts p215 ([],R) <-> rm_halts dagPerm ([],R) := K215F.Source215.p215_dagPerm.\nPrint Assumptions public_client.\n')
run('typed_client',['coqc',*reproduce.FLAGS,'EndpointClient.v'])
run('coqchk_concrete',['coqchk',*reproduce.FLAGS,'-silent','EndpointClient'])
receipt['complete']=True;receipt['recursive_check']='passed';receipt['driver_sha256']=sha(root/'reproduce.py');receipt['continuation_sha256']=sha(__file__);receipt['total_seconds']=round(sum(x['seconds'] for x in receipt['checks']),3)
receipt['objects']=[{'module':str(p.relative_to(work)),'sha256':sha(p)} for p in sorted(work.rglob('*.vo'))]
(out/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n');print('PASS_NORMALIZED_BALANCED_SOURCE',flush=True)
