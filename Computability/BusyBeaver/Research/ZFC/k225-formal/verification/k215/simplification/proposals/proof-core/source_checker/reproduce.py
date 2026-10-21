#!/usr/bin/env python3
"""Fresh check of composed normalized/balanced K215 source correspondence."""
import argparse, hashlib, json, os, pathlib, shutil, subprocess, time
ROOT=pathlib.Path(__file__).resolve().parent
sha=lambda p: hashlib.sha256(pathlib.Path(p).read_bytes()).hexdigest()
def main():
 ap=argparse.ArgumentParser(description=__doc__)
 ap.add_argument('--out',type=pathlib.Path,required=True)
 ap.add_argument('--recursive',action='store_true')
 ap.add_argument('--baseline',action='store_true')
 a=ap.parse_args();out=a.out.resolve()
 if out.exists() and any(out.iterdir()):raise SystemExit('Fresh replay requires an empty output directory')
 out.mkdir(parents=True,exist_ok=True)
 work=out/'work';logs=out/'logs';work.mkdir(exist_ok=True);logs.mkdir(exist_ok=True)
 coqc=shutil.which('coqc');coqchk=shutil.which('coqchk')
 if not coqc:raise SystemExit('coqc required on PATH')
 version=subprocess.check_output([coqc,'--version'],text=True).strip()
 compat='version 8.18.' in version
 if not (compat or 'version 9.1.' in version):raise SystemExit('Validated compatibility: Coq 8.18 / Rocq 9.1')
 order=(['Compat818.v'] if compat else [])+['deps/K230/RM.v','deps/K230/RMEquiv.v','deps/K230/Prog230.v','deps/K230P/Bisim230.v','deps/K215F/Prog215.v','deps/K215F/DagPerm.v','PathCodec.v','BisimMirror.v','NormalizedBisim.v','NormalizedCert215.v','BalancedBisim.v','BalancedNormalized.v','Source215BalancedNormalized.v']
 if a.baseline:order.append('NormalizedSource215.v')
 flags=['-Q','deps/K230','K230','-Q','deps/K230P','K230P','-Q','deps/K215F','K215F']
 result={'schema':'K215-balanced-normalized-v1','scope':'Exact all-register source equivalence, not full binary/ZFC endpoint','toolchain':version,'compiler_sha256':sha(coqc),'sources':[],'checks':[],'complete':False}
 for name in order:
  src=ROOT/('deps/K230/RMEquiv.rocq91.v' if name=='deps/K230/RMEquiv.v' else name)
  data=src.read_bytes()
  if name=='deps/K230/RMEquiv.v' and compat:
   needle=b'From K230 Require Import RM.'
   assert data.count(needle)==1
   data=data.replace(needle,needle+b'\nRequire Import Compat818.')
  dst=work/name;dst.parent.mkdir(parents=True,exist_ok=True);dst.write_bytes(data)
  result['sources'].append({'name':name,'delivered_sha256':sha(src),'compiled_sha256':sha(dst)})
 def run(name,cmd):
  log=logs/(name+'.log');start=time.monotonic()
  with log.open('w') as f:
   p=subprocess.Popen(cmd,cwd=work,stdout=f,stderr=subprocess.STDOUT)
   _,status,usage=os.wait4(p.pid,0);p.returncode=os.waitstatus_to_exitcode(status)
  txt=log.read_text();row={'name':name,'command':cmd,'exit_code':p.returncode,'seconds':round(time.monotonic()-start,3),'max_rss_kib':usage.ru_maxrss,'closed_reports':txt.count('Closed under the global context'),'log_sha256':sha(log)}
  result['checks'].append(row);(out/'result.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(row),flush=True)
  if p.returncode:print(txt);raise SystemExit(p.returncode)
 for name in order:run(name.replace('/','_'),[coqc,*flags,name])
 for name,n in [('BalancedNormalized.v',2),('Source215BalancedNormalized.v',3)]:
  row=next(r for r in result['checks'] if r['name']==name)
  assert row['closed_reports']==n and 'Axioms:' not in (logs/(name+'.log')).read_text()
 if a.recursive:
  if not coqchk:raise SystemExit('coqchk required for --recursive')
  run('coqchk_Source215BalancedNormalized',[coqchk,*flags,'-silent','Source215BalancedNormalized'])
 result['complete']=True;result['recursive_kernel_check']='passed' if a.recursive else 'not requested'
 result['total_seconds']=round(sum(r['seconds'] for r in result['checks']),3)
 (out/'result.json').write_text(json.dumps(result,indent=2)+'\n')
 print('PASS_BALANCED_NORMALIZED',flush=True)
if __name__=='__main__':main()
