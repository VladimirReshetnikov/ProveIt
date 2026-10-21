#!/usr/bin/env python3
"""Fresh small-closure replay; no project compiler object is shipped or trusted."""
import argparse, fcntl, hashlib, json, pathlib, shutil, subprocess, tempfile, time
p=argparse.ArgumentParser(description=__doc__)
p.add_argument('--out',type=pathlib.Path,required=True,help='fresh disposable build directory')
p.add_argument('--baseline',action='store_true',help='compile exact earlier source versions')
p.add_argument('--skip-kernel',action='store_true',help='omit the separate recursive coqchk pass')
p.add_argument('--coqc',default='coqc');p.add_argument('--coqchk',default='coqchk')
a=p.parse_args();base=pathlib.Path(__file__).resolve().parent;work=a.out.resolve()
if work.exists() and any(work.iterdir()): raise SystemExit('--out must be empty or absent')
work.mkdir(parents=True,exist_ok=True);(work/'logs').mkdir(exist_ok=True)
version=subprocess.check_output([a.coqc,'--version'],text=True)
compat='version 8.' in version
order=[('K230S','KCode230'),('K230L','Codes230')]+[('K215F',x) for x in ['Codes222','Thm222','DomRho8','ThmDom','EnumPerm','L1_SoundPerm','L1_CompPerm','SeedPerm']]
receipt={'toolchain':version,'baseline':a.baseline,'namespace_compatibility':compat,'modules':[],'checks':[]}
sha=lambda b:hashlib.sha256(b).hexdigest()
for ns,name in order:
 rel=pathlib.Path(ns)/(name+'.v');src=base/'source'/rel
 if not a.baseline and (base/'refactored'/rel).exists():src=base/'refactored'/rel
 data=src.read_bytes();compiled=data.replace(b'From Stdlib ',b'From Coq ') if compat else data
 dest=work/rel;dest.parent.mkdir(exist_ok=True);dest.write_bytes(compiled)
 receipt['modules'].append({'module':ns+'.'+name,'source':str(src.relative_to(base)),'source_sha256':sha(data),'compiled_source_sha256':sha(compiled),'compatibility_aliases':data.count(b'From Stdlib ') if compat else 0})
flags=['-Q','K230S','K230S','-Q','K230L','K230L','-Q','K215F','K215F']
def save(): (work/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
def run(cmd,name):
 with (pathlib.Path(tempfile.gettempdir())/'proveit-proof-compiler.lock').open('a') as lock:
  fcntl.flock(lock,fcntl.LOCK_EX);start=time.monotonic()
  result=subprocess.run(cmd,cwd=work,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
  elapsed=time.monotonic()-start
 (work/'logs'/(name+'.log')).write_bytes(result.stdout)
 receipt['checks'].append({'name':name,'command':cmd,'exit_code':result.returncode,'elapsed_seconds':elapsed,'log_sha256':sha(result.stdout)});save()
 print(name,result.returncode,round(elapsed,3),flush=True)
 if result.returncode:
  print(result.stdout.decode(errors='replace'));raise SystemExit(result.returncode)
for (ns,name),record in zip(order,receipt['modules']):
 run([a.coqc]+flags+[ns+'/'+name+'.v'],ns+'.'+name)
 record['object_sha256']=sha((work/ns/(name+'.vo')).read_bytes());save()
client=(base/'verification/Client.v').read_text()
if a.baseline: client=client[:client.index('Check (enum_complete_from')]
(work/'Client.v').write_text(client);run([a.coqc]+flags+['Client.v'],'Client')
if not a.skip_kernel:run([a.coqchk]+flags+['K215F.SeedPerm'],'recursive-coqchk')
receipt['status']='PASS';save()
