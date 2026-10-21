#!/usr/bin/env python3
"""Serial proof-data and checker-symmetry build, with exact pinned dependencies.
No system installation is modified. --fetch-upstream downloads only two pinned
source files; alternatively provide an existing upstream checkout. The full
K215/ZFC endpoint is outside this build.
"""
import argparse, hashlib, json, os, shutil, subprocess, time, urllib.request
from pathlib import Path
HERE=Path(__file__).resolve().parent
p=argparse.ArgumentParser()
p.add_argument('--coqc',default='coqc')
p.add_argument('--coqchk',default='coqchk')
p.add_argument('--coqlib')
p.add_argument('--out',type=Path,required=True)
p.add_argument('--reference',type=Path)
p.add_argument('--fetch-upstream',action='store_true')
p.add_argument('--certificates-only',action='store_true')
a=p.parse_args();out=a.out.resolve();out.mkdir(parents=True,exist_ok=True)
basefiles=['OriginalCertificate.v','CompactCertificate.v','CertificateIdentity.v']
more=['K215F/OffsetBisim230.v','OffsetMirror.v']
files=basefiles+(more if not a.certificates_only else [])
for f in files:
 d=out/f;d.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(HERE/f,d)
if not a.certificates_only:
 pins=json.loads((HERE/'upstream-pins.json').read_text())
 for dst,pin in pins.items():
  if a.reference:
   data=(a.reference/pin['source']).read_bytes()
  elif a.fetch_upstream:
   url='https://raw.githubusercontent.com/elliotglazer/k230-rocq/'+pin['commit']+'/'+pin['source']
   with urllib.request.urlopen(url) as response:data=response.read()
  else:raise SystemExit('Supply --reference /path/to/k230-rocq or --fetch-upstream; use --certificates-only for the offline equality proof.')
  if hashlib.sha256(data).hexdigest()!=pin['sha256']:raise SystemExit('Upstream hash mismatch: '+dst)
  d=out/dst;d.parent.mkdir(parents=True,exist_ok=True);d.write_bytes(data)
order=basefiles+([] if a.certificates_only else ['K230/RM.v','K230P/Bisim230.v','K215F/OffsetBisim230.v','OffsetMirror.v'])
flags=(['-coqlib',a.coqlib] if a.coqlib else [])
if not a.certificates_only:flags+=['-Q','K230','K230','-Q','K230P','K230P','-Q','K215F','K215F']
flags+=['-Q','.','']
records=[]
version=subprocess.check_output([a.coqc]+(['-coqlib',a.coqlib] if a.coqlib else [])+['--version'],text=True).strip()
for f in order:
 t=time.monotonic();r=subprocess.run([a.coqc]+flags+[f],cwd=out,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
 log=f.replace('/','_')+'.log';(out/log).write_text(r.stdout)
 records.append({'file':f,'exit_code':r.returncode,'seconds':time.monotonic()-t,'source_sha256':hashlib.sha256((out/f).read_bytes()).hexdigest(),'log':log,'output':r.stdout})
 print(f,r.returncode,round(time.monotonic()-t,3),flush=True)
 (out/'compilation.json').write_text(json.dumps({'version':version,'records':records},indent=2)+'\n')
 if r.returncode:raise SystemExit(r.returncode)
mods=['CertificateIdentity']+([] if a.certificates_only else ['OffsetMirror'])
t=time.monotonic();r=subprocess.run([a.coqchk,'-silent']+flags+mods,cwd=out,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
(out/'kernel-check.log').write_text(r.stdout)
(out/'kernel-check.json').write_text(json.dumps({'modules':mods,'exit_code':r.returncode,'seconds':time.monotonic()-t,'version':version},indent=2)+'\n')
if r.returncode:raise SystemExit(r.returncode)
print('PASS_CLOSED_RECURSIVE_KERNEL')
