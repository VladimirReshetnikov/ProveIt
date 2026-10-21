#!/usr/bin/env python3
"""Fresh Coq replay of the exact drain contracts and literal graph checks."""
import argparse,hashlib,json,pathlib,shutil,subprocess,time
p=argparse.ArgumentParser();p.add_argument('--coqc',default='coqc');p.add_argument('--coqchk',default='coqchk');p.add_argument('--out',required=True);p.add_argument('--recursive',action='store_true');a=p.parse_args()
base=pathlib.Path(__file__).resolve().parent;out=pathlib.Path(a.out).resolve()
if out.exists() and any(out.iterdir()):raise SystemExit('Use a fresh or empty output directory.')
out.mkdir(parents=True,exist_ok=True)
receipt={'scope':'Literal canonical graph drain normalization; no source-graph or binary endpoint','commands':[]}
for name in ['DrainAffine.v','DrainInstances.v']:shutil.copy2(base/'formal'/name,out/name)
commands=[[a.coqc,'-Q','.','',name] for name in ['DrainAffine.v','DrainInstances.v']]
if a.recursive:commands.append([a.coqchk,'-silent','-Q','.','','DrainInstances'])
for i,cmd in enumerate(commands):
 t=time.monotonic();r=subprocess.run(cmd,cwd=out,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
 log=out/f'command-{i}.log';log.write_bytes(r.stdout)
 receipt['commands'].append({'argv':cmd,'exit_code':r.returncode,'seconds':time.monotonic()-t,'log_sha256':hashlib.sha256(r.stdout).hexdigest()})
 (out/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
 print(cmd[0],cmd[-1],r.returncode,flush=True)
 if r.returncode:print(r.stdout.decode(errors='replace'));raise SystemExit(r.returncode)
receipt['source_sha256']={n:hashlib.sha256((out/n).read_bytes()).hexdigest() for n in ['DrainAffine.v','DrainInstances.v']}
receipt['status']='PASS';(out/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
