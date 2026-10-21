#!/usr/bin/env python3
"""Freshly compile the exact production-selector adapter and its small closure."""
import argparse,hashlib,json,shutil,subprocess,time
from pathlib import Path
MODULES=[('K230S','KCode230'),('K230L','Codes230'),('K215F','DomRho8'),
         ('K215F','Codes222'),('K215F','Thm222'),('K215F','ThmDom'),
         ('K215F','EnumPerm'),('K215F','L1_CompPerm'),
         ('','EarlyHaltSelection'),('','NativeSelection'),('','K215SelectorAdapter')]
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def main():
 p=argparse.ArgumentParser();p.add_argument('--output',type=Path,required=True)
 p.add_argument('--coqc',default='coqc');p.add_argument('--coqchk',default='coqchk');a=p.parse_args()
 out=a.output.resolve();out.mkdir(parents=True,exist_ok=False);src=Path(__file__).resolve().parent
 for ns,m in MODULES:
  s=src/'upstream'/ns/(m+'.v') if ns else src/(m+'.v')
  d=out/ns/(m+'.v');d.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(s,d)
 flags=sum((['-Q',ns,ns] for ns in ['K230S','K230L','K215F']),[])
 commands=[[a.coqc,'--version']]+[[a.coqc,'-q']+flags+[str(Path(ns)/(m+'.v'))] for ns,m in MODULES]
 commands.append([a.coqchk,'-silent']+flags+['K215SelectorAdapter'])
 records=[]
 for i,cmd in enumerate(commands):
  t=time.monotonic();r=subprocess.run(cmd,cwd=out,capture_output=True,text=True,timeout=180)
  log=out/f'{i:02d}.log';log.write_text(r.stdout+r.stderr)
  records.append({'command':cmd,'returncode':r.returncode,'seconds':time.monotonic()-t,'log':log.name,'log_sha256':sha(log)})
  if r.returncode:break
 receipt={'status':'PASS_COMPILED_AND_KERNEL_RECHECKED' if len(records)==len(commands) and all(x['returncode']==0 for x in records) else 'FAIL',
          'actions':records,'source_hashes':{str(Path(ns)/(m+'.v')):sha(out/ns/(m+'.v')) for ns,m in MODULES},
          'object_hashes':{str(Path(ns)/(m+'.vo')):sha(out/ns/(m+'.vo')) for ns,m in MODULES if (out/ns/(m+'.vo')).exists()},
          'scope':'Exact production NIP/DROP/exec/ax_stack adapter plus small compiler dependency closure; not full binary endpoint.'}
 (out/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt,indent=2))
 raise SystemExit(0 if receipt['status'].startswith('PASS') else 1)
if __name__=='__main__':main()
