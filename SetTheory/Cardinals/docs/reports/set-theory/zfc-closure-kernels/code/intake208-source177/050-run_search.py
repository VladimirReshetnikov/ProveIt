#!/usr/bin/env python3
"""Reproduce restricted two-row fold search on the named current 215 tables."""
import argparse, json, hashlib, subprocess, time
from pathlib import Path

TABLES = {
 'K215':'k215.native.tm',
 'commands120':'alternatives/commands120/k215.native.tm',
 'composed':'alternatives/composed/k215.native.tm',
 'marker':'alternatives/conditional-marker/machine/marker215.native.tm',
 'context':'alternatives/context-returns/machine/k215-context.native.tm',
 'shallow':'alternatives/context-returns/machine/k215-shallow.native.tm',
 'direct':'alternatives/direct-transfer/machine/st215.native.tm',
 'dr215':'alternatives/dr215/DR215/machine/dr215.native.tm',
 'forced':'alternatives/forced-transfer/forced215/machine.native.tm',
 'gc-zc':'alternatives/gc-zc215/hybrid215/gc_zc215_start74.native.tm',
 'gc215':'alternatives/gc215/machine/gc215.native.tm',
 'mp-first':'alternatives/mp-first-transfer/machine/t215.native.tm',
 'rebalanced':'alternatives/rebalanced/machine/k215r.native.tm',
 'reencoded':'alternatives/reencoded/machine/k215.native.tm',
 'rho6-120':'alternatives/rho6/machines/rho6_120/candidate.native.tm',
 'rho6-210':'alternatives/rho6/machines/rho6_210/candidate.native.tm',
 'zero-credit':'alternatives/zero-credit/machine/zc215.native.tm',
 'zero-spare':'alternatives/zero-spare/machine/z215.native.tm',
 'zero-spare-mp':'alternatives/zero-spare-mp-first/machine/candidate.native.tm',
 'zero-spare-transfer':'alternatives/zero-spare-transfer/primary/machine/zero_spare_transfer215.native.tm',
 'zero-spare-z201':'alternatives/zero-spare-z201/primary/z201.native.tm',
}

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--repo',type=Path,required=True);ap.add_argument('--out',type=Path,required=True);ap.add_argument('--depth',type=int,default=4);a=ap.parse_args()
 here=Path(__file__).resolve().parent;a.out.mkdir(parents=True,exist_ok=True)
 subprocess.run(['g++','-O3','-std=c++17',str(here/'fold2.cpp'),'-o',str(a.out/'fold2')],check=True)
 subprocess.run(['g++','-O2','-std=c++17',str(here/'controls.cpp'),'-o',str(a.out/'controls')],check=True)
 root=a.repo/'Computability/BusyBeaver/Research/ZFC/candidate-k215'
 control=subprocess.run([str(a.out/'controls'),str(root/'k215.native.tm')],check=True,text=True,capture_output=True)
 (a.out/'controls.txt').write_text(control.stdout)
 results=[]
 for name,rel in TABLES.items():
  start=time.monotonic();inp=a.out/(name+'.input')
  subprocess.run(['python3',str(here/'prepare_fold2.py'),str(root/rel),'--out',str(inp),'--depth',str(a.depth)],check=True,capture_output=True)
  with inp.open()as f:r=subprocess.run([str(a.out/'fold2')],stdin=f,text=True,capture_output=True,check=True)
  (a.out/(name+'.result')).write_text(r.stdout)
  meta=json.loads(inp.with_suffix('.json').read_text());meta['table']='Computability/BusyBeaver/Research/ZFC/candidate-k215/'+rel;meta['stdout']=r.stdout;meta['elapsed_seconds']=time.monotonic()-start
  results.append(meta);print(name,r.stdout.strip(),flush=True)
  (a.out/'results.json').write_text(json.dumps(results,indent=2)+'\n')
 provenance={'repository_commit':subprocess.check_output(['git','rev-parse','HEAD'],cwd=a.repo,text=True).strip(),'sources':{p.name:hashlib.sha256(p.read_bytes()).hexdigest()for p in [here/'fold2.cpp',here/'controls.cpp',here/'prepare_fold2.py',here/'run_search.py']},'controls':control.stdout,'scope':'Restricted two-row marker-fold synthesis. No minimum-state theorem and no claimed 214 machine.'}
 (a.out/'provenance.json').write_text(json.dumps(provenance,indent=2)+'\n')
if __name__=='__main__':main()
