#!/usr/bin/env python3
"""Fresh native-semantic transport build. Does not build CM215Endpoint.v."""
from pathlib import Path
import argparse,hashlib,json,shutil,subprocess,time
from check_inputs import ROOT,check

def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def main():
 ap=argparse.ArgumentParser(description=__doc__)
 ap.add_argument('--work',type=Path,default=ROOT/'.build')
 ap.add_argument('--coqc',default='coqc');ap.add_argument('--coqchk',default='coqchk')
 args=ap.parse_args();work=args.work.resolve();work.mkdir(parents=True,exist_ok=True)
 inputs=check();manifest=json.loads((ROOT/'source_manifest.json').read_text())
 for rel in manifest['files']:
  target=work/rel;target.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(ROOT/rel,target)
 flags=['-Q',str(work/'vendor/BusyCoq'),'BusyCoq','-Q',str(work/'vendor/K215F'),'K215F']
 order=['vendor/BusyCoq/LibTactics.v','vendor/BusyCoq/Helper.v','vendor/BusyCoq/TM.v','vendor/K215F/Table230.v','vendor/K215F/TM230.v','vendor/K215F/Table215.v','vendor/K215F/Dense215.v','CM215Table.v','CM215Stream.v']
 receipt={'status':'RUNNING','toolchain':subprocess.check_output([args.coqc,'--version'],text=True).strip(),'input_check':inputs,'modules':[],'endpoint_rebuilt':False}
 start=time.monotonic()
 for rel in order:
  t=time.monotonic();r=subprocess.run([args.coqc,*flags,str(work/rel)],cwd=work,capture_output=True,text=True)
  text=r.stdout+r.stderr;log=work/(Path(rel).stem+'.log');log.write_text(text)
  item={'source':rel,'source_sha256':sha(work/rel),'seconds':round(time.monotonic()-t,3),'exit_code':r.returncode,'log_sha256':sha(log)}
  receipt['modules'].append(item);print(rel,r.returncode,item['seconds'],flush=True)
  if r.returncode: raise RuntimeError(text)
  item['object_sha256']=sha((work/rel).with_suffix('.vo'))
  if rel=='CM215Stream.v':
   assert text.count('Closed under the global context')==2 and 'Axioms:' not in text
 t=time.monotonic();r=subprocess.run([args.coqchk,*flags,'-silent','-o','CM215Stream'],cwd=work,capture_output=True,text=True)
 log=work/'coqchk.log';log.write_text(r.stdout+r.stderr)
 receipt['coqchk']={'exit_code':r.returncode,'seconds':round(time.monotonic()-t,3),'log_sha256':sha(log)}
 if r.returncode:raise RuntimeError(r.stdout+r.stderr)
 receipt['seconds']=round(time.monotonic()-start,3);receipt['status']='PASS_CLOSED_KERNEL'
 (work/'verification.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt,indent=2))
if __name__=='__main__':main()
