#!/usr/bin/env python3
"""Portable release verification; --runtime rederives all symbolic cases."""
from pathlib import Path
import argparse,json,gzip,hashlib,sys,subprocess,tempfile
ROOT=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT/'code'))
import reconstruct as R

def main():
 if not __debug__:raise RuntimeError('Assertions must be enabled')
 p=argparse.ArgumentParser();p.add_argument('--runtime',action='store_true');p.add_argument('--out',type=Path);a=p.parse_args()
 out=a.out or Path(tempfile.mkdtemp(prefix='zc215-verify-'))
 if a.out:out.mkdir(parents=True,exist_ok=False)
 manifest=ROOT/'MANIFEST.json'
 if manifest.exists():
  for name,digest in json.loads(manifest.read_text())['sha256'].items():assert hashlib.sha256((ROOT/name).read_bytes()).hexdigest()==digest,name
 result={'reconstruction':R.reconstruct()}
 s,T=R.table((ROOT/'machine/zc215.native.tm').read_bytes());target,_=R.canonical(T,s)
 prior=json.loads(gzip.decompress((ROOT/'evidence/prior_215_tables.json.gz').read_bytes()));classes=set()
 for item in prior['tables']:
  M={(q,b):(w,d,z)for q,b,w,d,z in item['rows']}
  can,_=R.canonical(M,item['start']);ref,_=R.canonical(M,item['start'],True)
  classes.add(json.dumps(can,separators=(',',':')))
  assert can!=target and ref!=target,item['path']
 assert len(prior['tables'])==67 and len(classes)==16
 result['comparison']={'tables':67,'rooted_classes':16,'exact_or_reflection_matches':0,'scope':'All parseable 215-state .tm files in the pinned checkout; excludes historical archive members not present as .tm files.'}
 subprocess.run([sys.executable,'-B',str(ROOT/'code/audit_source_credit.py'),'--candidate',str(ROOT),'--parent',str(ROOT/'reference/commands120'),'--startup',str(ROOT/'evidence/blank_startup.json'),'--out',str(out/'source_credit_audit.json')],check=True)
 subprocess.run([sys.executable,'-B',str(ROOT/'code/audit_machine.py'),'--baseline',str(ROOT/'reference/commands120'),'--candidate',str(ROOT),'--out',str(out/'machine_audit.json')],check=True)
 result['source_credit_audit']=json.loads((out/'source_credit_audit.json').read_text())['status']
 result['machine_audit']=json.loads((out/'machine_audit.json').read_text())['status']
 subprocess.run([sys.executable,'-B',str(ROOT/'code/check_tag_lowering.py'),'--out',str(out/'tag_lowering_check.json')],check=True,stdout=subprocess.DEVNULL)
 tag=json.loads((out/'tag_lowering_check.json').read_text())
 assert tag==json.loads((ROOT/'evidence/tag_lowering_check.json').read_text())
 result['tag_lowering_finite_corroboration']=tag['status']
 binder=subprocess.run([sys.executable,'-B',str(ROOT/'research/reconstruct_fresh_binder.py')],check=True,capture_output=True,text=True)
 result['source_only_fresh_binder']=json.loads(binder.stdout)
 if a.runtime:
  import replay_runtime
  result['fresh_runtime']=replay_runtime.replay(out/'runtime')
 (out/'verification.json').write_text(json.dumps(result,indent=2)+'\n')
 print(json.dumps(result,indent=2))
if __name__=='__main__':main()
