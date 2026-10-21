#!/usr/bin/env python3
"""Verify the release without network access. Add --runtime for all-natural replay."""
from pathlib import Path
import argparse,gzip,hashlib,json,subprocess,sys,tempfile,zipfile
ROOT=Path(__file__).resolve().parent
PARENT='K218_Dominated_Rho8_2026-10-20'
PARENT_SHA='080b4fe855c109ab77588c01c9e012d9572afa7721682306370ccb2eb22cbea9'
def need(ok,msg):
 if not ok:raise ValueError(msg)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def run(cmd,work,logname,cwd=None):
 with (work/logname).open('w')as log:p=subprocess.run([sys.executable,'-B',*map(str,cmd)],cwd=cwd,stdout=log,stderr=subprocess.STDOUT)
 if p.returncode:
  print((work/logname).read_text()[-7000:]);raise RuntimeError('Failed: '+logname)
 print('PASS',logname,flush=True)
def inventory():
 cases=json.loads(gzip.decompress((ROOT/'evidence/runtime_cases.json.gz').read_bytes()));sites=json.loads((ROOT/'machine/sites217.json').read_text());expected=[(i,b)for i,x in enumerate(sites)for b in((False,True)if x[1]=='CD'else(False,))]
 need([(x['site_index'],x['positive'])for x in cases]==expected,'Complete ordered guarded case coverage')
 need(len(cases)==6176,'6176 cases')
 for x in cases:need(len(x['duration'])==13 and x['duration'][0]>0 and all(v>=0 for v in x['duration']),'Positive affine clock')
 met=json.loads((ROOT/'evidence/runtime_metrics.json').read_text());need(sum(x['symbolic_steps']for x in cases)==met['symbolic_rules']==1616558,'Rule census');need(min(x['duration'][0]for x in cases)==13,'Progress constant')
 print('PASS stored case inventory (fresh derivation requires --runtime)',flush=True)
 return cases
def main():
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--runtime',action='store_true');ap.add_argument('--work',type=Path,help='Retain regenerated receipts and logs here; must not exist');a=ap.parse_args()
 need(__debug__ and not sys.flags.optimize,'Python assertions must be enabled')
 manifest=json.loads((ROOT/'manifest.json').read_text())
 for name,digest in manifest['files'].items():need(sha(ROOT/name)==digest,'Manifest mismatch: '+name)
 print('PASS release manifest',len(manifest['files']),'files',flush=True)
 saved_cases=inventory();archive=ROOT/'parent'/f'{PARENT}.zip';need(sha(archive)==PARENT_SHA,'Pinned parent archive')
 temp=None
 if a.work:work=a.work.resolve();work.mkdir(parents=True,exist_ok=False)
 else:temp=tempfile.TemporaryDirectory(prefix='k217-replay-');work=Path(temp.name)
 with zipfile.ZipFile(archive)as z:
  for info in z.infolist():need((work/info.filename).resolve().is_relative_to(work),'Archive path containment')
  z.extractall(work)
 base=work/PARENT
 run([base/'verify_all.py'],work,'parent-finite.log',cwd=base)
 built=work/'rebuilt';run([ROOT/'code/reconstruct217.py','--base',base,'--output',built],work,'reconstruction.log')
 for name in ['k217.native.tm','k217.tm','sites217.json','unfolded218.native.tm']:need((built/name).read_bytes()==(ROOT/'machine'/name).read_bytes(),'Reconstructed bytes: '+name)
 run([ROOT/'code/audit_source_fold.py','--base',base,'--candidate',ROOT/'machine','--out',work/'source-fold.json'],work,'source-fold.log')
 run([ROOT/'code/audit_blank.py','--directory',ROOT/'machine','--canonical',ROOT/'machine/k217.tm','--output',work/'blank.json'],work,'blank.log')
 run([ROOT/'code/check_joint_fold.py','--old',ROOT/'machine/unfolded218.native.tm','--new',ROOT/'machine/k217.native.tm','--keep','69','--drop','400','--radius','7','--fuel','97','--output',work/'fold-window.json'],work,'fold-window.log')
 if a.runtime:
  dest=work/'runtime'
  run([base/'binary/code/validate_native.py',ROOT/'machine/k217.native.tm',ROOT/'machine/sites217.json',dest],work,'runtime.log')
  r=json.loads((dest/'runtime.json').read_text());need(r['status']=='UNIVERSAL_MATHEMATICAL_PASS'and r['proved_cases']==6176,'Full runtime proof')
  need(json.loads((dest/'runtime_cases.json').read_text())==saved_cases,'Exact ordered symbolic case receipts')
  need(r['table_sha256']==sha(ROOT/'machine/k217.native.tm')and r['sites_sha256']==sha(ROOT/'machine/sites217.json'),'Runtime exact byte binding')
  print('PASS all 6176 freshly regenerated cases match delivered receipts',flush=True)
 result={'status':'ALL_REQUESTED_K217_CHECKS_PASS','working_states':217,'rows':434,'blank_startup_steps':312617,'source_occurrences':4751,'fresh_runtime':a.runtime,'runtime_cases':6176,'proof_assistant_endpoint':'No new Lean/Rocq endpoint for these bytes','native_sha256':sha(ROOT/'machine/k217.native.tm'),'canonical_sha256':sha(ROOT/'machine/k217.tm')}
 (work/'result.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
 if a.work:print('Regenerated evidence:',work)
 if temp:temp.cleanup()
if __name__=='__main__':main()
