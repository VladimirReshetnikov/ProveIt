#!/usr/bin/env python3
"""Offline checks for two215 alternatives. --runtime freshly derives primary cases.
--secondary-runtime freshly derives the rho6 alternative cases.
Default checks exact reconstruction, inherited parent, source/graph/blank proofs,
and complete stored symbolic inventories. It does not freshly derive runtime.
"""
from pathlib import Path
import argparse,gzip,hashlib,json,subprocess,sys,tempfile,zipfile
ROOT=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT/'code'))
from reconstruct import reconstruct,table
from check_source import check as source_check
from check_seed import check as seed_check
from check_novelty import check as novelty_check
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def run(args,work,name,cwd=None):
 with(work/name).open('w')as f:p=subprocess.run([sys.executable,'-B',*map(str,args)],cwd=cwd,stdout=f,stderr=subprocess.STDOUT)
 if p.returncode:print((work/name).read_text()[-5000:]);raise RuntimeError(name)
 print('PASS',name,flush=True)
def inventory():
 r=json.loads((ROOT/'evidence/runtime.json').read_text());c=json.loads(gzip.decompress((ROOT/'evidence/runtime_cases.json.gz').read_bytes()));sites=json.loads((ROOT/'source/sites215.json').read_text())
 assert r['status']=='UNIVERSAL_MATHEMATICAL_PASS'and r['working_states']==215 and r['proved_cases']==r['expected_cases']==6176 and not r['failures']
 assert r['table_sha256']==sha(ROOT/'machine/k215.native.tm')and r['sites_sha256']==sha(ROOT/'source/sites215.json')
 assert r['checker_sha256']==sha(ROOT/'code/runtime/symbolic_runtime.py')and r['helper_sha256']==sha(ROOT/'code/runtime/independent_runtime.py')
 assert [(x['site_index'],x['positive'])for x in c]==[(i,b)for i,x in enumerate(sites)for b in((False,True)if x[1]=='CD'else(False,))]
 assert all(len(x['duration'])==13 and x['duration'][0]>0 and all(v>=0 for v in x['duration'])for x in c)
 assert sum(x['symbolic_steps']for x in c)==1753058 and min(x['duration'][0]for x in c)==6
 T=table(ROOT/'machine/k215.native.tm');mp={int(k):v for k,v in json.loads((ROOT/'code/inputs/legacy_mapping.json').read_text()).items()}
 for q in{q for q,b in T}|{254}:
  if q not in mp:mp[q]=q+1000
 rev={mp[q]:q for q,b in T};covered={tuple(y)for x in c for y in x['rows']}
 for block in r['blocks']:
  for ev in block['trace']:
   if ev[0]in('literal','unary'):covered.add(tuple(ev[1][:2]))
 assert {(rev[q],b)for q,b in covered}==set(T)
 print('PASS stored6176-case inventory, positive progress and all430-row coverage',flush=True);return c
def main():
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--runtime',action='store_true');ap.add_argument('--secondary-runtime',action='store_true');ap.add_argument('--work',type=Path,help='New output directory outside this packet');a=ap.parse_args()
 if not __debug__ or sys.flags.optimize:raise RuntimeError('Run Python with assertions enabled; -O and -OO are not permitted')
 files=json.loads((ROOT/'manifest.json').read_text())['files'];actual={str(p.relative_to(ROOT))for p in ROOT.rglob('*')if p.is_file()and '__pycache__'not in p.parts and p.name!='manifest.json'};assert actual==set(files)
 for n,d in files.items():assert sha(ROOT/n)==d,n
 print('PASS exact manifest',flush=True);saved=inventory();pins=json.loads((ROOT/'provenance/input_pins.json').read_text());archive=ROOT/'parent'/pins['parent_archive'];assert sha(archive)==pins['parent_archive_sha256'];tmp=None
 if a.work:work=a.work.resolve();assert not work.is_relative_to(ROOT);work.mkdir(parents=True,exist_ok=False)
 else:tmp=tempfile.TemporaryDirectory(prefix='alternative215-');work=Path(tmp.name)
 with zipfile.ZipFile(archive)as z:
  for i in z.infolist():assert(work/i.filename).resolve().is_relative_to(work)and(i.external_attr>>16)&0o170000!=0o120000
  z.extractall(work)
 parent=work/pins['parent_directory'];run([parent/'verify.py'],work,'parent-default.log',cwd=parent)
 rebuilt=work/'rebuilt';reconstruct(parent,rebuilt)
 for n in('k215.native.tm','k215.normalized.tm','k215.tm'):assert(rebuilt/n).read_bytes()==(ROOT/'machine'/n).read_bytes()
 assert(rebuilt/'sites215.json').read_bytes()==(ROOT/'source/sites215.json').read_bytes();print('PASS exact17-row and DAG reconstruction',flush=True)
 source=source_check(parent);(work/'source.json').write_text(json.dumps(source,indent=2));print('PASS all-natural source correspondence',flush=True)
 seed=seed_check();(work/'seed.json').write_text(json.dumps(seed,indent=2));print('PASS exact716307-step blank root',flush=True)
 novelty=novelty_check(parent);(work/'novelty.json').write_text(json.dumps(novelty,indent=2));print('PASS nonisomorphism against all three baselines',flush=True)
 if a.runtime:
  dest=work/'runtime';run([ROOT/'code/validate_native.py',ROOT/'machine/k215.native.tm',ROOT/'source/sites215.json',dest],work,'runtime.log')
  r=json.loads((dest/'runtime.json').read_text());assert r['status']=='UNIVERSAL_MATHEMATICAL_PASS'and r['proved_cases']==6176;assert json.loads((dest/'runtime_cases.json').read_text())==saved;assert json.loads((dest/'startup.json').read_text())==json.loads(gzip.decompress((ROOT/'evidence/startup.json.gz').read_bytes()))
 sys.path.insert(0,str(ROOT/'secondary'));from verify_secondary import check as secondary_check
 secondary=secondary_check(parent,work/'secondary',fresh_runtime=a.secondary_runtime)
 result=dict(status='ALL_REQUESTED_ALTERNATIVE215_CHECKS_PASS',secondary=secondary,fresh_runtime=a.runtime,working_states=215,blank_seed=seed,source=source,scope='Materially different physical encoding and bootstrap; same calibrated logical calculus. Ordinary mathematical proof, no new proof-assistant endpoint.')
 (work/'result.json').write_text(json.dumps(result,indent=2));print(json.dumps(result,indent=2))
 if tmp:tmp.cleanup()
if __name__=='__main__':main()
