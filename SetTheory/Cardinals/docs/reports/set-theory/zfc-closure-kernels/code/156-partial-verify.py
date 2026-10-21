#!/usr/bin/env python3
"""Offline exact-K216 validation. Add --runtime for fresh unbounded symbolic replay."""
from pathlib import Path
import argparse,gzip,hashlib,json,subprocess,sys,tempfile,zipfile
ROOT=Path(__file__).resolve().parent
PARENT='K217_Dominated_Continuation_2026-10-20'
PARENT_SHA='4aa33f0c4844043d243fb7d01ef316d4b72de641864e5317525f7cfac7f5c809'
def need(ok,msg):
 if not ok:raise ValueError(msg)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def run(cmd,work,name,cwd=None):
 with(work/name).open('w')as log:r=subprocess.run([sys.executable,'-B',*map(str,cmd)],cwd=cwd,stdout=log,stderr=subprocess.STDOUT)
 if r.returncode:
  print((work/name).read_text()[-7000:]);raise RuntimeError('Failed: '+name)
 print('PASS',name,flush=True)
def inventory():
 C=json.loads(gzip.decompress((ROOT/'evidence/runtime_cases.json.gz').read_bytes()));S=json.loads((ROOT/'source/sites216.json').read_text());R=json.loads((ROOT/'evidence/runtime.json').read_text());M=json.loads((ROOT/'evidence/runtime_metrics.json').read_text())
 need(R['status']=='UNIVERSAL_MATHEMATICAL_PASS'and R['proved_cases']==R['expected_cases']==6176,'Unbounded receipt')
 need(R['table_sha256']==sha(ROOT/'machine/k216.native.tm')and R['sites_sha256']==sha(ROOT/'source/sites216.json'),'Exact runtime binding')
 need(R['checker_sha256']==sha(ROOT/'code/runtime/symbolic_runtime.py')and R['helper_sha256']==sha(ROOT/'code/runtime/independent_runtime.py'),'Checker/helper binding')
 need([(x['site_index'],x['positive'])for x in C]==[(i,b)for i,x in enumerate(S)for b in((False,True)if x[1]=='CD'else(False,))],'Complete ordered guarded cases')
 for c in C:need(len(c['duration'])==13 and c['duration'][0]>0 and all(x>=0 for x in c['duration']),'Positive affine duration')
 need(sum(c['symbolic_steps']for c in C)==M['symbolic_rules']==1709992,'Symbolic rule census');need(min(c['duration'][0]for c in C)==13,'Minimum positive progress')
 sys.path.insert(0,str(ROOT/'code'));from reconstruct216 import table
 T=table(ROOT/'machine/k216.native.tm');m={int(k):v for k,v in json.loads((ROOT/'code/inputs/legacy_mapping.json').read_text()).items()}
 for q in {q for q,b in T}|{254}:
  if q not in m:m[q]=q+1000
 rev={m[q]:q for q,b in T};covered={tuple(x)for c in C for x in c['rows']}
 for b in R['blocks']:
  for ev in b['trace']:
   if ev[0]in('literal','unary'):covered.add(tuple(ev[1][:2]))
 covered={(rev[q],b)for q,b in covered};need(covered==set(T),'All432 rows covered by symbolic runtime')
 print('PASS stored symbolic inventory and all432 row coverage (fresh derivation: --runtime)',flush=True);return C
def main():
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--runtime',action='store_true');ap.add_argument('--work',type=Path,help='Retain regenerated receipts/logs; directory must not exist');a=ap.parse_args()
 need(__debug__ and not sys.flags.optimize,'Assertions must be enabled')
 manifest=json.loads((ROOT/'manifest.json').read_text());files=manifest['files']
 actual={str(p.relative_to(ROOT))for p in ROOT.rglob('*')if p.is_file()and '__pycache__'not in p.parts and p.name!='manifest.json'}
 need(actual==set(files),'Manifest exact file inventory')
 for name,digest in files.items():need(sha(ROOT/name)==digest,'Manifest mismatch: '+name)
 print('PASS release manifest',len(files),'files',flush=True);saved=inventory()
 archive=ROOT/'parent'/f'{PARENT}.zip';need(sha(archive)==PARENT_SHA,'Pinned parent archive')
 temp=None
 if a.work:work=a.work.resolve();work.mkdir(parents=True,exist_ok=False)
 else:temp=tempfile.TemporaryDirectory(prefix='k216-replay-');work=Path(temp.name)
 with zipfile.ZipFile(archive)as z:
  for i in z.infolist():need((work/i.filename).resolve().is_relative_to(work),'Archive containment')
  z.extractall(work)
 base=work/PARENT
 run([base/'verify.py'],work,'parent-default.log',cwd=base)
 rebuilt=work/'rebuilt';run([ROOT/'code/reconstruct216.py','--parent',base,'--out',rebuilt],work,'reconstruction.log')
 for name in('k216.native.tm','k216.tm','prefold217.native.tm'):need((rebuilt/name).read_bytes()==(ROOT/'machine'/name).read_bytes(),'Exact reconstructed '+name)
 for name in('sites216.json','sites216.compact.json'):need((rebuilt/name).read_bytes()==(ROOT/'source'/name).read_bytes(),'Exact reconstructed '+name)
 source=work/'source';run([ROOT/'code/source_equivalence.py','--baseline',base/'machine/sites217.json','--candidate',ROOT/'source/sites216.json','--out',source],work,'source.log')
 for name in('recipe.json','ordinal_correspondence.json','verification.json'):need((source/name).read_bytes()==(ROOT/'evidence'/('source_'+name)).read_bytes(),'Exact source proof '+name)
 run([ROOT/'code/audit216.py','--out',work/'blank-marker.json'],work,'blank-marker.log')
 run([ROOT/'code/check_joint_fold.py','--old',ROOT/'machine/prefold217.native.tm','--new',ROOT/'machine/k216.native.tm','--keep','164','--drop','183','--radius','4','--fuel','20','--output',work/'fold-window.json'],work,'fold-window.log')
 fold=json.loads((work/'fold-window.json').read_text());need(fold['status']=='INDEPENDENT_ALL_TAPE_JOINT_DIAGRAM_PASS'and fold['inductive_window_contexts']==27527 and fold['nontrivial_contexts']==48,'All-tape fold census')
 if a.runtime:
  dest=work/'runtime';run([ROOT/'code/validate_native.py',ROOT/'machine/k216.native.tm',ROOT/'source/sites216.json',dest],work,'runtime.log')
  r=json.loads((dest/'runtime.json').read_text());need(r['status']=='UNIVERSAL_MATHEMATICAL_PASS'and r['proved_cases']==6176,'Fresh full runtime')
  need(json.loads((dest/'runtime_cases.json').read_text())==saved,'Exact freshly derived case receipts')
  need(r['table_sha256']==sha(ROOT/'machine/k216.native.tm')and r['sites_sha256']==sha(ROOT/'source/sites216.json'),'Fresh exact hash binding')
  need(json.loads((dest/'startup.json').read_text())==json.loads(gzip.decompress((ROOT/'evidence/startup.json.gz').read_bytes())),'Exact fresh startup trace')
  print('PASS all6176 freshly derived cases and whole startup match delivered evidence',flush=True)
 result={'status':'ALL_REQUESTED_K216_CHECKS_PASS','working_states':216,'rows':432,'blank_startup_steps':313133,'source_occurrences':4751,'runtime_cases':6176,'fresh_runtime':a.runtime,'native_sha256':sha(ROOT/'machine/k216.native.tm'),'canonical_sha256':sha(ROOT/'machine/k216.tm'),'proof_assistant_endpoint':'No new Lean/Rocq or internal-PA endpoint for these bytes.'}
 (work/'result.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
 if a.work:print('Regenerated evidence:',work)
 if temp:temp.cleanup()
if __name__=='__main__':main()
