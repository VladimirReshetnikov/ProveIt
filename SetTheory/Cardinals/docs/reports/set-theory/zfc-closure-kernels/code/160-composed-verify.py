#!/usr/bin/env python3
"""Offline exact-K215 checks. --runtime freshly derives primary unbounded cases.
Add --secondary-runtime to freshly derive the second machine's cases too.
Default checks construction, inherited calibration, source proofs, blank runs,
all-tape folds and stored inventories; it is not a fresh runtime derivation.
"""
from pathlib import Path
import argparse,gzip,hashlib,json,subprocess,sys,tempfile,zipfile
ROOT=Path(__file__).resolve().parent
PARENT='K216_Permuted_Commands_2026-10-21'
def need(ok,msg):
 if not ok:raise ValueError(msg)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def run(cmd,work,name,cwd=None):
 with(work/name).open('w')as log:r=subprocess.run([sys.executable,'-B',*map(str,cmd)],cwd=cwd,stdout=log,stderr=subprocess.STDOUT)
 if r.returncode:
  print((work/name).read_text()[-7000:]);raise RuntimeError('Failed: '+name)
 print('PASS',name,flush=True)
def readz(p):return json.loads(gzip.decompress(p.read_bytes()))
def inventory(D):
 C=readz(D/'evidence/runtime_cases.json.gz');S=json.loads((D/'source/sites215.json').read_text());R=json.loads((D/'evidence/runtime.json').read_text());M=json.loads((D/'evidence/runtime_metrics.json').read_text())
 need(R['status']=='UNIVERSAL_MATHEMATICAL_PASS'and R['proved_cases']==R['expected_cases']==6176 and R['working_states']==215 and not R['failures'],'Unbounded receipt')
 need(R['table_sha256']==sha(D/'machine/k215.native.tm')and R['sites_sha256']==sha(D/'source/sites215.json'),'Exact runtime binding')
 need(R['checker_sha256']==sha(ROOT/'code/runtime/symbolic_runtime.py')and R['helper_sha256']==sha(ROOT/'code/runtime/independent_runtime.py'),'Checker/helper binding')
 need(len(S)==4751 and [(x['site_index'],x['positive'])for x in C]==[(i,b)for i,x in enumerate(S)for b in((False,True)if x[1]=='CD'else(False,))],'Complete ordered guarded cases')
 for c in C:need(len(c['duration'])==13 and c['duration'][0]>0 and all(x>=0 for x in c['duration']),'Positive affine duration')
 need(sum(c['symbolic_steps']for c in C)==M['symbolic_rules'],'Symbolic rule census');need(min(c['duration'][0]for c in C)==M['minimum_duration_constant'],'Minimum positive progress')
 sys.path.insert(0,str(ROOT/'code'));from reconstruct215 import table
 T=table(D/'machine/k215.native.tm');m={int(k):v for k,v in json.loads((ROOT/'code/inputs/legacy_mapping.json').read_text()).items()}
 for q in {q for q,b in T}|{254}:
  if q not in m:m[q]=q+1000
 rev={m[q]:q for q,b in T};covered={tuple(x)for c in C for x in c['rows']}
 for b in R['blocks']:
  for ev in b['trace']:
   if ev[0]in('literal','unary'):covered.add(tuple(ev[1][:2]))
 covered={(rev[q],b)for q,b in covered};need(covered==set(T)and len(T)==430,'All430 rows covered by symbolic runtime')
 print('PASS stored symbolic inventory and all430 row coverage (fresh derivation: runtime option)',flush=True);return C

def main():
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--runtime',action='store_true');ap.add_argument('--secondary-runtime',action='store_true');ap.add_argument('--work',type=Path,help='Retain receipts/logs; directory must not exist');a=ap.parse_args()
 need(__debug__ and not sys.flags.optimize,'Assertions must be enabled')
 manifest=json.loads((ROOT/'manifest.json').read_text());files=manifest['files']
 actual={str(p.relative_to(ROOT))for p in ROOT.rglob('*')if p.is_file()and '__pycache__'not in p.parts and p.name!='manifest.json'}
 need(actual==set(files),'Manifest exact file inventory')
 for name,digest in files.items():need(sha(ROOT/name)==digest,'Manifest mismatch: '+name)
 print('PASS release manifest',len(files),'files',flush=True)
 config=json.loads((ROOT/'code/variants.json').read_text());saved={p:inventory(ROOT/x['directory'])for p,x in config.items()}
 archive=ROOT/'parent'/f'{PARENT}.zip';pins=json.loads((ROOT/'provenance/input_pins.json').read_text());need(sha(archive)==pins['parent_archive_sha256'],'Pinned parent archive')
 temp=None
 if a.work:
  work=a.work.resolve();need(not work.is_relative_to(ROOT),'Work directory must be outside sealed packet');work.mkdir(parents=True,exist_ok=False)
 else:temp=tempfile.TemporaryDirectory(prefix='k215-replay-');work=Path(temp.name)
 with zipfile.ZipFile(archive)as z:
  for i in z.infolist():
   need((work/i.filename).resolve().is_relative_to(work),'Archive containment')
   need((i.external_attr>>16)&0o170000!=0o120000,'No archive symlinks')
  z.extractall(work)
 base=work/PARENT;run([base/'verify.py'],work,'parent-default.log',cwd=base)
 for variant,cfg in config.items():
  D=ROOT/cfg['directory'];rebuilt=work/('rebuilt'+variant)
  run([ROOT/'code/reconstruct215.py','--variant',variant,'--parent',base,'--out',rebuilt],work,'reconstruction'+variant+'.log')
  for name in('k215.native.tm','k215.tm','prefold216.native.tm'):need((rebuilt/name).read_bytes()==(D/'machine'/name).read_bytes(),'Exact reconstructed '+name)
  for name in('sites215.json','sites215.compact.json'):need((rebuilt/name).read_bytes()==(D/'source'/name).read_bytes(),'Exact reconstructed '+name)
  source=work/('source'+variant);run([D/'source/verify_source.py','--baseline',base/cfg['parent_source'],'--candidate',D/'source/sites215.json','--recipe',D/'source/dag_recipe.json','--out',source],work,'source'+variant+'.log')
  need(json.loads((source/'verification.json').read_text())['status']=='ALL_NATURAL_SOURCE_BISIMULATION_PASS','Source proof')
  need((source/'ordinal_correspondence.json').read_bytes()==(D/'evidence/source_correspondence.json').read_bytes(),'Exact ordinal graph')
  run([ROOT/'code/audit215.py','--variant',variant,'--out',work/('blank-marker'+variant+'.json')],work,'blank-marker'+variant+'.log')
  run([ROOT/'code/check_joint_fold.py','--old',D/'machine/prefold216.native.tm','--new',D/'machine/k215.native.tm','--keep','164','--drop','183','--radius','4','--fuel','20','--output',work/('fold-window'+variant+'.json')],work,'fold-window'+variant+'.log')
  fold=json.loads((work/('fold-window'+variant+'.json')).read_text());need(fold['status']=='INDEPENDENT_ALL_TAPE_JOINT_DIAGRAM_PASS','All-tape positive fold')
  if (variant=='210'and a.runtime)or(variant=='120'and a.secondary_runtime):
   dest=work/('runtime'+variant);run([ROOT/'code/validate_native.py',D/'machine/k215.native.tm',D/'source/sites215.json',dest],work,'runtime'+variant+'.log')
   r=json.loads((dest/'runtime.json').read_text());need(r['status']=='UNIVERSAL_MATHEMATICAL_PASS'and r['proved_cases']==6176,'Fresh full runtime')
   need(json.loads((dest/'runtime_cases.json').read_text())==saved[variant],'Exact freshly derived case receipts')
   need(r['table_sha256']==sha(D/'machine/k215.native.tm')and r['sites_sha256']==sha(D/'source/sites215.json'),'Fresh exact hash binding')
   need(json.loads((dest/'startup.json').read_text())==readz(D/'evidence/startup.json.gz'),'Exact fresh startup trace')
 result={'status':'ALL_REQUESTED_K215_CHECKS_PASS','working_states':215,'rows':430,'primary_blank_startup_steps':95714,'secondary_blank_startup_steps':96284,'source_occurrences':4751,'runtime_cases_each':6176,'fresh_primary_runtime':a.runtime,'fresh_secondary_runtime':a.secondary_runtime,'proof_assistant_endpoint':'No new Lean/Rocq or internal-PA endpoint for these bytes.'}
 (work/'result.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
 if a.work:print('Regenerated evidence:',work)
 if temp:temp.cleanup()
if __name__=='__main__':main()
