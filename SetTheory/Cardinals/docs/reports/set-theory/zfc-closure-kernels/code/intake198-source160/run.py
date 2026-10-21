#!/usr/bin/env python3
"""Nine selected Source160 leaves on copies; no wrapper, manifest or ancestor execution."""
from pathlib import Path,PurePosixPath
import argparse,subprocess,sys,json,shutil,zipfile,stat,hashlib,time

def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def dump(p,x):p.write_text(json.dumps(x,indent=2)+'\n')
def main():
 ap=argparse.ArgumentParser();ap.add_argument('--packet',type=Path,required=True);ap.add_argument('--output',type=Path,required=True);a=ap.parse_args();O=a.output.resolve();O.mkdir(parents=True,exist_ok=False);P=O/'packet';shutil.copytree(a.packet,P)
 parents=O/'parents';parents.mkdir()
 with zipfile.ZipFile(P/'parent/K216_Permuted_Commands_2026-10-21.zip')as z:
  for i in z.infolist():
   if i.is_dir():continue
   p=PurePosixPath(i.filename);assert not p.is_absolute()and'..'not in p.parts and not stat.S_ISLNK(i.external_attr>>16)
   t=parents/p;t.parent.mkdir(parents=True,exist_ok=True);t.write_bytes(z.read(i))
 parent=parents/'K216_Permuted_Commands_2026-10-21';assert parent.is_dir()
 selected=[p for p in(P/'code').rglob('*')if p.is_file()and(p.suffix=='.py'or p.name in('variants.json','legacy_mapping.json'))]
 for prefix in ['', 'secondary/']:
  D=P/prefix
  selected+=[D/'source/verify_source.py',D/'source/dag_recipe.json',D/'source/table_recipe.json',D/'source/sites215.json',D/'source/sites215.compact.json',D/'machine/k215.native.tm',D/'machine/prefold216.native.tm',D/'machine/k215.tm',D/'machine/canonicalization.json',D/'evidence/startup.json.gz']
 selected+=[parent/x for x in ['machine/k216.native.tm','machine/sites216.json','secondary/k216-120.native.tm','secondary/sites120.json']]
 def inputs():return {str(p.relative_to(O)):sha(p)for p in selected}
 before=inputs();dump(O/'before.json',before);jobs=[];logs=O/'logs';logs.mkdir()
 def run(name,args,cap):
  cmd=[sys.executable,'-B',*[str(x)for x in args]];start=time.monotonic()
  with(logs/(name+'.stdout')).open('w')as out,(logs/(name+'.stderr')).open('w')as err:
   try:r=subprocess.run(cmd,stdout=out,stderr=err,timeout=cap);rc=r.returncode;timeout=False
   except subprocess.TimeoutExpired:rc=None;timeout=True
  row={'name':name,'argv':cmd,'returncode':rc,'timed_out':timeout,'seconds':time.monotonic()-start,'cap_seconds':cap};jobs.append(row);dump(O/'progress.json',jobs);print(name,rc,round(row['seconds'],3),flush=True);assert rc==0 and not timeout
 for v,pre,ps in [('210','',parent/'machine/sites216.json'),('120','secondary',parent/'secondary/sites120.json')]:
  D=P/pre
  run('reconstruct'+v,[P/'code/reconstruct215.py','--parent',parent,'--out',O/('rebuilt'+v),'--variant',v],90)
  run('source'+v,[D/'source/verify_source.py','--baseline',ps,'--candidate',D/'source/sites215.json','--recipe',D/'source/dag_recipe.json','--out',O/('source'+v)],90)
  assert json.loads((O/('source'+v)/'verification.json').read_text())['status']=='ALL_NATURAL_SOURCE_BISIMULATION_PASS'
  for name in ['sites215.json','sites215.compact.json']:
   assert(O/('rebuilt'+v)/name).read_bytes()==(D/'source'/name).read_bytes()
  for name in ['prefold216.native.tm','k215.native.tm','k215.tm']:
   assert(O/('rebuilt'+v)/name).read_bytes()==(D/'machine'/name).read_bytes()
  run('blank-marker'+v,[P/'code/audit215.py','--out',O/('blank-marker'+v+'.json'),'--variant',v],90)
  assert json.loads((O/('blank-marker'+v+'.json')).read_text())['status']=='MARKER_LEMMA_CANONICAL_ISOMORPHISM_AND_WHOLE_BLANK_PASS'
  run('fold'+v,[P/'code/check_joint_fold.py','--old',D/'machine/prefold216.native.tm','--new',D/'machine/k215.native.tm','--keep','164','--drop','183','--output',O/('fold'+v+'.json')],90)
  assert json.loads((O/('fold'+v+'.json')).read_text())['status']=='INDEPENDENT_ALL_TAPE_JOINT_DIAGRAM_PASS'
 D=P/'secondary';run('runtime120',[P/'code/validate_native.py',D/'machine/k215.native.tm',D/'source/sites215.json',O/'runtime120'],360)
 r=json.loads((O/'runtime120/runtime.json').read_text());assert r['status']=='UNIVERSAL_MATHEMATICAL_PASS'and r['proved_cases']==r['expected_cases']==6176 and r['working_states']==215 and not r['failures']
 after=inputs();assert before==after
 actual={'status':'NINE_SELECTED_SOURCE160_LEAVES_PASS','jobs':jobs,'before':before,'after':after,'runtime120':r,'scope':'New finite reconstruction/source/fold/blank checks for both variants and fresh unbounded secondary120. Primary210 full runtime transfers by separately checked literal state isomorphism to acceptedK215, not by a duplicate run. No wrapper, checksum manifest, nested ancestor suite, search, C++ or proof-assistant job.'}
 dump(O/'actual.json',actual);print(actual['status'],flush=True)
if __name__=='__main__':main()
