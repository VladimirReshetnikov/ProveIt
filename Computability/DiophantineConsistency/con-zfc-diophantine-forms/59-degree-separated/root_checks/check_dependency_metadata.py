#!/usr/bin/env python3
"""Independent read-only cross-family pins, binding paths, and metadata checks."""
from pathlib import Path
import ast,gzip,hashlib,json,re
R=Path(__file__).resolve().parents[1];O=R/'root_checks'
F=['encoding','sun','nine','signed','positive','short'];result={'scope':'Active authored family metadata only; preserved historical relative paths are classified separately.','source_pins':[],'active_binding_paths':[],'coherent_tuples':[],'manifest_mismatches':[],'manifest_unlisted_candidate_files':[],'assert_nodes':[],'external_imports':[],'absolute_path_hits':[]}
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def pin(fam,name,rec):
 p=R/fam/name
 row={'family':fam,'path':name,'exists':p.is_file(),'sha256_matches':p.is_file() and sha(p)==rec['sha256']}
 expected=rec.get('git_blob_sha') or rec.get('git_blob_sha1')
 if expected and p.is_file():
  raw=p.read_bytes();row['git_blob_matches']=hashlib.sha1(b'blob '+str(len(raw)).encode()+b'\0'+raw).hexdigest()==expected
 result['source_pins'].append(row)
def checkpath(fam,field,value,base,expected=None):
 p=base/value;exists=p.is_file();row={'family':fam,'field':field,'path':str(p.relative_to(R)) if p.is_relative_to(R) else str(p),'exists':exists}
 if expected is not None:row['hash_matches']=exists and sha(p)==expected
 result['active_binding_paths'].append(row)
for fam,key,pathkey in [('sun','files','local_path'),('signed','files','local_path'),('nine','imported','path'),('positive','sources','path')]:
 d=json.loads((R/fam/'SOURCE_PINS.json').read_text())
 for rec in d[key]:
  pin(fam,rec[pathkey],rec)
d=json.loads((R/'encoding/SOURCE_PINS.json').read_text());pin('encoding',d['local_file'],d)
for name,rec in json.loads((R/'short/SOURCE_PINS.json').read_text())['text_sources'].items():pin('short','upstream/'+name,rec)
for rec in json.loads((R/'signed/RATIO_SOURCE_PINS.json').read_text()):pin('signed',rec['local_path'],rec)
for fam,filename in [('signed','FIXED_BINDING.json'),('positive','COEFFICIENT_BINDING.json'),('short','COEFFICIENT_BINDING.json')]:
 base=R/fam;b=json.loads((base/filename).read_text())
 for key in ['source_binding_path','source_adapter_proof_path','source_reference_proof_path']:
  if key in b:
   hkey={'source_binding_path':'source_binding_sha256','source_adapter_proof_path':'source_adapter_proof_sha256' if fam=='signed' else 'source_adapter_sha256'}.get(key)
   checkpath(fam,key,b[key],base,b.get(hkey)if hkey else None)
 for x in b['payloads']:checkpath(fam,'payload:'+x['name'],x['path'],base,x['gzip_sha256'])
base=R/'nine/coefficients/old_tuple';b=json.loads((base/'COEFFICIENT_BINDING.json').read_text())
for key,hkey in [('source_binding_path','source_binding_sha256'),('source_adapter_proof_path','source_adapter_sha256'),('complete_interface_proof_path','complete_interface_proof_sha256')]:checkpath('nine',key,b[key],base,b.get(hkey))
base=R/'nine/coefficients';b=json.loads((base/'COEFFICIENT_BINDING.json').read_text())
for key in ['definition_source','matching_source','parent_file']:checkpath('nine native comparisons',key,b[key],base,b.get('parent_sha256')if key=='parent_file'else None)
for x in b['ports']:checkpath('nine native comparisons','payload:'+x['port'],x['gzip_file'],base,x['gzip_sha256'])
# Verify all old31 payload bytes agree across families, not just their labels.
for fam,base in [('sun',R/'sun/data'),('signed',R/'signed/coefficients'),('positive',R/'positive/coefficients'),('short',R/'short/coefficients'),('nine primary',R/'nine/coefficients/old_tuple')]:
 vals={n:int.from_bytes(gzip.decompress((base/(n+'.bin.gz')).read_bytes()),'little')for n in ['beta','K','MC','MF_source']}
 hashes={n:hashlib.sha256(gzip.decompress((base/(n+'.bin.gz')).read_bytes())).hexdigest()for n in vals}
 B=1<<1064921;native=vals['MF_source']-(B-1)
 result['coherent_tuples'].append({'family':fam,'raw_hashes':hashes,'beta_correct':vals['beta']==B-1,'native_mask_range':0<native<B-1 and 0<vals['MC']<B-1,'population':native.bit_count()+vals['MC'].bit_count(),'mask_phases':vals['MC']%4==2 and native%8==4})
for fam,fn in [('encoding','RELEASE_FILES.json'),('signed','ARTIFACT_HASHES.json'),('short','MANIFEST.json')]:
 d=json.loads((R/fam/fn).read_text());rs=[(x['path'],x['sha256'])for x in d['files']]if fam=='encoding'else d.items()
 for name,h in rs:
  p=R/fam/name
  if not p.is_file() or sha(p)!=h:result['manifest_mismatches'].append({'family':fam,'manifest':fn,'file':name,'exists':p.is_file()})
 if fam in ['signed','short']:
  for p in (R/fam).rglob('*'):
   name=str(p.relative_to(R/fam))
   if p.is_file()and p.suffix in ['.py','.json','.md','.tex','.pdf','.gz','.lean']and'__pycache__'not in p.parts and p.name!=fn and name not in d:result['manifest_unlisted_candidate_files'].append({'family':fam,'manifest':fn,'file':name})
canonical_python={'encoding':['verify_split.py','test_split.py'],'sun':['build.py','circuit.py','source_audit.py','independent_check.py','reproduce.py','evaluate.py'],'nine':['build_nine.py','circuit.py','verify_nine.py','independent_review.py'],'signed':['build_jones.py','circuit.py','b4_support.py','split_source.py','check_jones.py','check_source_minimum_independent.py','split/verify_split.py'],'positive':['build_ordinary_merger.py','check_ordinary_merger.py','check_merger_independent.py'],'short':['build.py','audit.py']}
for fam,fs in canonical_python.items():
 for name in fs:
  p=R/fam/name;t=ast.parse(p.read_text())
  for n in ast.walk(t):
   if isinstance(n,ast.Assert):result['assert_nodes'].append({'family':fam,'file':name,'line':n.lineno,'test':ast.unparse(n.test)})
   if isinstance(n,(ast.Import,ast.ImportFrom)):
    modules=[a.name for a in n.names]if isinstance(n,ast.Import)else[n.module or '']
    for mod in modules:
     if mod.split('.')[0]in ['numpy','sympy']:result['external_imports'].append({'family':fam,'file':name,'module':mod})
  hits=re.findall(r'/(?:workspace|tmp)/[^\s\"\']+',p.read_text())
  for hit in hits:result['absolute_path_hits'].append({'family':fam,'file':name,'path':hit})
# Top-level literal circuits bind relative to themselves, not to the caller cwd.
for fam,folder in [('short','circuits'),('signed','generated'),('positive','')]:
 for p in sorted((R/fam/folder).glob('*.json')):
  d=json.loads(p.read_text())
  if isinstance(d,dict) and isinstance(d.get('coefficient_binding'),str):checkpath(fam,'circuit binding: '+p.name,d['coefficient_binding'],p.parent)
result['inert_historical_notes']=[{'file':'sun/data/coefficients_binding.json','field':'complete_interface_proof','value':'../../coefficients/COEFFICIENT_PROOF.md','classification':'Preserved historical metadata, explicitly overridden by INSTANCE.json; current proof exists at sun/upstream/COEFFICIENT_PROOF.md and is source-pinned.'},{'file':'encoding/explore.py','classification':'Optional discovery provenance only; contains a legacy sibling wave7 fallback, not imported by canonical replay.'},{'file':'*/coefficients/original_binding.json','classification':'Historical byte-for-byte provenance, not active coefficient adapters.'}]
result['old31_tuple_bytes_equal']=all(x['raw_hashes']==result['coherent_tuples'][0]['raw_hashes']for x in result['coherent_tuples'])
valid=all(x['exists']and x.get('hash_matches',True)for x in result['active_binding_paths'])and all(x['exists']and x['sha256_matches']and x.get('git_blob_matches',True)for x in result['source_pins'])and result['old31_tuple_bytes_equal']and all(x['beta_correct']and x['native_mask_range']and x['population']==1064921 and x['mask_phases']for x in result['coherent_tuples'])and not result['absolute_path_hits']
result['status']=('PASS_WITH_MANIFEST_WARNINGS'if result['manifest_mismatches']or result['manifest_unlisted_candidate_files']else'PASS')if valid else'FAIL'
(O/'DEPENDENCY_METADATA.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items()if k not in ['source_pins','active_binding_paths','coherent_tuples']},indent=2));print('source pins',len(result['source_pins']),'binding path checks',len(result['active_binding_paths']))

if not valid or result["manifest_mismatches"]:
 raise ValueError("Active metadata, manifest, binding or provenance audit failed")
