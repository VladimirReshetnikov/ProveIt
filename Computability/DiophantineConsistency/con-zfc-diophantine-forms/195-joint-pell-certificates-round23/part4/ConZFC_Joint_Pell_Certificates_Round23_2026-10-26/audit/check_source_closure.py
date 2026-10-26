"""Exact frozen dependency inventories and relative active source-pin closure.
No imported producer code; ordinary proof validity is reviewed separately.
"""
import hashlib,json,posixpath,sys
from pathlib import Path
root=Path(sys.argv[1]) if len(sys.argv)>1 else Path('/release')
expected_path=Path(sys.argv[2]) if len(sys.argv)>2 else root/'audit/EXPECTED_CLOSURE.json'
def need(q,msg):
 if not q:raise ValueError(msg)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def resolve(base,rel):
 p=posixpath.normpath(posixpath.join(base,rel));need(not(p=='..' or p.startswith('../') or p.startswith('/')),'source pin escapes release: '+p);return p
def record(path,meta):
 p=root/path;need(p.is_file(),'missing dependency '+path);need(sha(p)==meta['sha256'],'changed dependency '+path)
 if 'bytes' in meta:need(p.stat().st_size==meta['bytes'],'dependency size '+path)
 return {'path':path,'sha256':meta['sha256']}
expected=json.loads(expected_path.read_text());inventories=[]
for group in expected['groups']:
 base=group['path'];files=group['files'];actual={p.relative_to(root/base).as_posix() for p in (root/base).rglob('*') if p.is_file() and '__pycache__' not in p.parts and p.suffix!='.pyc'}
 need(actual==set(files),'frozen source component exact file census '+base)
 for rel,meta in files.items():record(resolve(base,rel),meta)
 inventories.append({'path':base,'files':len(files),'source_description':group['source_description']})
pins=[];historical_metadata=[];relocated=[]
relocations=expected.get('relocations',{})
for p in sorted(root.rglob('SOURCE_PINS.json')):
 if '__pycache__' in p.parts:continue
 obj=json.loads(p.read_text());base=p.parent.relative_to(root).as_posix();rel=p.relative_to(root).as_posix()
 if rel.endswith('incoming210/compact11/comparison115/SOURCE_PINS.json'):
  need(sha(p)=='9a0998711d0e8fba55f3a21abb3a5f320ad50b3315df96c35ca29ea94b8a6f08' and sha(p.parent.parent/'README.md')=='7d25594e6d18d827e1a5d8c4824d658ed760e06393fd67e5c1095fc7cc9357fb','exact historical comparison exclusion evidence')
  historical_metadata.append({'path':rel,'role':'Unchanged historical five-circuit source pins; enclosing compact11 README explicitly retains only comparison115 graph/binding, not its independent parent/proof package. Not a selected theorem dependency.'});continue
 elif isinstance(obj,dict) and isinstance(obj.get('files'),list):rs=[(r['path'],r) for r in obj['files']]
 elif isinstance(obj,dict) and isinstance(obj.get('dependencies'),dict):rs=obj['dependencies'].items()
 elif isinstance(obj,dict) and isinstance(obj.get('sources'),list):rs=[(r['local_path'],r) for r in obj['sources']]
 elif isinstance(obj,dict) and obj and all(isinstance(v,str) and len(v)==64 for v in obj.values()):rs=[(k,{'sha256':v}) for k,v in obj.items()]
 elif isinstance(obj,dict) and isinstance(obj.get('retained_proof_closure'),list):
  base=posixpath.dirname(base);rs=[(r['local_path'],r) for r in obj['retained_proof_closure']]
 elif isinstance(obj,dict) and 'incoming_equation' in obj and 'incoming_equation_sha256' in obj:
  rs=[(obj['incoming_equation'],{'sha256':obj['incoming_equation_sha256']}),('incoming210/SHA256SUMS',{'sha256':obj['incoming210_sha256sums_sha256']}),('conservative209/equation.json',{'sha256':obj['conservative_reciprocal_source_sha256']})]
  historical_metadata.append({'path':rel,'role':'credited archive sizes and digests are provenance; all current353 incoming files separately retained and SHA256SUMS-authenticated'})
 elif isinstance(obj,dict) and obj and all(isinstance(v,dict) and set(v)=={'equation','translation'} for v in obj.values()):
  historical_metadata.append({'path':rel,'role':'historical parent equation/translation hash inventory; exact byte-preserved ancestry and active reconstructed source bindings checked separately'});continue
 else:raise ValueError('Unreviewed source-pin schema: '+rel)
 for name,meta in rs:
  original=resolve(base,name)
  if rel in relocations:
   target=resolve(relocations[rel]['target_component'],name);r=record(target,meta);r['historical_relative_target']=original;relocated.append({'pin':rel,'original':original,'resolved':target,'sha256':meta['sha256']})
  else:r=record(original,meta)
  r['pin']=rel;pins.append(r)
if relocations:
 receipt_path=Path(sys.argv[3]) if len(sys.argv)>3 else root/'audit/SOURCE_RELOCATIONS.json'
 declared=json.loads(receipt_path.read_text())
 need(declared['status']=='PASS' and declared['files']==relocated,'complete exact declared source relocation receipt')
# Four active height source bindings are rooted in the enclosing release.
height=[]
p=root/'height_one/SOURCE_BINDINGS.json'
if p.is_file():
 for r in json.loads(p.read_text()):
  need(r['binding']=='byte_identical','height source binding mode');local=resolve('height_one',r['local']);enclosing=resolve('',r['enclosing_source']);record(local,r);record(enclosing,r);height.append({'local':local,'enclosing':enclosing,'sha256':r['sha256']})
reciprocal=[]
p=root/'reciprocal/SOURCE_BINDING.json'
if p.is_file():
 b=json.loads(p.read_text());component=resolve('reciprocal',b['ordinary_proof_component']);need(component=='signed','current reciprocal sibling signed proof component')
 local=resolve('reciprocal',b['source']);other=resolve(component,b['equation_path']);record(local,{'sha256':b['sha256']});record(other,{'sha256':b['sha256']})
 certificate=resolve(component,b['certificate_path']);record(certificate,{'sha256':b['certificate_sha256']});record('reciprocal/source/pell209_affine_certificate.json',{'sha256':b['certificate_sha256']})
 proof=resolve(component,b['ordinary_proof_path']);need((root/proof).is_file(),'reciprocal ordinary proof closure')
 reciprocal.append({'local':local,'sibling':other,'sha256':b['sha256'],'certificate':certificate,'certificate_sha256':b['certificate_sha256'],'ordinary_proof':proof})
# Additional proof texts fill explicitly documented historical source paths.
supp=[]
p=root/'source_supplements/SOURCE_BINDINGS.json'
if p.is_file():
 for r in json.loads(p.read_text())['files']:supp.append(record(resolve('source_supplements',r['local']),r))
sumfiles=[]
for p in sorted(root.rglob('SHA256SUMS')):
 base=p.parent.relative_to(root).as_posix();count=0
 for line in p.read_text().splitlines():
  if not line.strip():continue
  digest,rel=line.split(maxsplit=1);rel=rel.lstrip('*');need(len(digest)==64 and all(c in '0123456789abcdef' for c in digest),'SHA256SUMS digest')
  record(resolve(base,rel),{'sha256':digest});count+=1
 sumfiles.append({'path':p.relative_to(root).as_posix(),'files':count})
print(json.dumps({'status':'PASS','sha256sum_manifests':sumfiles,'exact_frozen_inventories':inventories,'exact_frozen_files':sum(x['files'] for x in inventories),'relative_source_pins_checked':len(pins),'source_pins':pins,'explicit_relocated_source_pins':relocated,'height_source_bindings':height,'reciprocal_source_bindings':reciprocal,'source_supplements':supp,'historical_metadata_schemas':historical_metadata,'boundary':'Exact current source/proof/code/numeral inventories and declared relative bindings. This authenticates presence and bytes; finite replay and ordinary theorem review are separate evidence.'},indent=2))
