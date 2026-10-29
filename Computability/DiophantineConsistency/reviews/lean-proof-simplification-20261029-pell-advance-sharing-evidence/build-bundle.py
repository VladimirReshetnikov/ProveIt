from pathlib import Path
import hashlib,json,subprocess,zipfile
r=Path('/dev/shm/pell-unit-advance-sharing-refresh');out=Path('/tmp/pell-unit-advance-sharing-evidence');w=Path('Computability/DiophantineConsistency/Lean/DiophantineConsistency');h=lambda b:hashlib.sha256(b).hexdigest();files={}
def add(n,b):
 assert n not in files,n;files[n]=b
for p in r.rglob('*'):
 if p.is_file() and p.suffix in ('.lean','.json','.log','.py','.time','.txt') and not any(x.startswith('paired-') for x in p.relative_to(r).parts):add('prototype/'+str(p.relative_to(r)),p.read_bytes())
for phase,rev in [('baseline','e9c6492417^'),('final','e9c6492417')]:
 for n in ['ArithmeticPellKnownUnit.lean','ArithmeticPellFirstNorm.lean']:
  b=subprocess.check_output(['git','show',rev+':'+str(w/n)]);assert b==(r/phase/'DiophantineConsistency'/n).read_bytes();add('commit/'+phase+'/'+n,b)
for n in ['ArithmeticPellClassification','ArithmeticPellCongruences','ArithmeticGcdNormalization','ArithmeticPellHalfIndex']:add('sources/'+n+'.lean',(w/(n+'.lean')).read_bytes())
for name,p in [('pell-positive-reflect-final-records.json','/tmp/pell-positive-reflect/final-records.json'),('pell-y-add-final-records.json','/tmp/pell-y-add/final-records.json'),('gcd-product-positivity-final-records.json','/tmp/gcd-product-positivity/final-records.json'),('four-positive-wrappers-upstream-records.json','/tmp/four-positive-wrappers/upstream-records.json')]:add('providers/'+name,Path(p).read_bytes())
for name in ['review.txt','audit.py','audit.log']:add('independent/'+name,Path('/tmp/pell-unit-advance-sharing-peer-'+name).read_bytes())
archive=out/'inputs-and-logs.zip'
with zipfile.ZipFile(archive,'w',compression=zipfile.ZIP_DEFLATED,compresslevel=9) as z:
 for n,b in sorted(files.items()):z.writestr(n,b)
review=Path('/tmp/pell-unit-advance-sharing-peer-review.txt').read_bytes();(out/'independent-review.txt').write_bytes(review)
m={'schema':'lean-proof-simplification-evidence-v1','source_commit':subprocess.check_output(['git','rev-parse','e9c6492417'],text=True).strip(),'source_parent':subprocess.check_output(['git','rev-parse','e9c6492417^'],text=True).strip(),'scope':'Reuse the generic Pell unit-advance equivalence','validation':'Paired KnownUnit, FirstNorm and four direct client builds succeed with four source-matched external project providers. Three client objects are identical; FirstIndex differs. Six-object-pinned probes give 38 common declaration/type/axiom reports and equal default simp/instance registrations. The generic equivalence changes from private to public with the same type and axioms.','limitations':['Source-matched direct provider receipts and selected direct clients do not establish a source-current transitive closure; broader downstream clients were not rebuilt.','Reports and sampled registrations do not establish equality of proof bodies or all persistent extensions. One client object differs.','Compiled objects are excluded; full replay requires the original external build environment and object dependencies. Earlier exploratory baseline-only builds using an older Classification object are not part of this refreshed lane.'],'archive':archive.name,'archive_sha256':h(archive.read_bytes()),'independent_review':{'path':'independent-review.txt','sha256':h(review)},'members':{n:{'bytes':len(b),'sha256':h(b)} for n,b in sorted(files.items())}}
(out/'BUNDLE.json').write_text(json.dumps(m,indent=2)+'\n');print(len(files),'members',archive.stat().st_size,'bytes',m['archive_sha256'])
