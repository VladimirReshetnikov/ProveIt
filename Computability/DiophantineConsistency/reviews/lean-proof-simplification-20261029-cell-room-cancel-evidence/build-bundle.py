from pathlib import Path
import hashlib,json,subprocess,zipfile
r=Path('/dev/shm/cell-room-cancel'); out=Path('/tmp/cell-room-cancel-evidence'); w=Path('Computability/DiophantineConsistency/Lean/DiophantineConsistency'); h=lambda b:hashlib.sha256(b).hexdigest(); files={}
def add(n,b):
 assert n not in files,n
 files[n]=b
for p in r.rglob('*'):
 if p.is_file() and p.suffix in ('.lean','.json','.log','.py','.time','.txt') and not any(x.startswith('objects-') for x in p.relative_to(r).parts): add('prototype/'+str(p.relative_to(r)),p.read_bytes())
for phase,rev in [('baseline','8f6f17c148^'),('final','8f6f17c148')]:
 n='ArithmeticCellTransfer.lean'; rel=str(w/n); b=subprocess.check_output(['git','show',rev+':'+rel]); assert b==(r/phase/'DiophantineConsistency'/n).read_bytes();add('commit/'+phase+'/'+n,b)
names=['ArithmeticStandardCasts','ArithmeticModularCancellation','ArithmeticCyclicWord','ArithmeticCellLabels','ArithmeticBinaryCarry','ArithmeticBinaryPopulation','ArithmeticWindowDigits','ArithmeticCellDecoding']
for n in names:add('sources/'+n+'.lean',(w/(n+'.lean')).read_bytes())
for name,p in [('binary-half-direct-final-records.json','/tmp/binary-half-direct/final-records.json'),('binary-half-direct-final-supplement-records.json','/tmp/binary-half-direct/final-supplement-records.json'),('shared-modular-cancel-records.json','/tmp/shared-modular-cancel/records.json'),('cell-no-carry-refresh-records.json','/dev/shm/cell-no-carry/refresh-records.json')]:add('providers/'+name,Path(p).read_bytes())
for name in ['review.txt','audit.py','audit.log']:
 p=Path('/tmp/cell-room-cancel-peer-'+name);add('independent/'+name,p.read_bytes())
archive=out/'inputs-and-logs.zip'
with zipfile.ZipFile(archive,'w',compression=zipfile.ZIP_DEFLATED,compresslevel=9) as z:
 for n,b in sorted(files.items()):z.writestr(n,b)
review=Path('/tmp/cell-room-cancel-peer-review.txt').read_bytes();(out/'independent-review.txt').write_bytes(review)
manifest={'schema':'lean-proof-simplification-evidence-v1','source_commit':subprocess.check_output(['git','rev-parse','8f6f17c148'],text=True).strip(),'source_parent':subprocess.check_output(['git','rev-parse','8f6f17c148^'],text=True).strip(),'scope':'Cancel the cell-width factor in cell_room','validation':'Paired target and direct ArithmeticCellDecoding builds succeed. Target has 59 namespace declarations and client 71 with equal type/axiom reports and sampled default simp/instance registrations; differing client objects were both pinned in the probes. Four direct and three sampled extra providers have source-matched prior producer rows. The target logs are empty and both client logs contain the same existing unused-H warning.','limitations':['Only the target and its sole tracked direct Lean client were rebuilt; the wider transitive dependency closure is cached. Producer associations do not establish source-current transitive closure.','The matching declaration/type/axiom and sampled registration reports do not establish equality of proof bodies or all persistent extensions. Client objects differ.','Compiled objects are excluded. The archived build and probe records include original temporary paths and hashes; full replay requires their external object dependencies and environment.'],'archive':archive.name,'archive_sha256':h(archive.read_bytes()),'independent_review':{'path':'independent-review.txt','sha256':h(review)},'members':{n:{'bytes':len(b),'sha256':h(b)} for n,b in sorted(files.items())}}
(out/'BUNDLE.json').write_text(json.dumps(manifest,indent=2)+'\n')
print(len(files),'members',archive.stat().st_size,'bytes',manifest['archive_sha256'])
