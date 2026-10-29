from pathlib import Path
import hashlib,json,subprocess,zipfile
r=Path('/dev/shm/cell-sum-unique');out=Path('/tmp/cell-sum-unique-evidence');w=Path('Computability/DiophantineConsistency/Lean/DiophantineConsistency');h=lambda b:hashlib.sha256(b).hexdigest();files={}
def add(n,b):
 assert n not in files,n
 files[n]=b
for p in r.rglob('*'):
 if p.is_file() and p.suffix in ('.lean','.json','.log','.py','.time','.txt') and p.name not in ('test.log','test.time') and not any(x.startswith('obj-') for x in p.relative_to(r).parts):add('prototype/'+str(p.relative_to(r)),p.read_bytes())
for phase,rev in [('baseline','2e364c3e91^'),('final','2e364c3e91')]:
 n='ArithmeticCellLabels.lean';b=subprocess.check_output(['git','show',rev+':'+str(w/n)]);assert b==(r/phase/'DiophantineConsistency'/n).read_bytes();add('commit/'+phase+'/'+n,b)
for n in ['ArithmeticCellLocal','MFDoubledClause2011','ArithmeticStandardCasts','ArithmeticModularCancellation','ArithmeticCyclicWord','ArithmeticCellTransfer']:add('sources/'+n+'.lean',(w/(n+'.lean')).read_bytes())
for name,p in [('high-digits-module-sharing-final-records.json','/tmp/high-digits-module-sharing/final-records.json'),('construction-share-bound-refresh-records.json','/tmp/construction-share/bound-refresh-records.json'),('binary-half-direct-final-supplement-records.json','/tmp/binary-half-direct/final-supplement-records.json'),('shared-modular-cancel-records.json','/tmp/shared-modular-cancel/records.json'),('cell-no-carry-refresh-records.json','/dev/shm/cell-no-carry/refresh-records.json')]:add('providers/'+name,Path(p).read_bytes())
for name in ['review.txt','audit.py','audit.log']:add('independent/'+name,Path('/tmp/cell-sum-unique-peer-'+name).read_bytes())
archive=out/'inputs-and-logs.zip'
with zipfile.ZipFile(archive,'w',compression=zipfile.ZIP_DEFLATED,compresslevel=9) as z:
 for n,b in sorted(files.items()):z.writestr(n,b)
review=Path('/tmp/cell-sum-unique-peer-review.txt').read_bytes();(out/'independent-review.txt').write_bytes(review)
m={'schema':'lean-proof-simplification-evidence-v1','source_commit':subprocess.check_output(['git','rev-parse','2e364c3e91'],text=True).strip(),'source_parent':subprocess.check_output(['git','rev-parse','2e364c3e91^'],text=True).strip(),'scope':'Use finite-sum characterization for selected cell','validation':'Paired target and sole tracked direct client ArithmeticCellTransfer builds pass with identical client objects and empty logs. Object-pinned probes report 76 common target declarations with identical types and axioms, six generated target proof names removed, and 59 identical client declarations; sampled global simp and instance registrations match. All five unchanged direct target/client provider source/object pairs have matching successful producer records.','limitations':['The target, direct client, and selected prior producer receipts do not establish a source-current transitive closure. Wider downstream clients were not rebuilt.','The six removed generated public proof names have no references in tracked Lean/Python search, but declaration reports and sampled registrations do not prove equality of proof bodies or all persistent extensions.','Compiled objects are omitted. Recorded build and probe paths refer to original temporary directories; full replay requires the external environment and object dependencies.'],'archive':archive.name,'archive_sha256':h(archive.read_bytes()),'independent_review':{'path':'independent-review.txt','sha256':h(review)},'members':{n:{'bytes':len(b),'sha256':h(b)} for n,b in sorted(files.items())}}
(out/'BUNDLE.json').write_text(json.dumps(m,indent=2)+'\n');print(len(files),'members',archive.stat().st_size,'bytes',m['archive_sha256'])
