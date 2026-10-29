from pathlib import Path
import hashlib,json,subprocess,zipfile
r=Path('/dev/shm/cell-selector-unit');out=Path('/tmp/cell-selector-unit-evidence');w=Path('Computability/DiophantineConsistency/Lean/DiophantineConsistency');h=lambda b:hashlib.sha256(b).hexdigest();files={}
def add(n,b):
 assert n not in files,n
 files[n]=b
for p in r.rglob('*'):
 if p.is_file() and p.suffix in ('.lean','.json','.log','.py','.time','.txt') and not any(x.startswith(('obj-','objects-')) for x in p.relative_to(r).parts):add('prototype/'+str(p.relative_to(r)),p.read_bytes())
for phase,rev in [('baseline','cf31781e72^'),('final','cf31781e72')]:
 n='ArithmeticCellLocal.lean';b=subprocess.check_output(['git','show',rev+':'+str(w/n)]);assert b==(r/phase/'DiophantineConsistency'/n).read_bytes();add('commit/'+phase+'/'+n,b)
for n in ['ArithmeticCellPhysical','NativePreliminaryCount2011','CurrentHighDigitFacts2011','MFDoubledClause2011','ArithmeticCellLabels']:add('sources/'+n+'.lean',(w/(n+'.lean')).read_bytes())
for name,p in [('construction-share-bound-refresh-records.json','/tmp/construction-share/bound-refresh-records.json'),('high-digits-module-sharing-final-records.json','/tmp/high-digits-module-sharing/final-records.json')]:add('providers/'+name,Path(p).read_bytes())
for name in ['review.txt','audit.py','audit.log']:add('independent/'+name,Path('/tmp/cell-selector-unit-peer-'+name).read_bytes())
archive=out/'inputs-and-logs.zip'
with zipfile.ZipFile(archive,'w',compression=zipfile.ZIP_DEFLATED,compresslevel=9) as z:
 for n,b in sorted(files.items()):z.writestr(n,b)
review=Path('/tmp/cell-selector-unit-peer-review.txt').read_bytes();(out/'independent-review.txt').write_bytes(review)
m={'schema':'lean-proof-simplification-evidence-v1','source_commit':subprocess.check_output(['git','rev-parse','cf31781e72'],text=True).strip(),'source_parent':subprocess.check_output(['git','rev-parse','cf31781e72^'],text=True).strip(),'scope':'Share private selector unit in ArithmeticCellLocal','validation':'Paired target and sole tracked direct client ArithmeticCellLabels builds pass with identical client objects. Object-pinned probes report 177 common target declarations, with two private reports changed, 10 private selector declarations removed and 7 added; 76 client declaration reports and sampled simp and instance registrations match. Four unchanged direct target/client provider source/object pairs have matching successful producer records.','limitations':['The target, direct client, and prior producer receipts do not establish a source-current transitive closure. Wider downstream clients were not rebuilt.','The old private helper names occur only in the target source in a tracked Lean/Python search. Declaration reports and sampled registrations do not prove equality of proof bodies or all persistent extensions.','Compiled objects are omitted. Recorded build and probe paths refer to original temporary directories; full replay requires the external environment and object dependencies.','Target builds each emit the same three existing warnings after phase path and line-number normalization; client logs are empty.'],'archive':archive.name,'archive_sha256':h(archive.read_bytes()),'independent_review':{'path':'independent-review.txt','sha256':h(review)},'members':{n:{'bytes':len(b),'sha256':h(b)} for n,b in sorted(files.items())}}
(out/'BUNDLE.json').write_text(json.dumps(m,indent=2)+'\n');print(len(files),'members',archive.stat().st_size,'bytes',m['archive_sha256'])
