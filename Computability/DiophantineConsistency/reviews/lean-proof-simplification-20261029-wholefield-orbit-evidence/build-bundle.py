from pathlib import Path
import hashlib,json,subprocess,zipfile
out=Path('/tmp/wholefield-orbit-evidence');src=Path('/dev/shm/wholefield-orbit-refresh');commit=subprocess.check_output(['git','rev-parse','28dcbeff43'],text=True).strip();parent=subprocess.check_output(['git','rev-parse',commit+'^'],text=True).strip();review=Path('/tmp/wholefield-orbit-refresh-peer-review.txt');sha=lambda x:hashlib.sha256(x).hexdigest();items={'independent/review.txt':review.read_bytes(),'independent/audit.py':Path('/tmp/wholefield-orbit-refresh-peer-audit.py').read_bytes(),'independent/audit.log':Path('/tmp/wholefield-orbit-refresh-peer-audit.log').read_bytes(),'bundle/build-bundle.py':(out/'build-bundle.py').read_bytes()};(out/'independent-review.txt').write_bytes(review.read_bytes())
rel='Computability/DiophantineConsistency/Lean/DiophantineConsistency/ArithmeticWholeField.lean'
for ph,rev in [('baseline',parent),('final',commit)]:
 data=subprocess.check_output(['git','show',rev+':'+rel]);assert data==(src/ph/'DiophantineConsistency/ArithmeticWholeField.lean').read_bytes();items['commit/'+ph+'/ArithmeticWholeField.lean']=data
for p in src.rglob('*'):
 if not p.is_file() or p.is_symlink() or p.suffix in ('.olean','.ilean','.o','.c'):continue
 rel=p.relative_to(src)
 if rel.parts[0] in ('provider','committed-baseline','committed-final'):continue
 items['prototype/'+str(rel)]=p.read_bytes()
for path in ['/dev/shm/cell-sum-unique/final-records.json','/dev/shm/wang-push-direct/final-target-records.json']:
 p=Path(path);items['prior/'+str(p).lstrip('/')]=p.read_bytes()
w=Path('Computability/DiophantineConsistency/Lean/DiophantineConsistency');dec=json.loads((src/'provider-record.json').read_text());rows=json.loads((src/'final-records.json').read_text());sources={}
for x in [dec,*rows]:
 for d in x['direct_inputs']:
  p=Path(d['source']); assert sha(p.read_bytes())==d['source_before']==d['source_after']; sources[p.name]=p.read_bytes()
for name in ['ArithmeticCellLabels','ArithmeticCellTransfer','ArithmeticCellLocal','MFDoubledClause2011','ArithmeticWangTable','ArithmeticMachineRun215']:
 p=w/(name+'.lean');sources[p.name]=p.read_bytes()
for n,data in sorted(sources.items()):items['provider-sources/'+n]=data
archive=out/'inputs-and-logs.zip'
with zipfile.ZipFile(archive,'w',compression=zipfile.ZIP_DEFLATED,compresslevel=9) as z:
 for name,data in sorted(items.items()):z.writestr(name,data)
manifest={'schema':'lean-proof-simplification-evidence-v1','source_commit':commit,'source_parent':parent,'scope':'Share orbit-cell membership and derive the orbit return by divisibility','validation':'Paired ArithmeticWholeField and direct ArithmeticOccupation builds pass using rebuilt current-source ArithmeticCellDecoding, current-source ArithmeticCellLabels and ArithmeticCellTransfer, and current-source ArithmeticWangPlane. Target reports show 74 common declarations with unchanged types and axioms and one new private theorem; 71 client declaration reports and sampled registrations match, although client objects differ. Client probes pin eight affected and provider objects.','limitations':['The compiled objects and overlays are excluded. Cached transitive dependencies were not fully rebuilt. Current-source receipts and matching direct producer input objects are recorded for Decoding, CellLabels, CellTransfer and WangPlane; source snapshots of other provider files are path samples, not all authenticated producer/source associations.','Target and client census reports compare printed names, types, axioms and sampled registrations; they do not assert proof-body equality. Paired timings are single samples under shared load.'],'archive':'inputs-and-logs.zip','archive_sha256':sha(archive.read_bytes()),'members':{n:{'sha256':sha(v),'bytes':len(v)} for n,v in sorted(items.items())},'independent_review':{'file':'independent-review.txt','sha256':sha(review.read_bytes())}}
(out/'BUNDLE.json').write_text(json.dumps(manifest,indent=2)+'\n')
with zipfile.ZipFile(archive) as z:
 assert z.testzip() is None and set(z.namelist())==set(items)
 for n,m in manifest['members'].items():
  b=z.read(n);assert len(b)==m['bytes'] and sha(b)==m['sha256'] and not n.endswith(('.olean','.ilean','.o'))
assert sha((out/'independent-review.txt').read_bytes())==manifest['independent_review']['sha256'];print('PASS',len(items),'members',archive.stat().st_size,'bytes, archive',manifest['archive_sha256']);print('manifest',sha((out/'BUNDLE.json').read_bytes()))
