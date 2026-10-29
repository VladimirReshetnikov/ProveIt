from pathlib import Path
import hashlib,json,subprocess,zipfile
out=Path('/tmp/beta-int-sharing-evidence');src=Path('/dev/shm/beta-int-sharing');commit=subprocess.check_output(['git','rev-parse','ca3ebb3033'],text=True).strip();parent=subprocess.check_output(['git','rev-parse',commit+'^'],text=True).strip();review=Path('/tmp/beta-int-sharing-peer-review.txt');sha=lambda x:hashlib.sha256(x).hexdigest();items={'independent/review.txt':review.read_bytes(),'independent/audit.py':Path('/tmp/beta-int-sharing-peer-audit.py').read_bytes(),'independent/audit.log':Path('/tmp/beta-int-sharing-peer-audit.log').read_bytes(),'bundle/build-bundle.py':(out/'build-bundle.py').read_bytes()};(out/'independent-review.txt').write_bytes(review.read_bytes())
for n,_ in json.loads((src/'scope.json').read_text())['files']:
 rel='Computability/DiophantineConsistency/Lean/DiophantineConsistency/'+n+'.lean'
 for ph,rev in [('baseline',parent),('final',commit)]:
  data=subprocess.check_output(['git','show',rev+':'+rel]);assert data==(src/ph/'DiophantineConsistency'/(n+'.lean')).read_bytes(),(n,ph);items['commit/'+ph+'/'+n+'.lean']=data
omitted=[]
for p in src.rglob('*'):
 if not p.is_file() or p.is_symlink() or p.suffix in ('.olean','.ilean','.o','.c'):continue
 rel=p.relative_to(src)
 if rel.parts[0] in ('objects-baseline','objects-final','replay-baseline','replay-final'):continue
 if p.name.endswith('.log.gz'):
  omitted.append({'path':str(p),'bytes':p.stat().st_size,'sha256':sha(p.read_bytes()),'reason':'large environment log omitted for compactness; full independent log comparison requires this external original'});continue
 items['prototype/'+str(rel)]=p.read_bytes()
receipts=set()
for d in json.loads((src/'producer-search.json').read_text()):
 for a in d['matching_producers']:
  if a['source_after']==a['source_before']: receipts.add(a['file']);break
 else:
  if d['matching_producers']:receipts.add(d['matching_producers'][0]['file'])
receipts.add('/tmp/current-packing-positive-sharing/refresh3-records.json')
receipts.add('/tmp/current-packing-positive-sharing/prior-reused-provider-manifest.json')
for path in sorted(receipts):
 p=Path(path)
 if p.exists():items['prior/'+str(p).lstrip('/')]=p.read_bytes()
items['bundle/omitted-logs.json']=(json.dumps(omitted,indent=2)+'\n').encode();archive=out/'inputs-and-logs.zip'
with zipfile.ZipFile(archive,'w',compression=zipfile.ZIP_DEFLATED,compresslevel=9) as z:
 for name,data in sorted(items.items()):z.writestr(name,data)
manifest={'schema':'lean-proof-simplification-evidence-v1','source_commit':commit,'source_parent':parent,'scope':'Share integer positivity of beta across production proofs','validation':'Sixteen changed modules, ten prerequisite modules, eleven focused direct checks and six practical production direct clients pass paired builds. A source-matched NativePositiveSourceConstruction replay passes 27 affected modules per phase. The strengthened 18-object target and 24-object client probes confirm 529 common target declarations and 86 client declarations have equal types and axioms, with one new target theorem, and identical global simp and instance registrations.','limitations':['NativeAdaptiveCurrent2011 and the umbrella remain untested; the former needs a separately missing twelve-module NativeAdaptive chain. All other transitive dependencies are cached; no full current-source transitive build is claimed.','The original lanes have 26 distinct external direct project source/object pairs. Fourteen have matching source/object producer rows, including two with only single source samples; twelve have no matching producer in the documented search. The fresh replay provides a source-matched NativePositiveSourceConstruction producer for the sole unmatched direct provider of a changed module, and separately pins its recorded Carrier66Source object; its transitive closure retains the older SignedPellResidue boundary.','All 14 large compressed environment logs, including superseded probe logs, are omitted; bundle/omitted-logs.json records external paths, hashes and sizes. Full independent log comparisons require these external originals. Source snapshots, comparison JSON, scripts and probe records are retained.','Initial final missing-provider and baseline load-order failures are retained and disclosed. Baseline historical failed rows originally pointed to log paths later reused; separately preserved initial-baseline logs correspond to the recorded failure hashes. Shared-load timing observations are single samples; compiled objects and overlays are excluded.','The production-directory scan covers 19 cast uses; seven further matches are historical research/review snapshots outside production and remain untouched.'],'archive':'inputs-and-logs.zip','archive_sha256':sha(archive.read_bytes()),'members':{n:{'sha256':sha(v),'bytes':len(v)} for n,v in sorted(items.items())},'independent_review':{'file':'independent-review.txt','sha256':sha(review.read_bytes())}}
(out/'BUNDLE.json').write_text(json.dumps(manifest,indent=2)+'\n')
with zipfile.ZipFile(archive) as z:
 assert z.testzip() is None and set(z.namelist())==set(items)
 for n,m in manifest['members'].items():
  b=z.read(n);assert len(b)==m['bytes'] and sha(b)==m['sha256'] and not n.endswith(('.olean','.ilean','.o'))
assert sha((out/'independent-review.txt').read_bytes())==manifest['independent_review']['sha256'];print('PASS',len(items),'members',archive.stat().st_size,'bytes, archive',manifest['archive_sha256']);print('manifest',sha((out/'BUNDLE.json').read_bytes()),'omitted environment logs',len(omitted))
