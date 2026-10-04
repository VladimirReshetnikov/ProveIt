"""Local report-owner data-only verification. Never imports scientific source.
Verifies frozen manifests, original metadata and exact typesetting replay.
"""
from pathlib import Path
import hashlib,json,stat
R=Path('/workspace/shared/report69-low-arity-compilers-release-20261004')
B=Path('/workspace/shared/report69-build-exact-v5')
def sha(data):return hashlib.sha256(data).hexdigest()
def enc(x):return (json.dumps(x,sort_keys=True,indent=2)+'\n').encode()
def put(name,x):(R/'qa'/name).write_bytes(enc(x))
def require(ok,msg):
 if not ok:raise ValueError(msg)
old=json.loads((R/'qa/ORIGINAL_INPUT_METADATA.json').read_bytes()); now={}
for full,row in old.items():
 p=Path(full);s=p.lstat();item={'mode':stat.S_IMODE(s.st_mode),'mtime_ns':s.st_mtime_ns,'kind':'directory' if stat.S_ISDIR(s.st_mode) else 'file'}
 if item['kind']=='file':
  require(stat.S_ISREG(s.st_mode) and s.st_nlink==1,'nonregular original');b=p.read_bytes();item.update(bytes=len(b),sha256=sha(b))
 now[full]=item
require(now==old,'original metadata changed')
# Also establish exact descendants within every original root, not only existing-key equality.
roots=[Path(s) for s in old if not any(str(Path(s).parent)==k for k in old)]
for root in roots:
 expected={s for s in old if s==str(root) or root in Path(s).parents}
 actual={str(root),*(str(p) for p in root.rglob('*'))}
 require(actual==expected,'original entry set changed: '+str(root))
put('ORIGINAL_INPUTS_UNCHANGED.json',{'status':'PASS','entries':len(old),'roots':len(roots),'bytes_modes_nanosecond_mtimes_and_exact_inventory':True,'read_access_times_excluded':True})
manifest_checks=[]
for relative,filename,pin in [
 ('science/low-arity','MANIFEST.sha256','b243e39e0fd9698f9d610f0f6d2b17485a98df8e20a9412c1c38c65877a42c82'),
 ('audits/low-arity-independent','MANIFEST.sha256','6852625bc450563eeda5ad96956e3ac18da64b95ca446c654da14f3b978594b3'),
 ('science/exact-degree-comparison','MANIFEST.json','fed0313f8f623cce051ceba49cd39cc6f739f3a75053189218c6139a5f4a9715'),
 ('audits/exact-degree-comparison','MANIFEST.json',None)]:
 root=R/relative;raw=(root/filename).read_bytes()
 if pin:require(sha(raw)==pin,'manifest pin')
 if filename.endswith('sha256'):
  entries=[{'file':line.split('  ',1)[1],'sha256':line.split('  ',1)[0]} for line in raw.decode().splitlines() if line]
 else:entries=json.loads(raw)['files']
 require(len({e['file'] for e in entries})==len(entries),'duplicate source manifest member')
 for e in entries:
  p=root/e['file'];require(root in p.parents,'manifest traversal');b=p.read_bytes();require(sha(b)==e['sha256'],'source manifest content')
  if 'bytes' in e:require(len(b)==e['bytes'],'source manifest bytes')
  if 'mode' in e:require(stat.S_IMODE(p.stat().st_mode)==e['mode'],'source manifest mode')
 require({p.relative_to(root).as_posix() for p in root.rglob('*') if p.is_file()}=={filename,*(e['file'] for e in entries)},'manifest coverage')
 manifest_checks.append({'root':relative,'manifest_sha256':sha(raw),'payload_files':len(entries),'status':'PASS'})
put('SOURCE_MANIFEST_VERIFICATION.json',{'status':'PASS','checks':manifest_checks,'science_executed':False})
receipt=json.loads((B/'BUILD_RECEIPT.json').read_bytes())
require(receipt['status']=='PASS' and receipt['packaged_pdf_match'] and receipt['dependency_lock_verified'],'exact build receipt')
require((B/'Report69.pdf').read_bytes()==(R/'Report69.pdf').read_bytes(),'exact pdf')
base=R/'qa/locked-final-build'
first=json.loads((base/'PAGE_INVENTORY.json').read_bytes());second=json.loads((B/'PAGE_INVENTORY.json').read_bytes());require(first==second,'raster inventory')
for name in first:require((base/'pages'/name).read_bytes()==(B/'pages'/name).read_bytes(),'raster bytes')
put('EXACT_REPLAY_COMPARISON.json',{'status':'PASS','pdf_sha256':sha((R/'Report69.pdf').read_bytes()),'page_count':len(first),'every_page_byte_equal':True,'dependency_lock_sha256':sha((R/'tools/BUILD_DEPENDENCIES_LOCK.json').read_bytes()),'system_inputs':len(json.loads((R/'tools/BUILD_DEPENDENCIES_LOCK.json').read_bytes())['system_inputs']),'original_inputs_preserved':True})
put('EXACT_PACKAGED_BUILD_RECEIPT.json',receipt)
notes=[
'Title, abstract, input domain and main result are clean and legible.',
'Clipping proof, exact-horizon boundary and finite preprocessing are clean.',
'Tensor basis, five residuals and both-direction proof are clean.',
'Horizon-zero formula and fixed-program sharpness table are clean.',
'Clipped-grid/tail diagram and one-witness factor table are clean; labels no longer break awkwardly.',
'One-witness proof, degree, SOS distinction and closure introduction are clean.',
'Complete closure theorem and both directions are clean; theorem heading stays with statement.',
'Fixed-dimensional extension and tensor coefficient norms are clean.',
'Tensor support, storage and operation counts are clean.',
'One-witness norms, storage, gates and parity comparison are clean.',
'Native resource table and comparison are clean; no overlapping columns.',
'Full POWER expression/residual displays and domain recovery are clean.',
'Restored equations, constructive quotient argument and progression are clean.',
'Degree certificate, gap equations and composition ledger are clean; product block distinguished.',
'Composition proof, infinite fibers and context are clean.',
'Scope qualifications, source hashes and Pell attribution are clean.',
'Stored-evidence boundary, preservation, separate terminal gate and references are clean.']
put('OWNER_VISUAL_REVIEW.json',{'status':'PASS','reviewer':'Report69 writer','scope':'Individual visual inspection of every final v5 rendered PNG plus full source review; independent reviews are separate','pdf_sha256':receipt['pdf_sha256'],'manuscript_pins_sha256':receipt['manuscript_pins_sha256'],'pages':[{'page':i,'file':f'page-{i:02d}.png','sha256':first[f'page-{i:02d}.png']['sha256'],'status':'PASS','observations':note} for i,note in enumerate(notes,1)],'clipping_overlap_missing_glyph_or_table_defect':False})
print('PASS: source manifests,',len(old),'original entries, exact PDF,',len(first),'page rasters and owner visual record')
