"""Read-only audit: compat overlay preserves every canonical project object."""
from pathlib import Path
import hashlib,json,os,shutil,tempfile
B=Path('/tmp/adaptive13-assembly-recomposed-q9s50zdl'); C=Path(os.environ.get('WANG_COMPAT_TABLE','/tmp/adaptive-wang-table-compat-bu_4_5dx')); Q=Path('/tmp/adaptive-wang-chunk-full-src/DiophantineConsistency')
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest();read=lambda p:json.loads(Path(p).read_text());bs=read(B/'state.json');cs=read(C/'state.json');g=read(B/'guards.json');pr=read(B/'providers.json');chunk=Path(cs['chunk_provider']);ck=read(chunk/'state.json');assert bs['status']==cs['status']==ck['status']=='PASS'
assert sha(B/'guards.json')==bs['guards_sha256']==cs['guards_sha256'] and sha(B/'providers.json')==bs['providers_sha256']==cs['providers_sha256'];assert sha(chunk/'state.json')==cs['chunk_state_sha256']
bh=sha(B/'state.json');ch=sha(C/'state.json');expected={Path('DiophantineConsistency')/(r['name']+'.olean'):r['object_sha256'] for r in ck['records']};expected[Path('DiophantineConsistency/ArithmeticWangTable.olean')]=cs['object_sha256']
def auth():
 return (sha(B/'state.json')==bh and sha(C/'state.json')==ch and sha(chunk/'state.json')==cs['chunk_state_sha256'] and sha(B/'guards.json')==bs['guards_sha256'] and sha(B/'providers.json')==bs['providers_sha256'] and all(sha(p)==v for p,v in g.items()) and all(sha(x['path'])==x['sha256'] for x in pr.values()) and all(sha(Q/(r['name']+'.lean'))==r['source_sha256'] and sha(chunk/'lib/DiophantineConsistency'/(r['name']+'.olean'))==r['object_sha256'] and sha(chunk/'logs'/(r['name']+'.log'))==r['log_sha256'] for r in ck['records']))
assert auth();w=Path(tempfile.mkdtemp(prefix='adaptive-wang-compat-overlay-audit-'));shutil.copyfile(__file__,w/'driver.py');state={'status':'RUNNING','private':str(w),'base_state_sha256':bh,'compat_state_sha256':ch,'guards_sha256':bs['guards_sha256'],'providers_sha256':bs['providers_sha256'],'scope':'Read-only object overlap audit for the compatibility overlay; no canonical integration or historical object provenance claim.'}
def save():(w/'state.json').write_text(json.dumps(state,indent=2)+'\n')
save();print('PRIVATE',w,flush=True)
try:
 base={f.relative_to(B/'lib') for f in (B/'lib').rglob('*.olean') if f.is_file()};comp={f.relative_to(C/'lib') for f in (C/'lib').rglob('*.olean') if f.is_file()};missing=sorted(map(str,base-comp));extra=comp-base;diff=[];records={}
 for rel in sorted(base):
  a=sha(B/'lib'/rel);b=sha(C/'lib'/rel) if rel in comp else None;records[str(rel)]={'canonical':a,'compat':b}
  if a!=b:diff.append(str(rel))
 extras={str(rel):sha(C/'lib'/rel) for rel in sorted(extra)};result={'canonical_count':len(base),'compat_count':len(comp),'missing':missing,'changed':diff,'extras':extras,'expected_extras':{str(k):v for k,v in expected.items()},'canonical_overlap':records};(w/'result.json').write_text(json.dumps(result,indent=2)+'\n');state['result_sha256']=sha(w/'result.json');state.update(canonical_count=len(base),compat_count=len(comp),missing_count=len(missing),changed_count=len(diff),extra_count=len(extra));assert not missing and not diff and extras=={str(k):v for k,v in expected.items()} and auth();state['status']='PASS';save();print('PASS',w,'base',len(base),'extras',len(extra),flush=True)
except BaseException as e:state.update(status='FAILED',failure=str(e));save();raise
