from pathlib import Path
import hashlib,json,zipfile,subprocess
root=Path('Computability/DiophantineConsistency/reviews/lean-proof-simplification-20261028-nonzero-sphere-sharing-evidence'); m=json.loads((root/'BUNDLE.json').read_text()); h=lambda b:hashlib.sha256(b).hexdigest(); archive=root/m['archive']; assert h(archive.read_bytes())==m['archive_sha256']
with zipfile.ZipFile(archive) as z:
 assert z.testzip() is None
 names=z.namelist(); assert len(names)==len(set(names)) and set(names)==set(m['members'])
 for n, v in m['members'].items():
  d=z.read(n); assert len(d)==v['bytes'] and h(d)==v['sha256'], n
 print('archive CRC and',len(names),'manifest members verified')
 read=lambda n:z.read(n); data=lambda n:json.loads(read('prototype/'+n)); prefix='Computability/DiophantineConsistency/Lean/DiophantineConsistency/'
 assert subprocess.check_output(['git','rev-parse',m['source_commit']+'^']).decode().strip()==m['source_parent']
 for phase,rev in [('baseline',m['source_parent']),('final',m['source_commit'])]:
  for n in ('CarrierNonzeroSpheres','CarrierNonzeroSpheresChecks'):
   ref=subprocess.check_output(['git','show',f'{rev}:{prefix}{n}.lean']); assert read(f'snapshots/{phase}/DiophantineConsistency/{n}.lean')==ref
  assert read(f'commit/{phase}.lean')==read(f'snapshots/{phase}/DiophantineConsistency/CarrierNonzeroSpheres.lean')
 print('commit and parent source snapshots match')
 review=(root/m['independent_review']['file']).read_bytes();assert h(review)==m['independent_review']['sha256'] and review==read('independent/nonzero-sphere-independent-review.txt'); print('standalone and bundled review match')
 providers=data('provider-records.json'); assert len(providers)==2
 for x in providers:
  n=x['module'];assert x['status']==0 and x['before']==x['after'] and x['log_sha256']==h(read(f'prototype/provider-{n}.log')) and x['time'].encode()==read(f'prototype/provider-{n}.time')
  for d in x['direct_inputs']: assert d['before']==d['after']
  source=subprocess.check_output(['git','show',f"{m['source_commit']}:{x['source']}"]);assert h(source)==x['before']
 fresh={x['module']:x for x in providers}; rows={}
 for phase,file in [('baseline','pre-docfix-records.json'),('final','final-docfix-records.json')]:
  xs=[x for x in data(file) if x['phase']==phase];assert len(xs)==2
  for x in xs:
   n=x['module'];assert x['status']==0 and x['before']==x['after']==h(read(f'snapshots/{phase}/DiophantineConsistency/{n}.lean')) and x['log_sha256']==h(read(f'prototype/{phase}-{n}.log')) and x['time'].encode()==read(f'prototype/{phase}-{n}.time')
   for d in x['direct_inputs']:
    assert d['before']==d['after']; dep=d['module'].split('.')[-1];y=fresh.get(dep) or rows[(phase,dep)];assert d['before']==y['object_sha256'] and d['resolved']==y['object']
   rows[phase,n]=x
 assert rows['baseline','CarrierNonzeroSpheresChecks']['object_sha256']==rows['final','CarrierNonzeroSpheresChecks']['object_sha256']
 print('two provider and four target/client receipts, direct object pins and matching client objects')
 adopted=next(x for x in data('records2.json') if x['phase']=='final' and x['module']=='CurrentPositiveZero2011'); d=next(d for d in fresh['CarrierScaledAuxiliary118']['direct_inputs'] if d['module'].endswith('.CurrentPositiveZero2011'));assert adopted['status']==0 and adopted['before']==adopted['after']==h(subprocess.check_output(['git','show',f"{m['source_commit']}:{prefix}CurrentPositiveZero2011.lean"])) and d['before']==adopted['object_sha256'];print('prior current-positive provider receipt matches direct input')
 for x in data('repeat-records.json'):
  ph=x['phase'];n=x['module'];assert x['status']==0 and x['before']==x['after']==rows[ph,n]['before'] and x['object_sha256']==rows[ph,n]['object_sha256'];assert x['log_sha256']==h(read(f'prototype/repeat1-{ph}-{n}.log')) and x['time'].encode()==read(f'prototype/repeat1-{ph}-{n}.time')
 print('paired repeat records checked')
 for x in data('coherent-probe-records.json'):
  ph=x['phase'];n=x['probe'];assert x['status']==0 and x['source_before']==x['source_after']==h(read('prototype/'+Path(x['source']).name)) and x['log_sha256']==h(read(f'prototype/probe-{ph}-{n}.log')) and x['objects_before']==x['objects_after']==[rows[ph,'CarrierNonzeroSpheres']['object_sha256']]
 for n in ('names','coherent-interfaces','simp','instances','private'):assert read(f'prototype/probe-baseline-{n}.log')==read(f'prototype/probe-final-{n}.log')
 assert read('prototype/probe-baseline-names.log').count(b'DECL ')==46
 for n,count in [('simp',55579),('instances',23485)]:assert len(read(f'prototype/probe-baseline-{n}.log').splitlines())==count
 print('ten probe receipts and paired declarations/simp/instances verified')
 pre=next(x for x in data('pre-docfix-records.json') if x['phase']=='final' and x['module']=='CarrierNonzeroSpheres');recon=read('prototype/pre-docfix-reconstructed.lean');assert pre['before']==pre['after']==h(recon) and pre['object_sha256']!=rows['final','CarrierNonzeroSpheres']['object_sha256'];doc=b'/-- External exact-current-port equivalences, not internal HA/ZFC derivations. -/\n';assert read('commit/final.lean').replace(doc,b'')==recon
 print('reconstructed pre-docfix source matches receipt; overwritten object not available in archive')
 man=data('prior-reused-provider-manifest.json');q=next(x for x in man['reused_objects'] if x['source'].endswith('/SignedPellResidue.lean'));assert q['sha256']=='45937af80eafe9cb6fd29e046d3f7f87b35d309da8f84bfdd9c99ae1347ab93a'; old=man['protected'][q['source']];assert old=='46afed5402b7bf1a63d567e32906e28f4c06a26b1aab6c8788ef46a405a69fb4';current=h(subprocess.check_output(['git','show',f"{m['source_commit']}:{q['source']} ".strip()]));assert current=='ecd4dfbb29cc66499f65941f497640d48788284e8b52324d2ef8dba4fae772be' and old!=current
 print('older SignedPell cached inventory boundary confirmed; no full closure claim')
 print('object binaries are not archived; original audit corroborates live artifacts when available')
