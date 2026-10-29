from pathlib import Path
import json,hashlib,zipfile,subprocess,re
p=Path('Computability/DiophantineConsistency/reviews/lean-proof-simplification-20261028-wang-input-cases-evidence');b=json.loads((p/'BUNDLE.json').read_text());arc=p/b['archive'];H=lambda v:hashlib.sha256(v).hexdigest();assert H(arc.read_bytes())==b['archive_sha256']
with zipfile.ZipFile(arc) as z:
 assert z.testzip() is None; names=z.namelist();assert len(names)==len(set(names)) and set(names)==set(b['members'])
 for n in names:
  x=b['members'][n];data=z.read(n);assert len(data)==x['bytes'] and H(data)==x['sha256'];assert not n.endswith(('.olean','.ilean','.o','.c'))
 print('archive CRC/hash and',len(names),'manifest sizes/hashes pass; no compiled objects')
 review=(p/b['independent_review']['file']).read_bytes();assert H(review)==b['independent_review']['sha256']==H(z.read('independent/wang-input-independent-review.txt'));print('review matches standalone')
 commit=b['source_commit'];parent=b['source_parent'];assert subprocess.check_output(['git','rev-parse',commit+'^'],text=True).strip()==parent;prefix='Computability/DiophantineConsistency/Lean/DiophantineConsistency/'
 for ph,ref in [('baseline',parent),('final',commit)]:
  for n in ('WangTiles942InputLanguage','WangTiles942Signals','WangTiles942InputLanguageChecks'):
   d=subprocess.check_output(['git','show',ref+':'+prefix+n+'.lean']);assert d==z.read(f'snapshots/{ph}/DiophantineConsistency/{n}.lean')
   if n=='WangTiles942InputLanguage':assert d==z.read(f'commit/{ph}.lean')==z.read(f'prototype/{ph}-commit.lean');print('git',ph,n,H(d))
 print('all source snapshots match commit/parent')
 rd=lambda n:json.loads(z.read(n));prior=next(x for x in rd('provider/fresh-client-records.json') if x['job']=='WangTiles942Boundary' and x['phase']=='final');assert prior['status']==0 and prior['source_sha256']==prior['source_after']==H(subprocess.check_output(['git','show',commit+':'+prefix+'WangTiles942Boundary.lean']));print('Boundary prior receipt source/object',prior['source_sha256'],prior['object_sha256'])
 rows={};num=0
 for ph in ('baseline','final','baseline-repeat','final-repeat'):
  original='baseline' if ph.startswith('baseline') else 'final'
  for x in rd(f'prototype/{ph}-records.json'):
   n=x['module'];assert x['status']==0 and x['before']==x['after']==H(z.read(f'snapshots/{original}/DiophantineConsistency/{n}.lean')) and x['log_sha256']==H(z.read('prototype/'+Path(x['log']).name)) and x['time'].encode()==z.read(f'prototype/{ph}-{n}.time') and x['object_sha256']
   for d in x['direct_inputs']:
    m=d['module'].split('.')[-1];assert d['before']==d['after']
    if m=='WangTiles942Boundary':assert d['before']==prior['object_sha256']
    else:assert d['resolved']==rows[(ph,m)]['object'] and d['before']==rows[(ph,m)]['object_sha256']
    num+=1
   if n=='WangTiles942InputLanguage':assert z.read('prototype/'+Path(x['log']).name)==b''
   rows[(ph,n)]=x
 for ph in ('baseline','final'):
  for n in ('names','interfaces','simp','instances'):
   x=rd(f'prototype/probe-{n}-{ph}.json');assert x['status']==0 and x['source_before']==x['source_after']==H(z.read('prototype/'+Path(x['source']).name)) and x['object_before']==x['object_after']==rows[(ph,'WangTiles942InputLanguage')]['object_sha256'] and x['log_sha256']==H(z.read('prototype/'+Path(x['log']).name))
 print(len(rows),'builds',num,'direct-input occurrences and 8 probe receipts checked; target logs empty')
 for n in ('WangTiles942Signals','WangTiles942InputLanguageChecks'):assert rows['baseline',n]['object_sha256']==rows['final',n]['object_sha256'];print('client hashes identical',n)
 for n in ('names','interfaces','simp','instances'):
  a=z.read(f'prototype/baseline-{n}.log');d=z.read(f'prototype/final-{n}.log');assert a==d;print(n,'identical log lines',len(a.splitlines()))
 def parse(n):return {m.group(1):m.group(0) for m in re.finditer(r'^DECL (\S+) TYPE .*?(?=^DECL |\Z)',z.read(n).decode(),re.M|re.S)}
 a=parse('prototype/baseline-interfaces.log');d=parse('prototype/final-interfaces.log');assert a==d and len(a)==37;v=parse('snapshots/superseded-v1/final-interfaces.log');assert a.keys()==v.keys() and sum(a[k]!=v[k] for k in a)==9;print('37 target declaration blocks match, superseded v1 changes 9')
 assert z.read('snapshots/superseded-v1/final-WangTiles942InputLanguage.log').count(b' warning:')==3 and b' warning:' not in z.read('snapshots/superseded-v2/final-WangTiles942InputLanguage.log');assert not any('superseded-v2/final-interfaces' in n for n in names);print('v1 warnings 3, v2 warnings 0; v2 interface census absent')
 f=rd('prototype/setup-failed-records.json')[0];assert f['status']!=0 and f['before']==f['after']==H(z.read('snapshots/superseded-v1/source.lean')) and f['log_sha256']==H(z.read('prototype/setup-failed.log')) and f['time'].encode()==z.read('prototype/setup-failed.time');print('pre-elaboration setup failure preserved')
 print('Archive excludes object bytes; first-provider resolution is recorded, not independently recreated here. Earlier Boundary provider did not pin all transitive input sources, and wider project/package closure is cached. Superseded v2 interface effect unverified.')
