from pathlib import Path
import hashlib,json,zipfile,subprocess,re
D=Path('Computability/DiophantineConsistency/reviews/lean-proof-simplification-20261028-rank-mask-residue-evidence'); m=json.loads((D/'BUNDLE.json').read_text());p=D/m['archive']; h=lambda x:hashlib.sha256(x).hexdigest(); assert h(p.read_bytes())==m['archive_sha256']; print('archive',h(p.read_bytes()))
with zipfile.ZipFile(p) as z:
 assert z.testzip() is None; names=z.namelist();assert len(names)==len(set(names)) and set(names)==set(m['members']);print('CRC and complete member set',len(names))
 for n,v in m['members'].items():
  x=z.read(n);assert len(x)==v['bytes'] and h(x)==v['sha256'],n
 print('all member sizes/hashes pass')
 def b(n):return z.read(n)
 def j(n):return json.loads(b(n))
 review=b('independent/rank-mask-independent-review.txt'); assert h(review)==m['independent_review']['sha256']==h((D/m['independent_review']['file']).read_bytes()); print('review hash matches')
 rel='Computability/DiophantineConsistency/Lean/DiophantineConsistency/ArithmeticRankForcing2011.lean'
 for phase,rev in [('baseline',m['source_parent']),('final',m['source_commit'])]:
  x=subprocess.check_output(['git','show',rev+':'+rel]);assert x==b('commit/'+phase+'.lean')==b('snapshots/sources/paired-'+phase+'/DiophantineConsistency/ArithmeticRankForcing2011.lean');print('git source snapshot matches',phase,rev)
 W='Computability/DiophantineConsistency/Lean/DiophantineConsistency/ArithmeticConstructionAssembly.lean';c=subprocess.check_output(['git','show',m['source_commit']+':'+W]);assert c==b('snapshots/sources/paired-baseline/DiophantineConsistency/ArithmeticConstructionAssembly.lean')==b('snapshots/sources/paired-final/DiophantineConsistency/ArithmeticConstructionAssembly.lean');print('client snapshots match commit')
 maskrows=j('provider/mask-ins-simplify/records.json');mask=next(x for x in maskrows if x['name']=='ArithmeticMaskConstants' and x['phase']=='final' and x['status']==0);pmap=j('provider/mask-ins-simplify/independent-direct-provider-audit.json');vm=j('provider/variation-tail-sharing/post-commit-provider-matches.json');vr=next(x for x in j('provider/variation-tail-sharing/refreshed2-final-records.json') if x['module']=='ArithmeticConstructionVariation');rows={}
 for phase in ['paired-baseline','paired-final']:
  for x in j('prototype/'+phase+'-records.json'):
   n=x['module'];assert x['status']==0 and x['source_before']==x['source_after']==h(b('snapshots/sources/'+phase+'/DiophantineConsistency/'+n+'.lean'));assert x['log_sha256']==h(b('prototype/'+phase+'-'+n+'.log')) and x['time_sha256']==h(b('prototype/'+phase+'-'+n+'.time'))
   for d in x['direct_inputs']:
    assert d['object_before']==d['object_after'] and d['source_before']==d['source_after'];k=d['module'].split('.')[-1]
    if n=='ArithmeticRankForcing2011':
     if k=='ArithmeticMaskConstants':assert (d['source_before'],d['object_before'])==(mask['before'],mask['object_sha256'])
     else:q=pmap[d['module']];assert (d['source_before'],d['object_before'])==(q['source_sha256'],q['object_sha256']) and q['matching_prior_rows']
    elif k=='ArithmeticRankForcing2011':assert d['resolved']==rows[(phase,k)]['object'] and d['object_before']==rows[(phase,k)]['object_sha256'];assert d['source_before']==h(b('commit/baseline.lean'))
    elif k=='ArithmeticConstructionVariation':assert (d['source_before'],d['object_before'])==(vr['source_before'],vr['object_sha256'])
    else:assert any(v['module']==k and v['source']==d['source_before'] and v['object']==d['object_before'] and v['matches'] for v in vm),(phase,k)
   rows[phase,n]=x;print('build and provider receipts',phase,n,x['timing'])
  for x in j('prototype/'+phase+'-probes.json'):
   k=x['name'];assert x['status']==0 and x['source_before']==x['source_after']==h(b('prototype/'+k+'.lean')) and x['object_before']==x['object_after']==rows[phase,'ArithmeticRankForcing2011']['object_sha256'];assert x['log_sha256']==h(b('prototype/'+phase+'-'+k+'.log')) and x['time_sha256']==h(b('prototype/'+phase+'-'+k+'.time'))
  x=j('prototype/repeat-'+phase+'-records.json')[0];y=rows[phase,'ArithmeticRankForcing2011'];assert x['status']==0 and x['source_before']==x['source_after']==y['source_before'] and x['object_sha256']==y['object_sha256'];assert x['log_sha256']==h(b('prototype/repeat-'+phase+'-ArithmeticRankForcing2011.log')) and x['time_sha256']==h(b('prototype/repeat-'+phase+'-ArithmeticRankForcing2011.time'));assert [(d['module'],d['resolved'],d['object_before']) for d in x['direct_inputs']]==[(d['module'],d['resolved'],d['object_before']) for d in y['direct_inputs']];print('repeat',phase,x['timing'])
 assert rows['paired-baseline','ArithmeticConstructionAssembly']['object_sha256']==rows['paired-final','ArithmeticConstructionAssembly']['object_sha256'];print('recorded client object hashes equal')
 for k,count in [('interfaces',5),('simp',35447),('instances',15616)]:
  a=b('prototype/paired-baseline-'+k+'.log'); assert a==b('prototype/paired-final-'+k+'.log');n=(len(re.findall(rb'^DECL ',a,re.M)) if k=='interfaces' else len(a.splitlines())); assert n==count,(k,n);print('identical probe output',k,n)
 x=j('prototype/closure-probe-record.json');assert x['status']==0 and x['source_before']==x['source_after']==h(b('prototype/closure-probe.lean')) and x['log_sha256']==h(b('prototype/closure-probe.log'));assert [v['before'] for v in x['objects']]==[rows['paired-final','ArithmeticConstructionAssembly']['object_sha256'],rows['paired-final','ArithmeticRankForcing2011']['object_sha256']] and all(v['before']==v['after'] for v in x['objects']);print('pinned closure log:',b('prototype/closure-probe.log').decode().strip().replace('\n','; '))
 graph=j('prototype/full-graph.json');imp=graph['imports'];seen=set();todo=['DiophantineConsistency.ArithmeticConstructionAssembly']
 while todo:
  n=todo.pop()
  if n in seen:continue
  seen.add(n);todo.extend(imp.get(n,[]))
 assert 'DiophantineConsistency.ArithmeticModularCancellation' in seen and 'DiophantineConsistency.SplitKernelData59' not in seen and 'DiophantineConsistency.GapKernelData66' not in seen;assert len(imp)==126 and len(graph['missing_modules'])==45 and not graph['ambiguous_modules'];print('recorded local source graph',len(imp),'nodes',len(graph['missing_modules']),'unresolved names; helper reachable, generated kernels not reached')
 for name,meta in graph['source_hashes'].items():
  data=subprocess.check_output(['git','show',m['source_parent']+':'+meta['source']]);assert h(data)==meta['sha256'];assert re.findall(r'^import\s+([^\s]+)',data.decode(),re.M)==imp[name]
 assert re.findall(rb'^import\s+([^\s]+)',b('commit/final.lean'),re.M)==re.findall(rb'^import\s+([^\s]+)',b('commit/baseline.lean'),re.M)
 print('all 126 recorded source hashes and direct import lists match pinned parent; changed target imports unchanged')
 boundaries=j('prototype/cached-boundaries.json');assert len(boundaries)==5;print('recorded cached boundary modules:',', '.join(x['module'] for x in boundaries))
 for phase in ['paired-baseline','paired-final']:
  for mod in ['ArithmeticRankForcing2011','ArithmeticConstructionAssembly']:
   v=rows[phase,mod];obj=Path(v['object']);print('external object',phase,mod,'MATCH' if obj.is_file() and h(obj.read_bytes())==v['object_sha256'] else 'MISSING OR CHANGED')
 for v in boundaries:
  obj=Path(v['object_path']);src=Path(v['current_source']);print('external cached boundary',v['module'],'object',('MATCH' if obj.is_file() and h(obj.read_bytes())==v['object_sha256'] else 'MISSING OR CHANGED'),'sampled source',('MATCH' if src.is_file() and h(src.read_bytes())==v['current_source_sha256'] else 'MISSING OR CHANGED'))
 assert not any(n.endswith('.olean') for n in names);print('archive contains no compiled objects; portable object hashes are receipt claims')
print('PASS')
