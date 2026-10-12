import sys,json,pathlib,collections,time
sys.path.insert(0,'/workspace/scratch/9f3a01c0ff48/experiments_native')
from search_surfaces import inspect_hit,ROOT,normal_cut_handlebodies
path=ROOT.parent/'reports/57/results/discovery_corpus.json'
records=json.loads(path.read_text())['records']
records=[r for r in records if not r['id'].startswith(('fibonacci','solid_torus_sum'))]
records.sort(key=lambda r: (not r['id'].startswith(('finite_trefoil','pachner23')),r['tetrahedra']))
stats=collections.Counter();saved=[];started=time.monotonic()
for source in records:
 print('SOURCE',source['id'],len(source['standard_vertices']),flush=True)
 for i,surface in enumerate(source['standard_vertices']):
  raw=source['triangulation'];coords=surface['coordinates']
  c=dict(id=source['id']+f'/vertex{i}',triangulation=raw,coordinates=coords)
  stats['cases']+=1
  result=normal_cut_handlebodies(raw,coords,boundary_method='moments')
  stats[result['status']]+=1
  if result['status']=='COMPLETE':continue
  stats[result['reason']]+=1
  if result['reason'] not in ('annular_core_attachment','boundary_kernel_cancellation_stalled'):continue
  d,hits=inspect_hit(c,result)
  good=[m for m in d['modes'] if m['core']=='COMPLETE' and m.get('annuli')]
  if good:
   print('ANNULUS',c['id'],result['reason'],json.dumps(good),flush=True)
   saved.append(dict(case=c,reason=result['reason'],audit=d,hits=hits))
   pathlib.Path('/workspace/scratch/9f3a01c0ff48/experiments_native/discovery_annuli.json').write_text(json.dumps(saved,indent=2)+'\n')
   if hits:
    print('HIT',json.dumps(hits),flush=True)
    if len([x for x in saved if x['hits']])>=6:break
 else:
  print('PROGRESS',dict(stats),'seconds',time.monotonic()-started,flush=True)
  continue
 break
print('DONE',dict(stats),'seconds',time.monotonic()-started,flush=True)
