import sys,json,random,pathlib,collections,time
sys.path.insert(0,'/workspace/scratch/9f3a01c0ff48/experiments_native')
from search_surfaces import inspect_hit,ROOT,normal_cut_handlebodies
from tests.test_normal_surface_orbits import relabel
corpus=json.loads((ROOT/'marked_parallelity_research/corpus.json').read_text())['cases']
seed_cases=[c for c in corpus if c['id'].startswith('pilot/') and ('fibonacci' in c['id'] or '/lst_' in c['id'])]
seed_cases=[c for c in seed_cases if len(c['triangulation']['tetrahedra'])>=4]
stats=collections.Counter();saved=[];rng=random.Random(120102026)
start=time.monotonic()
for run in range(100):
 for source in seed_cases:
  raw,coords=relabel(source['triangulation'],source['coordinates'],rng)
  c=dict(id=source['id']+f'/relabel{run}',triangulation=raw,coordinates=coords)
  stats['cases']+=1
  result=normal_cut_handlebodies(raw,coords,boundary_method='moments')
  stats[result['status']]+=1
  if result['status']=='COMPLETE':continue
  stats[result['reason']]+=1
  d,hits=inspect_hit(c,result)
  good=[m for m in d['modes'] if m['core']=='COMPLETE' and m.get('annuli')]
  if good:
   print('ANNULUS',c['id'],result['reason'],json.dumps(good),flush=True)
   saved.append(dict(case=c,reason=result['reason'],audit=d,hits=hits))
   pathlib.Path('/workspace/scratch/9f3a01c0ff48/experiments_native/relabel_annuli.json').write_text(json.dumps(saved,indent=2)+'\n')
   if hits:
    print('HIT',json.dumps(hits),flush=True)
    if len([x for x in saved if x['hits']])>=6:break
 else:
  if run%5==0:print('PROGRESS',run,dict(stats),flush=True)
  continue
 break
print('DONE',dict(stats),'seconds',time.monotonic()-start,flush=True)
