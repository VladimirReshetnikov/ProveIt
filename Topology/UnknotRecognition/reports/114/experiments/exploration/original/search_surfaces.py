import pathlib,sys,json,collections,time,itertools
sys.path.insert(0,'/workspace/scratch/9f3a01c0ff48/experiments_native')
from inspect_annuli import inspect,ROOT,cyclic,reduce,inv
from fastunknot.normal_cut_handlebodies import normal_cut_handlebodies
from normal_orbit_research.fixtures import regina_triangulation,export_surface,layered_torus
import regina

def whitehead(words,max_rank=6):
 words=[cyclic(w) for w in words];labels=sorted({abs(x) for w in words for x in w})
 if len(labels)>max_rank:return None
 moves=[]
 while True:
  if all(len(w)==1 for w in words) and len({abs(w[0]) for w in words})==len(words):return {'words':words,'moves':moves}
  current=sum(map(len,words));best=None
  signed=labels+[-x for x in labels]
  for a in signed:
   rest=[x for x in signed if abs(x)!=abs(a)]
   for mask in range(1<<len(rest)):
    subset={a}|{x for i,x in enumerate(rest) if mask>>i&1}
    images={}
    for x in signed:
     if abs(x)==abs(a):images[x]=[x]
     else:images[x]=([-a] if -x in subset else [])+[x]+([a] if x in subset else [])
    result=[cyclic([y for x in w for y in images[x]]) for w in words]
    size=sum(map(len,result))
    if size<current and (best is None or size<best[0]):best=(size,a,sorted(subset),result)
  if best is None:return None
  _,a,subset,words=best;moves.append([a,subset])

def inspect_hit(case,native):
 d=inspect(case)
 hits=[]
 for m in d['modes']:
  if m['core']!='COMPLETE' or not m.get('annuli'):continue
  by_component={}
  for c in m['components']:
   labels={h+1 for h in c['remaining_one_handles']}
   annuli=[a for a in m['annuli'] if a['final'] and abs(a['final'][0]) in labels]
   if annuli:by_component[c['id']]=annuli
  for component,annuli in by_component.items():
   p=whitehead([a['final'] for a in annuli])
   if p is not None:hits.append({'mode':m['mode'],'component':component,'annuli':annuli,'primitive':p})
 return d,hits

if __name__=='__main__':
 stats=collections.Counter();out=[];start=time.monotonic()
 for n in range(1,11):
  raw,_=layered_torus(n);t=regina_triangulation(raw)
  surfaces=regina.NormalSurfaces(t,regina.NormalCoords.Standard,regina.NormalList.Vertex)
  print('ENUM',n,len(surfaces),flush=True)
  for k,s in enumerate(surfaces):
   x=export_surface(s)
   for factor in (1,2):
    case={'id':f'fib{n:02d}/vertex{k:03d}/scale{factor}','triangulation':raw,'coordinates':[[factor*v for v in r] for r in x]}
    stats['cases']+=1
    r=normal_cut_handlebodies(raw,case['coordinates'],boundary_method='moments')
    stats[r['status']]+=1
    if r['status']=='COMPLETE':continue
    stats[r['reason']]+=1
    d,hits=inspect_hit(case,r)
    m=[m for m in d['modes'] if m['core']=='COMPLETE' and m.get('annuli')]
    if m:
     print('ANNULAR',case['id'],r['reason'],json.dumps(m),flush=True)
     out.append({'case':case,'reason':r['reason'],'audit':d,'hits':hits})
     pathlib.Path('/workspace/scratch/9f3a01c0ff48/experiments_native/new_annuli.json').write_text(json.dumps(out,indent=2)+'\n')
     if hits:
      print('HIT',json.dumps(hits),flush=True)
      if len([c for c in out if c['hits']])>=5:break
   else:continue
   break
  else:continue
  break
 print('DONE',dict(stats),'seconds',time.monotonic()-start,flush=True)
