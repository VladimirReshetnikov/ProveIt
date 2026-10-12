import sys,json,pathlib,collections,time
ROOT=pathlib.Path('/workspace/scratch/9f3a01c0ff48/ProveIt/Topology/UnknotRecognition/fast');sys.path.insert(0,str(ROOT))
from fastunknot.normal_cut_handlebodies import normal_cut_handlebodies
from fastunknot.normal_parallelity import normal_cut_parallelity
from fastunknot.parallelity_boundary_moments import _compile
from fastunknot.core_handlebody import core_handlebody_certificate, select_core_forest
from fastunknot.disk_bundle_absorption import absorb_disk_bundles,source_core_circle
from fastunknot.core_three_handle_reduction import reduce_core_three_handles

def reduce(w):
 out=[]
 for x in w:
  if out and x==-out[-1]:out.pop()
  else:out.append(x)
 return out

def cyclic(w):
 w=reduce(w)
 while len(w)>1 and w[0]==-w[-1]:w=w[1:-1]
 return w

def inv(w):return [-x for x in w[::-1]]

def coreword(core,handle,forest):
 word=[]
 for flag in handle['cycle']:
  if flag['dimension']!=1 or flag['handle'] in forest:continue
  h=core['handles1'][flag['handle']]
  a=(flag['tetrahedron'],flag['face'])
  if a==(h['tetrahedron'],h['face']):sign=1
  elif a==(h['target_tetrahedron'],h['target_face']):sign=-1
  else:raise ValueError((a,h))
  word.append(sign*(flag['handle']+1))
 return word

def inspect(case):
 p=normal_cut_parallelity(case['triangulation'],case['coordinates'],record_certificate=True)
 g=p['geometry'];s=p['summary'];b=_compile(g,p['certificate']['input_sha256'],None,True,lambda:None,'pair')['skeleton']
 output={'id':case['id'],'bases':[{k:v for k,v in x.items() if k!='core_ports'} for x in s['base_profiles']],'attachments':len(b['attachment_components'])}
 output['modes']=[]
 for mode in ['source','max_passages','reverse_id']:
  forest=select_core_forest(g['core'],strategy=mode)
  geom=g
  if g['core']['handles3']:
   reduced=reduce_core_three_handles(g,strategy='max_weight',lower_forest=forest)
   if reduced is None:continue
   geom=reduced[0]
  deferred={i for i,p in enumerate(s['base_profiles']) if (p['euler_characteristic'],p['boundary_components'])!=(1,1)}
  aug=absorb_disk_bundles(geom,s,b,primitive_bases=deferred)
  if aug is None:continue
  augmented=aug[0]
  proof=core_handlebody_certificate(augmented,forest=forest)
  if proof['status']!='COMPLETE':
   output['modes'].append({'mode':mode,'core':proof['status'],'reason':proof.get('reason')});continue
  # Augmented disk rows need source-circle signs, original rows contain flags.
  active={h['id']:coreword(augmented,h,set(forest)) for h in augmented['handles2'][:len(geom['core']['handles2'])]}
  # Reduction may alter rows? dedicated version below guards their cycle metadata.
  for rr in aug[1]['components']:
   active[rr['two_handle']]=[c['sign']*(c['handle']+1) for c in rr['crossings'] if c['handle'] not in forest]
  passive={};raw={};owners={}
  base_owner={port:i for i,p in enumerate(s['base_profiles']) for port in p['core_ports']}
  for ai,a in enumerate(b['attachment_components']):
   if a['kind']!='circle':continue
   base=base_owner[abs(a['word'][0])-1]
   if base not in deferred:continue
   crossed,_=source_core_circle(geom,a['word'])
   raw[ai]=[c['sign']*(c['handle']+1) for c in crossed if c['handle'] not in forest]
   passive[ai]=raw[ai];owners[ai]=base
  raw_lengths={i:len(w) for i,w in passive.items()}
  for r,h in proof['certificate']['cancellations']:
   donor=active.pop(r);h+=1
   positions=[i for i,x in enumerate(donor) if abs(x)==h]
   if len(positions)!=1:raise ValueError(('invalid pivot',r,h,donor))
   at=positions[0];image=inv(donor[at+1:]+donor[:at]) if donor[at]>0 else donor[at+1:]+donor[:at]
   for bank in (active,passive):
    for i,w in list(bank.items()):
     image_inv=inv(image)
     out=[]
     for x in w:out.extend(image if x==h else image_inv if x==-h else [x])
     bank[i]=reduce(out)
  output['modes'].append({'mode':mode,'core':'COMPLETE','components':proof['components'],'annuli':[{'attachment':i,'base':owners[i],'raw':raw[i],'final':cyclic(w),'raw_length':raw_lengths[i]} for i,w in passive.items()]})
 return output

if __name__=='__main__':
 results=[];fail=[];counts=collections.Counter()
 for filename in ['corpus.json','moment_corpus.json','three_handle_corpus.json']:
  for case in json.loads((ROOT/'marked_parallelity_research'/filename).read_text())['cases']:
   if case['id'].startswith(('binary/','large/')):continue
   r=normal_cut_handlebodies(case['triangulation'],case['coordinates'],boundary_method='moments')
   counts[(filename,r['status'],r.get('reason'))]+=1
   if r['status']!='COMPLETE':
    try:d=inspect(case);d.update(corpus=filename,reason=r.get('reason'));results.append(d)
    except Exception as e:
     print('ERROR',filename,case['id'],repr(e),flush=True);continue
    pathlib.Path('/workspace/scratch/9f3a01c0ff48/experiments_native/annuli_audit.json').write_text(json.dumps(results,indent=2)+'\n')
    print(filename,case['id'],r.get('reason'),[(m['mode'],m['core'],[(a['base'],a['raw'],a['final']) for a in m.get('annuli',[])]) for m in d['modes']],flush=True)
 print([(k,v) for k,v in counts.items()])
