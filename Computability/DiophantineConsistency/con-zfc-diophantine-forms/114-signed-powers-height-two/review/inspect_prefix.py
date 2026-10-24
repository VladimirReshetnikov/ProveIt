import collections,json
from pathlib import Path
base=Path('/workspace/scratch/d92ebb3227ad/signed_frame/source')
s=json.loads((base/'sign_certificate.json').read_text());r=json.loads((base/'raw_builder.json').read_text());d=json.loads((base/'domain75.json').read_text())
drop={548,575,584,592,600,609,618,627,636}; signed={546,573,583,591,599,607,617,625,635}
def poly(ts):
 p=collections.defaultdict(int)
 for c,m in ts:p[tuple(sorted(m))]+=c
 return {m:c for m,c in p.items() if c}
def add(a,b,scale=1):
 z=collections.defaultdict(int,a)
 for m,c in b.items():z[m]+=scale*c
 return {m:c for m,c in z.items() if c}
def mul(a,b):
 z=collections.defaultdict(int)
 for ma,ca in a.items():
  for mb,cb in b.items():z[tuple(sorted(ma+mb))]+=ca*cb
 return {m:c for m,c in z.items() if c}
def comb(recipe):
 z={}
 for t in recipe:z=add(z,mul(poly(t['multiplier']),poly(r['rows'][t['row']]['terms'])))
 return z
bounds={g['predicate']['raw_variables'][0]:0 for g in d['guards'] if g['predicate']['kind']=='retained_scalar' and g['predicate']['raw_variables'][0] not in drop}
bounds.update({87:2,93:2})
steps=sum((q['preceding_sign_steps'] for q in s['prefix_proof']['five_stages']),[])+s['prefix_proof']['final_sign_steps']
for st in steps:
 want=add({(st['variable'],):st['coefficient']},poly(st['rhs']),-1)
 assert poly(r['rows'][st['row']]['terms']) in [want,{m:-c for m,c in want.items()}],(st['variable'],st['row'])
for st in s['prefix_proof']['five_stages']+s['prefix_proof']['preliminary_t_n_bounds']:
 assert comb(st['row_combination'])==add(mul(poly(st['factor']),{(st['variable'],):1}),poly(st['rhs']),-1)
def low(ts):
 total=0
 for c,m in ts:
  if c<0:return None
  term=1
  for v,e in collections.Counter(m).items():
   if v not in bounds:
    if e%2:return None
    term=0
   else:term=min(3,term*pow(bounds[v],e))
  total=min(3,total+c*term)
 return total
# All gate derivations are exact; cap every bound at3 to avoid giant integers.
for _ in range(30):
 old=bounds.copy()
 for st in steps:
  z=low(st['rhs'])
  if z is not None:bounds[st['variable']]=max(bounds.get(st['variable'],0),min(3,z))
 # Five non-gate deductions use only their listed source coordinates.
 for st in s['prefix_proof']['preliminary_t_n_bounds']:
  z=low(st['rhs'])
  if z is not None:bounds[st['variable']]=max(bounds.get(st['variable'],0),z)
 for st in s['prefix_proof']['five_stages']:
  if st['variable']==130:
   deps={59,87,131,106,107,123}
   if deps<=bounds.keys():bounds[130]=0
  else:
   if low(st['factor']) is not None and low(st['factor'])>=1 and low(st['rhs']) is not None:
    bounds[st['variable']]=max(bounds.get(st['variable'],0),int(low(st['rhs'])>=1))
 if bounds==old:break
print('prefix known',len([v for v in bounds if v<643]))
print('missing prefix',sorted(set(range(643))-bounds.keys()))
print('missing unsigned frame',sorted(set(s['frame_arguments'])-signed-bounds.keys()))
print('unsigned frame lower',[(v,bounds.get(v)) for v in s['frame_arguments'] if v not in signed])
for call in s['power_calls']:
 if call['output'] in signed:
  seed=next(t for t in s['seeds'] if t['aliases']['k']==call['exponent'])
  print('selected',call['index'],call['output'],call['base'],bounds[call['base']],call['exponent'],bounds[call['exponent']],seed['aliases']['YminusK'])
print('remaining power outputs known',all(p['output'] in bounds or p['output'] in signed for p in s['power_calls']))
