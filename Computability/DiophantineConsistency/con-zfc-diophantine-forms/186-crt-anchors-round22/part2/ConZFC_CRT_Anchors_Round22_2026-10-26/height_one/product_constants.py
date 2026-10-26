"""Use available smaller integer factors for monic constant constructors."""
from normalize import normalize as old_normalize
from split_normalize import normalize as split_normalize

def normalize(source,split=False,chain=False):
 norm=(split_normalize if split else old_normalize)(source)
 constants={v['value']:i for i,v in enumerate(norm['variables']) if v['kind']=='constant'}
 for row in norm['rows']:
  if row['kind']!='constant':continue
  c=row['value']
  options=[(a,c//a) for a in constants if 1<a<c and c%a==0 and a<=c//a and c//a in constants and c//a<c]
  if not options:continue
  a,b=min(options,key=lambda q:(q[1],q[0]))
  row['terms']=[[1,[constants[c]]],[-1,[constants[a],constants[b]]]]
 if chain:
  scales={(v['coefficient'],v['variable']):i for i,v in enumerate(norm['variables']) if v['kind']=='scale'}
  for row in norm['rows']:
   if row['kind']!='scale':continue
   c,x=row['coefficient'],row['variable']
   options=[(d,c//d) for d in constants if 1<d<c and c%d==0 and (c//d,x) in scales]
   if options:
    d,b=min(options)
    row['terms']=[[1,[scales[c,x]]],[-1,[constants[d],scales[b,x]]]]
 return norm
