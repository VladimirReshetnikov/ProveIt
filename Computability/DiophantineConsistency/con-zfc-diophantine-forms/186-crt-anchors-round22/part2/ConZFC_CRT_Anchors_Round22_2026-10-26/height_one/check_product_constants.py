"""Independent exact normalization-rewrite checker; no producer imports."""
import copy

def require(b,m):
 if not b:raise ValueError(m)

def unorient(row):
 r=copy.deepcopy(row);sgn=r.pop('orientation',1)
 require(sgn in (-1,1),'row orientation for normalization comparison')
 r['terms']=[[sgn*z,m] for z,m in r['terms']]
 return r

def check(before,after,chain=False):
 require(before['variables']==after['variables'],'unchanged normalization coordinates')
 require(all(before.get(k)==after.get(k) for k in ('original_variables','constant_count','scale_count')),'unchanged normalization counts')
 vs=before['variables'];constants={v['value']:i for i,v in enumerate(vs) if v['kind']=='constant'};scales={(v['coefficient'],v['variable']):i for i,v in enumerate(vs) if v['kind']=='scale'}
 require(len(before['rows'])==len(after['rows']),'unchanged normalized row count')
 records=[]
 for old,new in zip(before['rows'],after['rows']):
  old,new=unorient(old),unorient(new);expected=copy.deepcopy(old)
  if old['kind']=='constant':
   c=old['value'];choices=sorted((b,a) for a in constants for b in constants if 1<a<=b<c and a*b==c)
   if choices:
    b,a=choices[0];pivot=constants[c]
    require(constants[a]<pivot and constants[b]<pivot,'constant product strictly triangular')
    expected['terms']=[[1,[pivot]],[-1,[constants[a],constants[b]]]]
    records.append({'kind':'constant_product','value':c,'factors':[a,b]})
  elif chain and old['kind']=='scale':
   c,x=old['coefficient'],old['variable'];choices=sorted((d,b) for d in constants for b,y in scales if y==x and 1<d<c and d*b==c)
   if choices:
    d,b=choices[0];pivot=scales[c,x]
    require(constants[d]<pivot and scales[b,x]<pivot,'scale product strictly triangular')
    expected['terms']=[[1,[pivot]],[-1,[constants[d],scales[b,x]]]]
    records.append({'kind':'scale_chain','coefficient':c,'variable':x,'multiplier':d,'predecessor':b})
  require(new==expected,'complete exact monic factor-network rewrite')
 return {'status':'pass','unchanged_variables':len(vs),'unchanged_rows':len(before['rows']),'constant_products':sum(r['kind']=='constant_product' for r in records),'scale_chains':sum(r['kind']=='scale_chain' for r in records),'records':records}

def mutations(before,after,chain=False):
 rejected=[]
 for kind in ['constant_product_sign','constant_product_factor','nontriangular_product','source_row_changed','coordinate_value_changed']+(['scale_chain_factor'] if chain else []):
  b=copy.deepcopy(after)
  rs=[r for r in b['rows'] if r['kind']=='constant' and any(len(m)==2 for z,m in r['terms'])];r=rs[0];t=next(t for t in r['terms'] if len(t[1])==2)
  if kind=='constant_product_sign':t[0]*=-1
  elif kind=='constant_product_factor':t[1][0]=t[1][1]+1
  elif kind=='nontriangular_product':t[1][0]=r['terms'][0][1][0]
  elif kind=='source_row_changed':next(r for r in b['rows'] if r['kind']=='source')['terms'][0][0]*=-1
  elif kind=='coordinate_value_changed':next(v for v in b['variables'] if v['kind']=='constant')['value']+=1
  else:
   r=next(r for r in b['rows'] if r['kind']=='scale' and any(len(m)==2 and any(b['variables'][i]['kind']=='scale' for i in m) for z,m in r['terms']));next(t for t in r['terms'] if len(t[1])==2)[1][1]=0
  try:check(before,b,chain)
  except (ValueError,KeyError,IndexError,TypeError):rejected.append(kind)
  else:raise ValueError('Normalization mutation survived: '+kind)
 return rejected
