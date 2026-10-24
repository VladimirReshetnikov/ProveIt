from pathlib import Path
import json,itertools,math,sys
from circuit_helper import Circuit
R=Path(__file__).resolve().parent
REPO=R/'upstream'
BASE=REPO/'71-determinant-guards/nine_positive/generated/composed9_positive.json'
def import_source(x):
 d=Circuit();mapping={}
 for idx,node in enumerate(x['nodes']):
  kind=node['kind']
  if kind=='literal':out=d.c(node['value'])
  elif kind in ('variable','fixed'):out=d.leaf(kind,name=node['name'])
  else:out=d.op(kind,mapping[node['left']],mapping[node['right']])
  mapping[idx]=out
 d.names={name:mapping[idx] for name,idx in x['named_nodes'].items()}
 variables={node['name']:mapping[idx]for idx,node in enumerate(x['nodes'])if node['kind']=='variable'}
 return d,variables
def evaluate(d,poly,vs,order):
 cache={}
 def calc(terms,order):
  key=(tuple(sorted(terms.items())),order)
  if key in cache:return cache[key]
  if not terms:return d.c(0)
  # Factor common integer and common monomial before every recursion.
  g=math.gcd(*(abs(v)for v in terms.values()))
  if all(v<0 for v in terms.values()):g=-g
  shifts=tuple(min(m[j]for m in terms)for j in range(len(vs)))
  norm={tuple(a-b for a,b in zip(m,shifts)):v//g for m,v in terms.items()}
  fac=d.c(g)
  for j,e in enumerate(shifts):
   if e:fac=d.mul(fac,d.pow(vs[j],e))
  if not order:
   if list(norm)!=[(0,)*len(vs)]:raise ValueError('incomplete monomial evaluation')
   out=d.mul(fac,d.c(norm[(0,)*len(vs)]))
  else:
   j=order[0];groups={}
   for m,v in norm.items():
    exp=m[j];m=list(m);m[j]=0;groups.setdefault(exp,{})[tuple(m)]=v
   inds=sorted(groups,reverse=True);prev=inds[0];out=calc(groups[prev],order[1:])
   for exp in inds[1:]:out=d.add(d.mul(out,d.pow(vs[j],prev-exp)),calc(groups[exp],order[1:]));prev=exp
   out=d.mul(fac,out,d.pow(vs[j],prev))
  cache[key]=out;return out
 return calc(poly,tuple(order))
def build(base,typ,order):
 d,variables=import_source(base);c=d.c;n=d.names;A=n['A'];C=n['C'];ii=variables['i'];j=variables['j']
 t=d.save('Laurent_t',d.add(n['B1'],d.mul(d.sub(j,c(1)),C)))
 vs=[A,C,ii,t]
 name={'direct':'laurent_candidate.json','correction':'laurent_correction.json','nopad':'laurent_correction_nopad.json','nopad_D':'laurent_correction_nopad_Dbasis.json','nopad_4JD':'laurent_correction_nopad_4JDbasis.json'}[typ]
 if typ.endswith('_D'):vs.append(n['D'])
 if typ.endswith('_4JD'):vs=[n['J'],C,ii,t,n['D']]
 factor=4 if typ.endswith('_4JD')else 1
 raw=json.loads((R/name).read_text());raw=raw['majorant']if typ=='direct' else raw
 poly={tuple(m):int(v)for m,v in raw};core=evaluate(d,poly,vs,order)
 if typ=='direct':T=core
 else:
  old=n['V1']
  if typ.startswith('nopad'):old=d.mul(d.sub(n['major_T'],d.add(d.mul(c(640),ii),c(4096))),n['H'])
  T=d.sub(d.mul(c(16*factor),d.pow(C,7),old),core)
 T=d.save('Laurent_T',T);scale=d.save('Laurent_scale',d.mul(c(65536*factor),d.pow(C,7)))
 a1=d.save('Laurent_a1',d.mul(d.pow(scale,2),n['D'],n['F'],n['I']))
 Theta=d.save('Laurent_Theta',d.sub(n['E0'],d.mul(n['Omega'],d.add(n['V0'],T))))
 inner=d.sub(d.pow(Theta,2),d.mul(d.pow(n['Omega'],2),d.add(n['a0'],a1)))
 out=d.save('Laurent_F9',d.sub(d.pow(inner,2),d.mul(c(4),d.pow(n['Omega'],4),n['a0'],a1)))
 doc=d.finish(out);doc.update(schema='full-radical-polynomial-majorant-v1',variables=base['variables'],domain=base['domain'],type=typ,horner_order=list(order),exact_degree=1158228)
 for k in ['coefficient_recipes','base_scale_exponent','threshold_scale_exponent','coefficient_bound_exponent','port_bit_lengths','coherent_tuple','source_sha256','layout_sha256','Kcode','W','threshold_B_power']:
  doc[k]=base[k]
 return doc
def main():
 base=json.loads(BASE.read_text());scores=[];best=None
 for typ in ['nopad_4JD']:
  for order in itertools.permutations(range(5)):
   x=build(base,typ,order);count=x['total_operations'];scores.append([count,typ,order])
   if best is None or count<best['total_operations']:
    best=x;print('best',count,typ,order,flush=True)
 (R/'laurent9_positive.json').write_text(json.dumps(best,indent=2)+'\n')
 (R/'laurent9_evaluator_comparison.json').write_text(json.dumps(sorted(scores),indent=2)+'\n')
 print('best',best['total_operations'],best['operation_counts'],best['type'],best['horner_order'],flush=True)
if __name__=='__main__':main()
