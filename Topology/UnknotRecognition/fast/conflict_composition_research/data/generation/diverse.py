"""Short native LP batches: diverse full-source anchors and Q column orders."""
import argparse
import json
from random import Random
from time import monotonic
from fastunknot.normal_surface_geometry import _prepare
from fastunknot.normal_sector import _assemble_sector_kernel
from fastunknot.normal_euler import _euler_model
from fastunknot.normal_euler_tree import _formal_lift
from fastunknot.exact_lp import solve_nonnegative_kernel
from fastunknot.integer_codec import json_safe
from prepare import HERE,pins,digest


def main():
 p=argparse.ArgumentParser();p.add_argument('case');p.add_argument('--seconds',type=float,default=20);p.add_argument('--query-seconds',type=float,default=3);p.add_argument('--queries',type=int,default=20);p.add_argument('--seed',type=int,default=20261013);a=p.parse_args()
 path=HERE/(a.case+'-state.json');state=json.loads(path.read_text());source=state['chain']['triangulation'];key=digest(source);before=pins();started=monotonic();deadline=started+a.seconds
 rays=state['raw_rays'].setdefault(key,[]);seen={digest(r['coordinates']) for r in rays};record=dict(kind='diverse_anchors',source_sha256=key,seed=a.seed,native_sha256=before,queries=[])
 state['attempts'].append(record)
 def save():path.write_text(json.dumps(json_safe(state),indent=2)+'\n')
 def check():
  if monotonic()>deadline:raise TimeoutError('cooperative research phase ceiling')
 prepared=_prepare(source,check);n=len(source['tetrahedra']);kernel=_assemble_sector_kernel(source,prepared,tuple((t,q) for t in range(n) for q in range(3)),check);linear,weights=_euler_model(kernel,check)
 assert len(kernel.groups)==1 and weights==(1,)
 rng=Random(a.seed);anchors=list(kernel.groups[0]);rng.shuffle(anchors)
 for i in range(a.queries):
  if monotonic()>deadline:break
  anchor=anchors[i%len(anchors)];objective=[linear[j]-kernel.potentials[anchor][j] for j in range(3*n)];order=list(range(3*n));rng.shuffle(order);query_end=min(deadline,monotonic()+a.query_seconds)
  def limited():
   if monotonic()>query_end:raise TimeoutError('cooperative per-anchor ceiling')
  query=dict(anchor=anchor,objective=objective,column_permutation=order)
  record['queries'].append(query)
  try:
   result=solve_nonnegative_kernel([[row[j] for j in order] for row in kernel.cycle_rows],[objective[j] for j in order],max_pivots=1500,max_ellipsoid_iterations=300,max_feasibility_calls=10,check=limited)
   query['result']=result
   if result['status']=='POSITIVE':
    q=[0]*(3*n)
    for j,value in zip(order,result['primitive_x']):q[j]=value
    rows,chi,conflicts=_formal_lift(kernel,q,check);assert chi>0
    d=digest(rows);query.update(canonical_euler=chi,conflicts=conflicts,coordinates_sha256=d)
    if d not in seen:
     seen.add(d);rays.append(dict(coordinates=rows,euler_characteristic=chi,conflicts=conflicts,coordinates_sha256=d,origin='native full-source anchor LP with permuted columns; independent STANDARD replay pending'))
   query['status']=result['status']
  except TimeoutError as e:query.update(status='TIMEOUT',reason=str(e))
  save()
 record['native_pins_unchanged']=pins()==before;record['complete_queries']=len(record['queries']);save()
 print(dict(case=a.case,source_tetrahedra=n,queries=len(record['queries']),positive=sum(q['status']=='POSITIVE' for q in record['queries']),timeouts=sum(q['status']=='TIMEOUT' for q in record['queries']),rays=len(rays),pins=record['native_pins_unchanged']),flush=True)
 print([(q['anchor'],q['status'],q.get('conflicts')) for q in record['queries']],flush=True)

if __name__=='__main__':main()
