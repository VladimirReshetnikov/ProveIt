from pathlib import Path
from hashlib import sha256
import json,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path('research/ordinary13-positive87-to88-aux-model-draft')
for p,h in json.loads((D/'pins.json').read_text()).items():assert sha256(Path(p).read_bytes()).hexdigest()==h,p
G=[json.loads(Path(p).read_text()) for p in ('research/ordinary13-aux-root87-36/candidate.json','research/ordinary13-four-square88-30/candidate.json')]
def ev(g,v,p):
 d=dict(zip(g['witnesses'],v));d.update(zip(g['fixed_numerals'],p))
 for n,op,l,r in g['source']:
  x=d[l] if isinstance(l,str) else l;y=d[r] if isinstance(r,str) else r
  d[n]={'+':lambda:x+y,'-':lambda:x-y,'*':lambda:x*y}[op]()
 return d
for t in range(400):
 v=[(t*(i+4)+i*i+2)%9 for i in range(13)];p=[(t*(j+3)+j)%9-4 for j in range(4)]
 x=(t*3)%11;y=(t*5)%11;w=v.copy();w[11]=y;h=v.copy();h[11]=x
 out87=ev(G[0],w,p);out88=ev(G[1],h,p);base=ev(G[0],v,p)
 q=1+v[0]*p[0];k=v[9]+v[10];c=v[9]+v[7]*k;a=v[6]*v[7]+v[7];delta=3+4*a+a*a
 R=(v[2]+(q-v[1])*(q-1))*(q*q-1)+v[0]*(p[2]+p[3]*q)
 z=v[3]**2*(v[5]*c-R)-c;Q=delta*(v[3]**2-1)
 assert z==base['V']==out87['V']==out88['V'] and Q==base['Q']==out87['Q']==out88['Q']
 first,main,strong=base['A0'],base['A1'],base['g72']
 assert out87['out']==first**2+main**2+(y*y-Q*(y*y-z*z)-1)**2+strong**2
 assert out88['out']==first**2+main**2+((z+x)**2-Q*x*(z+x+z)-1)**2+strong**2
src=(D/'Positive87To88Aux.lean.src').read_text()
for s in ['theorem eval87','theorem eval88','def BoundsCut','1<Q v ∧ 1<z p v*z p v','positive_aux_coordinate_iff','(positive_aux_coordinate_iff (first p v) (main p v) (strong p v) 0 (z p v) (Q v) hQ hz).mpr','(positive_aux_coordinate_iff (first p v) (main p v) (strong p v) 0 (z p v) (Q v) hQ hz).mp']:
 assert s in src,s
print(json.dumps({'actual_literal_graph_controls':400,'arbitrary_signed_port_controls':True,'strict_bounds_explicit':True,'natural_witness_helper_source_only':True,'lean_executed':False},sort_keys=True,indent=2))
