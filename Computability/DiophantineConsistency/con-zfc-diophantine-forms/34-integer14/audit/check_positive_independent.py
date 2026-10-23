"""Independent quadratic-algebra evaluation of the homogeneous nested norm."""
import json,random,hashlib
from pathlib import Path
root=Path(__file__).resolve().parent.parent/'positive'
rng=random.Random(860223);out={}
for path in sorted(root.glob('positive12_shift_*_product.json')):
 p=json.loads(path.read_text());trials=0
 for prime in [101,1009,100003]:
  for _ in range(80):
   e={n:rng.randrange(-8,9)%prime for n in p['witnesses']+p['fixed_numerals']}
   def val(x):return e[x] if isinstance(x,str) else x%prime
   for name,op,a,b in p['source']:
    x,y=val(a),val(b);e[name]=({'+' :lambda:x+y,'-':lambda:x-y,'*':lambda:x*y}[op]())%prime
   rad=e['G']
   def add(a,b):return((a[0]+b[0])%prime,(a[1]+b[1])%prime)
   def mul(a,b):return((a[0]*b[0]+rad*a[1]*b[1])%prime,(a[0]*b[1]+a[1]*b[0])%prime)
   def scale(a,x):return(a[0]*x%prime,a[1]*x%prime)
   def sq(a):return mul(a,a)
   H,M,A,D,d,Q,c,T,b=[e[n] for n in ['H','Mbase','A','D','d','Q','c','T','b']]
   if p['variant'] in ['half','half_aux']:M*=2
   xx=(e['W'],-e['L']%prime);xs=sq(xx)
   ee=e['P']+e['U']-1;bb=2*Q*c*T*b
   cc=add(scale(xs,d),(H*H*(d*M*M*A-ee)%prime,0))
   uu=H**4*D*bb*bb%prime
   ff=add(add(sq(cc),(uu,0)),scale(xs,-4*d*d*H*H*M*M*A))
   ff=add(sq(ff),scale(sq(cc),-4*uu))
   want=(ff[0]**2-rad*ff[1]**2)%prime
   assert want==e['N']
   trials+=1
 out[path.name]={'quadratic_algebra_assignments':trials,'sha256':hashlib.sha256(path.read_bytes()).hexdigest()}
Path(__file__).with_name('POSITIVE_INDEPENDENT_CHECKS.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out))
