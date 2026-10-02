"""Independent coefficient replay using one common integer denominator.

This does not use the producer, LP, zeros, Gram moments, or GMP linear solver.
Its direct binomial multiplication formula matches ordinary product polynomials.
"""
import json,sys,math,time
from pathlib import Path
from fractions import Fraction as F
from functools import lru_cache
if not __debug__:
 raise RuntimeError('Exact certificate audit must run without Python optimization (-O or -OO).')
if hasattr(sys,'set_int_max_str_digits'):sys.set_int_max_str_digits(0)
D=Path(__file__).parent
T={r['id']:r for r in map(json.loads,(D/'a4_gaps.jsonl').read_text().splitlines())}
O={r['id']:r for r in json.loads((D/'face_orbits.json').read_text())}
@lru_cache(None)
def multiply(a,b):
 out=[(0,1)];i=0
 while a or b:
  p=a&7;q=b&7;nextout=[]
  for k in range(max(p,q),p+q+1):
   assert k<8
   factor=math.comb(k,p)*math.comb(p,p+q-k)
   nextout.extend((e+(k<<(3*i)),c*factor) for e,c in out)
  out=nextout;a>>=3;b>>=3;i+=1
 return out

def verify(tid):
 start=time.time();data=json.loads((D/f'global_integer_sextic_shifted_gmp_{tid}.json').read_text());assert data['template']==tid and data['gap']==3
 cert=data['certificate'];assert cert is not None
 actions=[a['variable_map'] for a in O[tid]['actions']];d=T[tid]['variables'];rays=[];denominator=1
 assert actions and all(sorted(a)==list(range(d)) for a in actions)
 def valid_code(e):return isinstance(e,int) and 0<=e<(1<<(3*d))
 for raw_weight,(m,terms) in cert['squares']:
  w=F(raw_weight);assert w>=0 and valid_code(m)
  z=[(a,F(c)) for a,c in terms];assert len({a for a,c in z})==len(z) and all(valid_code(a) for a,c in z)
  zd=math.lcm(*(c.denominator for a,c in z)) if z else 1
  rayden=w.denominator*zd*zd*len(actions)
  rays.append((m,w.numerator,rayden,[(a,c.numerator*(zd//c.denominator)) for a,c in z]))
  denominator=math.lcm(denominator,rayden)
 remainder=[(e,F(c)) for e,c in cert['positive_binomial_remainder']]
 for e,c in remainder:assert c>=0 and valid_code(e);denominator=math.lcm(denominator,c.denominator)
 total={}
 @lru_cache(None)
 def images(e):return tuple(sum(((e>>(3*i))&7)<<(3*perm[i]) for i in range(d)) for perm in actions)
 for m,wnum,rayden,z in rays:
  weight=wnum*(denominator//rayden)
  for i,(a,u) in enumerate(z):
   for j in range(i,len(z)):
    b,v=z[j];factor=weight*u*v*(1 if i==j else 2)
    for e,c in multiply(a,b):
     for f,k in multiply(e,m):
      q=factor*c*k
      for im in images(f):total[im]=total.get(im,0)+q
 for e,c in remainder:total[e]=total.get(e,0)+c.numerator*(denominator//c.denominator)
 total={e:c for e,c in total.items() if c};expected={e:c*denominator for e,c in T[tid]['gap3']}
 assert total==expected,'Exact coefficient mismatch'
 report={'template':tid,'gap':3,'integer_lifted_pass':True,'squares':len(rays),'positive_remainder_terms':len(remainder),'coefficients':len(expected),'denominator_bits':denominator.bit_length(),'seconds':time.time()-start}
 print(json.dumps(report),flush=True);return report
if __name__=='__main__':
 ids=list(map(int,sys.argv[1:]))
 if not ids:raise SystemExit('Usage: python verify_global_integer_sextic_lifted.py TEMPLATE_ID [TEMPLATE_ID ...]')
 reports=[verify(tid) for tid in ids]
 (D/'global_integer_sextic_lifted_verification.json').write_text(json.dumps(reports,indent=2)+'\n')
