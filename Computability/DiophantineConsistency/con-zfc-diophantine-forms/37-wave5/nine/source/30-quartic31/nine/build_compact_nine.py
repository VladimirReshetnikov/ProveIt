if not __debug__: raise SystemExit('Optimized Python is not permitted: assertions are audit checks.')
"""Newly authored Jones circuit specialization and magnitude-companion finalizer.
Imports only the independent rewriter newly authored during this review.
Upstream Python remains inert. No coefficient polynomial is executed as code.
"""
from pathlib import Path
import json,sys,hashlib,collections
HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE.parent/'review'))
from optimize_nine_circuit import Circuit,evaluate,audit_body

def construct(old,scale=1,tight=False):
 d=Circuit(); names={};mapping={}
 def clone(i):
  if i not in mapping:
   node=old['nodes'][i]
   if node['kind'] in ('add','sub','mul'):mapping[i]=d.op(node['kind'],clone(node['left']),clone(node['right']))
   else:mapping[i]=d.intern(node.copy())
  return mapping[i]
 for name,i in old['named_nodes'].items():names[name]=clone(i)
 def add(*xs):
  a=d.const(0)
  for x in xs:a=d.add(a,x)
  return a
 def mul(*xs):
  a=d.const(1)
  for x in xs:a=d.mul(a,x)
  return a
 def sub(a,b):return d.op('sub',a,b)
 def power(a,n):
  if n==0:return d.const(1)
  if n==1:return a
  h=power(a,n//2);s=d.mul(h,h)
  return d.mul(s,a) if n%2 else s
 def save(name,v):names[name]=v;return v
 c=d.const
 lookup={n.get('name'):clone(i) for i,n in enumerate(old['nodes']) if n['kind'] in ('variable','fixed')}
 g,h,s,w,ii,jj=(add(lookup[x],c(1)) for x in ('g0','h0','s0','w0','i0','j0'))
 z=lookup['z_index'];phi=lookup['phi'];R=names['R'];N=names['N'];q=names['q'];B=names['B'];b=names['b'];lam=names['lambda'];ell=names['ell'];P=names['P'];Y=names['Y'];U=names['U']
 # Twice the negative part. Index ensures every other summand is nonnegative.
 deltaR=save('deltaR',add(mul(c(4),z,lam,power(add(c(1),B,g),4),power(q,7),sub(power(N,2),N)),mul(c(2),b,ell,sub(power(N,2),c(1)))))
 if tight:
  deltaR=save('deltaR',mul(c(32),z,lam,power(g,4),power(q,7),sub(power(N,2),N)))
 Rbar=save('Rbar',add(R,deltaR))
 Kbar=save('Kbar',add(Rbar,c(1),mul(h,add(P,c(1)))))
 Abar=save('Abar',mul(Rbar,Y,add(U,c(1))))
 Cbar=save('Cbar',add(mul(c(2),Rbar),c(1),mul(b,w),phi))
 Jbar=save('Jbar',add(mul(c(4),Abar),c(5)))
 Dbar=save('Dbar',add(mul(add(power(Abar,2),c(1)),power(Cbar,2)),c(1)))
 Ebar=save('Ebar',mul(ii,Jbar,Dbar,power(Cbar,2)))
 Fbar=save('Fbar',add(mul(add(power(Abar,2),c(1)),power(Ebar,2)),c(1)))
 Gbar=save('Gbar',add(Abar,mul(Fbar,add(mul(Cbar,Dbar),c(1),Abar))))
 Hbar=save('Hbar',add(mul(c(2),Rbar),c(1),mul(jj,Cbar)))
 V0=save('V0',add(mul(add(P,c(1)),Kbar),c(2)))
 v1=mul(add(mul(add(Abar,c(1)),Cbar),c(1)),add(mul(add(Abar,c(1)),Ebar),c(1)),add(mul(add(Gbar,c(1)),Hbar),c(1)))
 V1=save('V1',add(mul(c(scale),v1),c(1)))
 W=names['W'];div=names['divisor'];dvnd=names['dividend'];a0=names['a0'];a1=names['a1']
 T=save('T',sub(add(mul(div,lookup['n']),dvnd),mul(W,add(dvnd,mul(V0,V1)))))
 inner=save('inner',sub(power(T,2),mul(power(W,2),add(a0,mul(power(V0,2),a1)))))
 out=save('output',sub(power(inner,2),mul(c(4),power(W,4),power(V0,2),a0,a1)))
 body=d.pack(out,names);body.update(nu=old['nu'],L=old['L'],weights=f'magnitude_companions_{"tight_" if tight else ""}scale{scale}',model=old['model'],source_circuit='nine_majorant_runs.json',coefficient_binding='COMPACT_CONSTANTS.json')
 return body

def index_bound(constants,manifest):
 bits={r['name']:r['bit_length'] for r in manifest['files']}
 bb=[bits[k] for k in ('beta','K','MC','MF_source')]
 records=[];global_bound=0
 for r in constants['coefficient_records']:
  terms=collections.defaultdict(int)
  for t in r['coefficient_polynomial_in_fixed_ports']:
   terms[sum(a*b for a,b in zip(bb,t['powers']))]+=abs(t['coefficient'])
  # Exact bound using sparse powers of two (at most about 6 MB transient each).
  bound=sum(c<<e for e,c in terms.items())
  s=(bound+1).bit_length()
  assert bound+1<(1<<s)
  global_bound=max(global_bound,s)
  records.append(dict(name=r['name'],exponent_upper_bound=s,power_of_two_terms=[dict(exponent=e,multiplier=c) for e,c in sorted(terms.items())]))
 constants=dict(constants)
 constants.update(port_binding='Use all four compact943 ports in COMPACT_COEFFICIENT_BINDING.json; MF is MF_source, K0 is K.',z_index=f'2^{global_bound}',index_exponent=global_bound,index_bound_proof='For each record, |c_alpha| is strictly below the sum of |term coefficient| times 2^(dot(port powers,port bit lengths)); the recorded finite sum plus 1 is strictly below 2^index_exponent.',previous_index_bound='The upstream symbolic bound 2+24*sum(rho_j^2) is valid but is superseded here.',actual_port_bit_lengths=bb,nu_caution=f'nu={constants["nu"]} counts parent-quartic witness variables; compact compiler radix exponent 5^10 does not authorize nu=9.')
 return constants,dict(status='PASS',index_exponent=global_bound,port_bit_lengths=bb,records=records)

if __name__=='__main__':
 raise SystemExit('Use the top-level verify_release.py for the selected final candidate.')
