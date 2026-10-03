#!/usr/bin/env python3
"""Independent mathematical audit of normalized auxiliary Bezout projection.
Reads authenticated JSON and proof bytes only; never imports author/historical code.
The general proof is in the companion note. Bounded checks are supplementary.
"""
import argparse
import hashlib
import json
from collections import Counter
from pathlib import Path

if not __debug__:
    raise RuntimeError('Run this assertion-based audit without optimized Python.')

PINS = {
'complete86_factored_first_root.py': '29cf4100b846bcbabb05185550b7d9ead6b572746048b94998a13c83eeaff40f',
'complete86_factored_first_root.json': '2dfe46fe9c5537ff51eb3c542806c58242238363e6018f9daab7eabf0b6fe61e',
'complete113_asymmetric_retained109.md': 'cee18b24b50fcea5f3cd6fa9fb20f8dbdd5ae9f5e99107e24ffff4e66b3305f0',
'complete86_transport_quotient_shear.py': 'c1cb668ae5538d168652c07627c00255d9c00a7d6373feb45da8c7c3806c9c45',
'complete86_transport_quotient_shear.json': '77ec7894c68f16e8d2dbb48f7c444bf7ab5e2c08f895bdad877f61b8c9c96efc',
'complete86_transport_quotient_shear.md': 'fd0254d6cb0a35686cd824e3f29384c9aed8141444256ce0a9442133a2785541',
'complete86_factored_first_root.md': '9f2b50449e0724e523e9dd5d022f229b77504976f23ee52ca2917cf11ceb322b',
'complete75_coupled_index_linear88.md': '1533ef2411347335704f46a8a1020d8d46dea1147b03e9c9d35684a687172e39',
'complete75_normalized_strong87.md': '9c1cfa3ccd5a71c127c8e6aa341fad6e857788d708129e04ea177dbbcdccfb3b',
'complete75_asymmetric_scale_tradeoffs.md': '3fb7aad219cc05570531c2e806bd4f4998681777963063761106400514a146c2',
'complete75_reversed_auxiliary89.md': '4eddb6627b6261b1d8f8617006e443908574c0b7b2d3fdda15ff85dc86bd9700',
'../../1980/PELL_RELAXED_AUXILIARY_PROOF.md': '9849260ea2776d26e9b615e0e1ed6fcd9b1c9e0e4cedb6cd8aaa2c0346ecbc90',
'../../1980/HALF_PARAMETER_PELL_92_PROOF.md': 'c1132ffe3610ff4132ca0a82312e24774328f4e9b3ed3b6f641055a7f29bfa7b',
'../../1980/FIXED_RAW_UNIVERSAL_75_PROOF.md': 'e381124c969087ffa867448177a9df693d81e7bd85dd3a8489d443220fba053d',
}
AUTHOR = {'complete85_auxiliary_bezout_projection.py': '3f619205a670b420312ba31d52b89cd8c87c169763ddf6c317c2db44ef0698f0', 'complete85_auxiliary_bezout_projection.json': 'e7ddc113f96cde37efc9d1973daffa5e4cef221db2c1d1c6ad1cf1772cd59edc', 'complete85_auxiliary_bezout_projection.md': 'd8f91555bed114470ee5dfb742175079f2df25e9c04d75abbf16752e70a91a4b'}
FACTORS = ['norm_first','norm_main','norm_input','norm_aux','norm_index','norm_transport','norm_strong']


def digest(b): return hashlib.sha256(b).hexdigest()
def exact(a,b):
    if type(a) is not type(b): return False
    if isinstance(a,dict): return a.keys()==b.keys() and all(exact(a[k],b[k]) for k in a)
    if isinstance(a,list): return len(a)==len(b) and all(exact(x,y) for x,y in zip(a,b))
    return a==b

def read_pins(root, pins):
    result={}
    for name,expected in pins.items():
        path=Path(root)/name
        b=path.read_bytes()
        assert digest(b)==expected, ('pin mismatch',name)
        result[name]=b
    return result

# Sparse integer polynomial ring, with monomials as sorted variable tuples.
class Poly:
    def __init__(self,d): self.d={m:c for m,c in d.items() if c}
    @staticmethod
    def coerce(x): return x if isinstance(x,Poly) else Poly({():x})
    @staticmethod
    def var(x): return Poly({(x,):1})
    def __add__(self,other):
        z=dict(self.d)
        for m,c in self.coerce(other).d.items(): z[m]=z.get(m,0)+c
        return Poly(z)
    __radd__=__add__
    def __neg__(self): return Poly({m:-c for m,c in self.d.items()})
    def __sub__(self,o): return self+-self.coerce(o)
    def __rsub__(self,o): return self.coerce(o)+-self
    def __mul__(self,other):
        z={}
        for m,c in self.d.items():
            for n,d in self.coerce(other).d.items():
                k=tuple(sorted(m+n));z[k]=z.get(k,0)+c*d
        return Poly(z)
    __rmul__=__mul__
    def __pow__(self,n):
        z=Poly.coerce(1)
        for _ in range(n): z=z*self
        return z
    def __eq__(self,o): return self.d==self.coerce(o).d


def algebra():
    c,T,f,R,D,i,K,u,k,x=map(Poly.var,['c','T','f','R','Delta','i','K','u','k','x'])
    Ns=f*f-D*i*i*c**4
    V=c*(T*f-1)-R*f*f
    o=c*T-R*f
    j=T*f-R*D*i*i*c**3-1
    assert o*f-c==V
    assert V+R-c*j==R*(1-Ns)
    assert V-c*j+K==(K-R)+R*(1-Ns)
    assert c*T==o+R*f
    # Negative first Pell norm descent preserves the actual norm polynomial.
    disc=u*(u+1); P=2*u+1
    assert (P*x-2*disc*k)**2-disc*(P*k-2*x)**2==x*x-disc*k*k
    X,Y=map(Poly.var,['X','Y']); a=Y*(X+1); A=a+2; first=2*X*Y*Y+1
    assert (2*A*A-1)-first==2*Y*Y*(X*X+X+1)+8*Y*(X+1)+6
    # Explicit strong-norm margin and auxiliary integer-gap contradiction.
    f2=1+D*i*i*c**4; H=D*(f2-1)
    assert H-(R*f2+c)==(D-R)*f2-D-c
    w,H0=map(Poly.var,['w','Haux'])
    assert w*w-1-(H0-1)*(2*w+1)==w*(w-2*H0+2)-H0
    return {'exact_ring_identities':8,'all_value_local_restoration':True,
            'whole_output_correction_requires_retained_factor_identity':True}


def pell(A,n):
    x,y=1,0
    for _ in range(n): x,y=A*x+(A*A-1)*y,x+A*y
    return x,y


def supplemental():
    counts=Counter()
    # Finite residue checks, not the proof of the general integer statements.
    for A in range(4):
      d=A*A-1
      for c in range(4):
       for f in range(4):
        for i in range(4):
         assert (f*f-d*i*i*c**4)%4!=3
         counts['strong_mod4']+=1
         for V in range(4):
          for y in range(4):
           h=d*d*i*i*c**4
           assert (h*(V*V-y*y)+y*y)%4!=3
           assert (V*V-d*y*y)%4!=3
           counts['auxiliary_and_standard_mod4']+=1
    for h in range(2,65):
      for v in range(2,2*h-1):
       assert v*v-1-(h-1)*(2*v+1)<0
       counts['nontrivial_root_gap_bound']+=1
    for R in range(1,11):
      for d in (R+1,R+5):
       for c in range(3,11):
        for i in range(1,4):
         f2=1+d*i*i*c**4; h=d*(f2-1)
         assert f2>4*c*c and h>R*f2+c
         counts['strong_size_margin']+=1
    for R in (51,52,79,100):
      for E in (R+3,2*R,3*R+1):
       for eps in (-1,1):
        for n in range(1,R):
         for v in (-2,-1,0,1,2):
          if 2*n==R+eps+v*E: assert v==0
          counts['asymmetric_no_wrap']+=1
    for X in range(2,6):
      for Y in range(2,6):
       A=Y*(X+1)+2; P=2*X*Y*Y+1; Q=2*A*A-1
       assert P>A and Q>P and A>Y+1
       for n in range(1,6):
        k=2*pell(P,n)[1]
        assert pell(A,2*n)[1]==2*A*pell(Q,n)[1]>=A*k
        assert pell(A,2*n+1)[1]>k*(Y+1)
        counts['negative_index_ratio']+=1
    # Independent actual Pell auxiliary fixtures: these are NOT full compiler zeros.
    fixtures=[]
    for A in range(2,6):
      p=3; d=A*A-1; D,c=pell(A,p); m=2*p*c; f,u=pell(A,m)
      assert u%(c*c)==0
      i=u//(c*c); h=d*u; xv,y=pell(h,p)
      assert xv%h==0
      V=xv//h; assert (V+c)%f==0 and (V+p)%c==0
      o=(V+c)//f; j=(V+p)//c
      assert (o+p*f)%c==0
      T=(o+p*f)//c
      assert min(i,V,o,j,T)>0
      assert V==c*(T*f-1)-p*f*f
      assert o==c*T-p*f and j==T*f-p*d*i*i*c**3-1
      assert f*f-d*i*i*c**4==1 and h*h*(V*V-y*y)+y*y==1
      assert V-j*c+1+p==1
      fixtures.append({'A':A,'p':p,'m':m,'c':c,'largest_value_bits':max(z.bit_length() for z in (f,V,y,T))})
    for A in range(2,6):
      for p in (2,3):
       D,c=pell(A,p)
       for mult in (1,2):
        m=p*c*mult; f,z=pell(A,m)
        assert z%(c*c)==0 and m%(p*c)==0
        assert (z//c-(m//p)*pow(D,m//p-1,c))%c==0
        counts['normalized_rank_binomial']+=1
    return {'bounded_checks':dict(counts),'auxiliary_only_fixtures':fixtures,
            'full_native_compiler_zero_materialized':False}


def literal_math_interface(parent,child):
    old={r[0]:r for r in parent['source']};new={r[0]:r for r in child['source']}
    expected={
      'wn2':['wn2','*','w','q'], 'sn2':['sn2','*','s','n2'],
      'R10b':['R10b','+','eta','zeta'],'R10a':['R10a','+','ksn2','eta'],
      'R12':['R12','+','UM','sn2'],'A':['A','+','a_square','a4m5'],
      'norm_strong':['norm_strong','-','L16','strong_difference'],
      'R16':['R16','*','A','strong_difference'],
      'index_difference':['index_difference','-','R10b','hpm1'],
      'norm_index':['norm_index','-','index_difference','r_lhs'],
      'kinner':['kinner','+','Kconstant','w'],
    }
    for name,row in expected.items(): assert old[name]==new[name]==row
    erased={'of','jc','linear_difference','norm_linear','eight_units'}
    replaced={'aux_u_rhs','polynomial'}
    for name,row in old.items():
      if name not in erased|replaced: assert new[name]==row
    assert [r for r in parent['source'] if 'o' in r[2:]]==[['of','*','o','f']]
    assert [r for r in parent['source'] if 'j' in r[2:]]==[['jc','*','j','R10a']]
    assert old['eight_units']==['eight_units','*','seven_units','norm_linear']
    assert child['free']==['auxiliary_quotient' if v=='o' else v for v in parent['free'] if v!='j']
    assert 'o' not in child['free'] and 'j' not in child['free']
    assert 'auxiliary_quotient' in child['free']
    assert new['aux_u_rhs']==['aux_u_rhs','-','auxiliary_c_Tf','auxiliary_R_f2']
    assert new['auxiliary_c_Tf']==['auxiliary_c_Tf','*','R10a','auxiliary_Tf_minus_one']
    assert new['auxiliary_Tf_minus_one']==['auxiliary_Tf_minus_one','-','auxiliary_Tf',1]
    assert new['auxiliary_Tf']==['auxiliary_Tf','*','auxiliary_quotient','f']
    assert new['auxiliary_R_f2']==['auxiliary_R_f2','*','r_lhs','L16']
    assert new['polynomial']==['polynomial','-','seven_units',1]
    assert set(new)==(set(old)-erased)|{'auxiliary_c_Tf','auxiliary_Tf_minus_one','auxiliary_Tf','auxiliary_R_f2'}
    # Independently expand each literal finalizer, with full norm ports cut.
    def tail(packet,names):
        rows={n:(op,a,b) for n,op,a,b in packet['source']}
        memo={n:Poly.var(n) for n in names}
        def at(n):
            if type(n) is int: return Poly.coerce(n)
            if n not in memo:
                op,a,b=rows[n];a,b=at(a),at(b)
                memo[n]=a*b if op=='*' else a+b if op=='+' else a-b
            return memo[n]
        return at(packet['output'])
    expected=Poly.coerce(1)
    for n in FACTORS: expected=expected*Poly.var(n)
    child_tail=tail(child,FACTORS)
    parent_tail=tail(parent,FACTORS+['norm_linear'])
    assert child_tail==expected-1
    assert parent_tail+1==(child_tail+1)*Poly.var('norm_linear')
    ledger=Counter('M' if row[1]=='*' else 'A' for row in child['source'])
    assert dict(ledger)=={'M':48,'A':37} and len(child['witnesses'])==18
    return {'same_retained_instructions':len(old)-len(erased|replaced),'local_changed_gates':5,'actual_finalizer_identities':2,
            'full_literal_operations':len(child['source']),'M':48,'A':37,'positive_witnesses':18,
            'exact_degree_independently_audited':False}


def verify(root,author_root):
    blobs=read_pins(root,PINS)
    assert len(AUTHOR)==3, 'Author freeze pins required.'
    authored=read_pins(author_root,AUTHOR)
    parent=json.loads(blobs['complete86_transport_quotient_shear.json'])['forms'][0]['packet']
    report=json.loads(authored['complete85_auxiliary_bezout_projection.json'])
    assert report['source_sha256']==AUTHOR['complete85_auxiliary_bezout_projection.py']
    assert all(PINS[n]==h for n,h in report['parent_pins'].items())
    child=report['packet']
    return {'status':'PASS','review_source_sha256':digest(Path(__file__).read_bytes()),
      'author_pins':AUTHOR,'dependency_pins':PINS,
      'interface':literal_math_interface(parent,child),'algebra':algebra(),'supplementary':supplemental(),
      'scope':'Independent positive-zero bijection and native sign proof; literal mathematical interface; bounded supplementary checks. No author/historical imports, API audit, exact-degree audit, or full universal Pell tuple.'}


def main():
    p=argparse.ArgumentParser();p.add_argument('--root',required=True);p.add_argument('--author-root');p.add_argument('--write');p.add_argument('--expect')
    a=p.parse_args();r=verify(a.root,a.author_root or a.root)
    assert exact(r,json.loads(json.dumps(r))), 'typed JSON roundtrip'
    if a.expect: assert exact(r,json.loads(Path(a.expect).read_text())), 'saved receipt mismatch'
    if a.write: Path(a.write).write_text(json.dumps(r,indent=2,sort_keys=True)+'\n')
    print(json.dumps({'status':r['status'],'operations':r['interface']['full_literal_operations'],'scope':r['scope']}))
if __name__=='__main__': main()
