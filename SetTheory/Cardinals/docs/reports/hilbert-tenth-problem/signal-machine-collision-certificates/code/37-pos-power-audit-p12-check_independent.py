#!/usr/bin/env python3
"""Independent static POWER12 audit. Only stdlib; never executes source files.

Polynomials use fixed-length exponent vectors. All arithmetic is exact. The
finite Pell fixtures use binary powering of a quadratic-ring element, not an
imported recurrence. Acceptance tables are supplied sets, never simulated.
"""
import argparse
import gzip
import hashlib
import json
import math
from pathlib import Path
from fractions import Fraction
import sys

if hasattr(sys, 'set_int_max_str_digits'):
    sys.set_int_max_str_digits(0)

PROOF_HASH = 'c188c29bd5df59c50b1d685feb3259a89b891e7415ba400edb579b5076f6a79f'
MANIFEST_HASH = '2149c3c0fc35d11451764350047c8e15aa0bade664660d3f22670e2f4246cad2'
LEAVES = ('o','g','q_b','q_v','J','q_alpha','d_wb_plus','d_wC_plus',
          'd_yC_plus','q_sigma_plus','q_tau_plus','q_r_plus')
ALIASES = ('d_wb','d_wC','d_yC','q_sigma','q_tau','q_r')

def digest(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()

def snapshot(root):
    result = {}
    for p in [root] + sorted(root.rglob('*')):
        s = p.lstat()
        assert not p.is_symlink(), 'Source symlinks are outside checker scope'
        result[str(p.relative_to(root))] = dict(mode=s.st_mode,size=s.st_size,
            mtime_ns=s.st_mtime_ns,sha256=digest(p) if p.is_file() else None)
    return result

class Ring:
    def __init__(self, names):
        self.names = tuple(names)
        assert len(names) == len(set(names))
        self.zero = (0,)*len(names)
    def const(self, c):
        if isinstance(c, Poly):
            assert c.ring is self
            return c
        assert isinstance(c, int)
        return Poly(self, {self.zero:c} if c else {})
    def var(self, name):
        m = list(self.zero)
        m[self.names.index(name)] = 1
        return Poly(self, {tuple(m):1})

class Poly:
    def __init__(self, ring, terms):
        self.ring = ring
        self.terms = {m:c for m,c in terms.items() if c}
    def __add__(self, q):
        q = self.ring.const(q)
        t = self.terms.copy()
        for m,c in q.terms.items():
            t[m] = t.get(m,0)+c
        return Poly(self.ring,t)
    __radd__ = __add__
    def __neg__(self):
        return Poly(self.ring,{m:-c for m,c in self.terms.items()})
    def __sub__(self,q): return self+-self.ring.const(q)
    def __rsub__(self,q): return self.ring.const(q)+-self
    def __mul__(self,q):
        q = self.ring.const(q)
        t = {}
        for a,c in self.terms.items():
            for b,d in q.terms.items():
                m = tuple(x+y for x,y in zip(a,b))
                t[m] = t.get(m,0)+c*d
        return Poly(self.ring,t)
    __rmul__ = __mul__
    def __pow__(self,n):
        assert isinstance(n,int) and n>=0
        a,p = self.ring.const(1),self
        while n:
            if n&1: a = a*p
            n >>= 1
            if n: p = p*p
        return a
    def __eq__(self,q): return self.terms == self.ring.const(q).terms
    def degree(self): return max(map(sum,self.terms),default=-1)
    def names(self):
        return {self.ring.names[i] for m in self.terms for i,e in enumerate(m) if e}
    def coefficient(self, powers):
        m=tuple(powers.get(n,0) for n in self.ring.names)
        return self.terms.get(m,0)
    def evaluate(self, values):
        powers = {}
        for m in self.terms:
            for i,e in enumerate(m):
                if e and (i,e) not in powers:
                    powers[i,e] = values[self.ring.names[i]]**e
        total = 0
        for m,c in self.terms.items():
            a = c
            for i,e in enumerate(m):
                if e: a = a*powers[i,e]
            total = total+a
        return total
    def payload(self):
        return [[list(m),str(c)] for m,c in sorted(self.terms.items())]

def sos(residuals):
    return sum((h*h for h in residuals),0)

def expressions(base, index, v):
    """Literal displayed formula; works on ints, Fractions, or Poly objects."""
    a = {n[:-5]:v[n]-1 for n in LEAVES if n.endswith('_plus')}
    a.update({n:v[n] for n in LEAVES if not n.endswith('_plus')})
    w,y = base+a['d_wb'], index+a['d_yC']
    beta = 4*y*a['q_b']+1
    V,T = y*y*a['q_v'],index+4*y*a['q_tau']
    M,d = base*a['o']+a['J'],2*base
    A = M+base*base+1
    X = y*A-d*base*y+d*base*a['o']+d*M*a['q_r']
    U = d*beta-A
    S = a['q_alpha']*X+a['q_sigma']*U
    a.update(w=w,y=y,beta=beta,v=V,t=T,M=M,d=d,A=A,X=X,U=U,S=S)
    qa = a['q_alpha']
    h = [X*X-(A*A-d*d)*y*y-d*d,
         U*U-(A*A-d*d)*qa*qa*V*V-d*d*qa*qa,
         S*S-d*d*qa*qa*((beta*beta-1)*T*T+1),
         w-index-a['d_wC'],
         A*A-d*d*(1+((w+1)*(w+1)-1)*w*w*a['g']*a['g'])]
    return h,a

def old_residuals(b,C,a,alpha,u,x,s):
    y,v,beta,t,w,M = [a[n] for n in ('y','v','beta','t','w','M')]
    return [x*x-(alpha*alpha-1)*y*y-1,
      u*u-(alpha*alpha-1)*v*v-1,s*s-(beta*beta-1)*t*t-1,
      beta-1-4*y*a['q_b'],beta-alpha-u*a['q_alpha'],
      v-y*y*a['q_v'],s-x-u*a['q_sigma'],t-C-4*y*a['q_tau'],
      y-C-a['d_yC'],w-b-a['d_wb'],w-C-a['d_wC'],M-b*a['o']-a['J'],
      alpha*alpha-((w+1)**2-1)*(w*a['g'])**2-1,
      2*b*alpha-M-b*b-1,x-y*(alpha-b)-b*a['o']-M*a['q_r']]

def restored(b,C,leaves):
    h,a = expressions(b,C,leaves)
    assert h == [0]*5 and all(leaves[n]>0 for n in LEAVES)
    alpha = Fraction(a['A'],a['d'])
    u = Fraction(a['U'],a['d']*a['q_alpha'])
    x = Fraction(a['X'],a['d'])
    s = Fraction(a['S'],a['d']*a['q_alpha'])
    assert all(z.denominator==1 and z>0 for z in (alpha,u,x,s))
    assert alpha>a['w']>=b and u>=alpha and u>=x and a['beta']>alpha
    assert old_residuals(b,C,a,alpha,u,x,s)==[0]*15
    # Full inverse map includes translating the adapter, not just projection.
    old_leaves = dict(leaves)
    old_leaves['u'] = int(u)
    old_leaves['q_alpha_plus'] = old_leaves.pop('q_alpha')+1
    projected = dict(old_leaves)
    del projected['u']
    projected['q_alpha'] = projected.pop('q_alpha_plus')-1
    assert projected == leaves
    return dict(alpha=int(alpha),u=int(u),x=int(x),s=int(s))

def quadratic_power(z,n):
    D=z*z-1
    def mul(a,b):
        return a[0]*b[0]+D*a[1]*b[1],a[0]*b[1]+a[1]*b[0]
    result, power = (1,0),(z,1)
    while n:
        if n&1: result=mul(result,power)
        n//=2
        if n: power=mul(power,power)
    assert result[0]**2-D*result[1]**2==1
    return result

def extended_gcd(a,b):
    r0,r1,s0,s1 = a,b,1,0
    while r1:
        q=r0//r1
        r0,r1,s0,s1 = r1,r0-q*r1,s1,s0-q*s1
    return r0,s0

def fixture(b,C,w,m,k):
    assert w>=max(b,C)
    alpha,aux = quadratic_power(w+1,w)
    assert aux%w==0
    g=aux//w
    x,y=quadratic_power(alpha,C)
    u,v=quadratic_power(alpha,2*C*y*m)
    assert v%(y*y)==0
    gcd,inv=extended_gcd(u,4*y)
    assert gcd==1
    qa0=((1-alpha)*inv)%(4*y)
    beta0=alpha+u*qa0
    beta=beta0+4*y*u*k
    s,t=quadratic_power(beta,C)
    M=2*b*alpha-b*b-1
    o=b**(C-1)
    numerators=(beta-1,v,s-x,t-C,x-y*(alpha-b)-b*o)
    divisors=(4*y,y*y,u,4*y,M)
    assert all(n%d==0 for n,d in zip(numerators,divisors))
    qb,qv,qs,qt,qr=(n//d for n,d in zip(numerators,divisors))
    values=dict(o=o,g=g,q_b=qb,q_v=qv,J=M-b*o,q_alpha=qa0+4*y*k,
        d_wb_plus=w-b+1,d_wC_plus=w-C+1,d_yC_plus=y-C+1,
        q_sigma_plus=qs+1,q_tau_plus=qt+1,q_r_plus=qr+1)
    assert all(z>0 for z in values.values())
    return values,dict(alpha=alpha,u=u,x=x,s=s),dict(beta0=beta0,qa0=qa0,y=y)

def compiler(T,accepted,L,R,j,r,s):
    K=T+1
    N=K*K
    delta=math.factorial(N-1)
    V1,V2,R0=0*j,0*j,0*j+1
    nodes=[]
    for i in range(1,N+1):
        den=math.prod(i-h for h in range(1,N+1) if h!=i)
        assert delta%den==0
        basis=0*j+delta//den
        for h in range(1,N+1):
            if h!=i: basis=basis*(j-h)
        a,b=1+(i-1)//K,1+(i-1)%K
        V1=V1+a*basis
        V2=V2+b*basis
        R0=R0*(j-i)
        nodes.append((a,b))
    H=0*j+1
    for i in sorted(accepted): H=H*(j-i)
    return [R0,(delta*L-V1)*(V1-delta*K),delta*(L-r+1)-V1,
            (delta*R-V2)*(V2-delta*K),delta*(R-s+1)-V2,H], (delta,V1,V2,nodes)

def dump(out,name,data):
    p=out/name
    text=json.dumps(data,sort_keys=True,separators=(',',':'))+'\n'
    if name.endswith('.gz'):
        with p.open('wb') as f:
            with gzip.GzipFile(filename='',mode='wb',fileobj=f,mtime=0) as z:
                z.write(text.encode())
    else: p.write_text(text)
    return dict(file=name,sha256=digest(p),bytes=p.stat().st_size)

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--source',required=True,type=Path)
    ap.add_argument('--out',required=True,type=Path)
    args=ap.parse_args()
    src,out=args.source.resolve(),args.out.resolve()
    assert src!=out and src not in out.parents, 'Never write in source tree'
    out.mkdir(parents=True,exist_ok=True)
    before=snapshot(src)
    result={'scope':'Independent exact algebra; pinned mathematical dependency; no upstream execution',
            'checker_sha256':digest(Path(__file__))}
    assert digest(src/'PROOF.md')==PROOF_HASH
    assert digest(src/'MANIFEST.sha256')==MANIFEST_HASH
    lines=(src/'MANIFEST.sha256').read_text().splitlines()
    for line in lines:
        expected,name=line.split('  ',1)
        assert digest(src/name)==expected,(name,'manifest')
    pins=json.loads((src/'SOURCE_PINS.json').read_text())
    for pin in pins:
        p=src/pin['file']
        assert digest(p)==pin['sha256'] and p.stat().st_size==pin['bytes']
    result['manifest_entries']=len(lines)
    result['dependency_pins']=len(pins)
    result['artifacts']=[dump(out,'source.before.json',before)]

    ring=Ring(('C','B','b','u')+LEAVES)
    C=ring.var('C')
    leaves={n:ring.var(n) for n in LEAVES}
    expansions={}
    choices=[('fixed_base_two',ring.const(2)),('variable_base_B_plus_one',ring.var('B')+1),
             ('independent_base_b',ring.var('b')),('fixed_base_three',ring.const(3)),
             ('fixed_base_seven',ring.const(7))]
    for label,b in choices:
        h,a=expressions(b,C,leaves)
        p=sos(h)
        variable=label in ('variable_base_B_plus_one','independent_base_b')
        base_name='B' if label=='variable_base_B_plus_one' else 'b'
        mon=dict(q_alpha=4,d_yC_plus=8,q_v=4)
        mon.update({base_name:8} if variable else {'J':4})
        assert [z.degree() for z in h]==([8,12,12,1,8] if variable else [4,10,10,1,6])
        assert p.degree()==(24 if variable else 20) and p.coefficient(mon)==1
        assert p.names()==set(LEAVES)|{'C'}|({base_name} if variable else set())
        info=dict(degrees=[z.degree() for z in h],degree=p.degree(),
                  residual_terms=[len(z.terms) for z in h],sos_terms=len(p.terms),
                  positive_leaves_including_output=12,auxiliaries=11,residual_slots=5,
                  degree_certificate=mon,certificate_coefficient=1,all_variables_live=True)
        if label in ('fixed_base_two','variable_base_B_plus_one'):
            reference=json.loads((src/'evidence'/ (label+'.polynomial.json')).read_text())
            for independent,record in zip(h+[p],reference['residuals']+[reference['polynomial']]):
                converted={tuple(row['powers'].get(n,0) for n in ring.names):int(row['coefficient']) for row in record}
                assert independent.terms==converted,(label,'full coefficient equality')
            info['source_full_coefficient_comparison']=True
            result['artifacts'].append(dump(out,label+'.independent.json.gz',
                dict(variables=ring.names,residuals=[z.payload() for z in h],polynomial=p.payload())))
        if label=='independent_base_b':
            bi=ring.names.index('b')
            weighted=lambda z:max((sum(m)-m[bi] for m in z.terms),default=-1)
            assert [weighted(z) for z in h]==[4,10,10,1,6]
            assert weighted(p)==20
            target=dict(J=4,q_alpha=4,d_yC_plus=8,q_v=4)
            wanted=tuple(target.get(n,0) for n in ring.names)
            cert=[(m[bi],c) for m,c in p.terms.items()
                  if all(m[i]==wanted[i] for i in range(len(m)) if i!=bi)]
            assert cert==[(0,1)]
            info['fixed_base_coefficient_ring_degrees']=[weighted(z) for z in h]
            info['fixed_base_degree_witness_coefficient_independent_of_b']=True
        expansions[label]=info
        if label=='fixed_base_two': hfixed=h
        if label=='variable_base_B_plus_one': hvariable=h
        print('Expanded',label,info['degree'],info['sos_terms'],flush=True)
    result['expansions']=expansions

    # Exact predecessor identities over free base and free u, with shifted adapters.
    h,a=expressions(ring.var('b'),C,leaves)
    d,A,X,U,y,v,t,beta,qa,qs=[a[n] for n in ('d','A','X','U','y','v','t','beta','q_alpha','q_sigma')]
    u=ring.var('u')
    f=[X*X-d*d-(A*A-d*d)*y*y,d*d*(u*u-1)-(A*A-d*d)*v*v,
       (X+d*u*qs)**2-d*d*(1+(beta*beta-1)*t*t),U-d*u*qa,h[3],h[4]]
    identities=[h[0]-f[0],h[3]-f[4],h[4]-f[5],
        h[1]-qa*qa*f[1]-f[3]*(U+d*u*qa),
        h[2]-qa*qa*f[2]-f[3]*qs*(2*qa*X+(U+d*u*qa)*qs)]
    assert all(z==0 for z in identities)
    result['generic_elimination_identities']=len(identities)

    fixture_records=[]
    cases=[(2,1,2,1),(2,1,2,2),(2,1,3,1),(3,1,3,1),
           (4,1,4,1),(5,1,5,1),(7,1,7,1),(2,2,2,1),(2,2,2,2),
           (2,2,3,1),(3,2,3,1)]
    evaluations=0
    perturbations=0
    for b,c,w,m in cases:
        local_h,_=expressions(ring.const(b),C,leaves)
        for k in (1,2,7):
            vals,expected,meta=fixture(b,c,w,m,k)
            rec=restored(b,c,vals)
            assert rec==expected
            assignment=dict(vals,C=c,B=b-1)
            assert all(z.evaluate(assignment)==0 for z in local_h)
            assert all(z.evaluate(assignment)==0 for z in hvariable)
            evaluations+=2
            # Off-surface checks: changing each of the twelve leaves by +/-1.
            for n in LEAVES:
                for delta in (-1,1):
                    changed=dict(vals)
                    changed[n]+=delta
                    if changed[n]<=0: continue
                    assert expressions(b,c,changed)[0]!=[0]*5,(b,c,n,delta)
                    perturbations+=1
            fixture_records.append(dict(b=b,C=c,w=w,u_multiple=m,k=k,
                leaves={n:str(z) for n,z in vals.items()},reconstructed={n:str(z) for n,z in rec.items()},
                beta_start={n:str(z) for n,z in meta.items()}))
    result.update(complete_fixtures=len(fixture_records),expanded_residual_fixture_evaluations=evaluations,
                  complete_reconstruction_roundtrips=len(fixture_records),rejected_single_leaf_perturbations=perturbations)
    result['artifacts'].append(dump(out,'fixtures.independent.json.gz',fixture_records))

    # Infinite-family identity including the excluded endpoint, proved polynomially.
    kr=Ring(('k',))
    k=kr.var('k')
    fam=dict(o=1,g=3,q_b=4+577*k,q_v=34,J=61,q_alpha=4*k,
        d_wb_plus=1,d_wC_plus=2,d_yC_plus=1,q_sigma_plus=4*k+1,q_tau_plus=1,q_r_plus=1)
    fh,fa=expressions(2,1,fam)
    assert all(z==0 for z in fh)
    result['symbolic_family_identities']=5
    endpoint={n:(z.evaluate({'k':0}) if isinstance(z,Poly) else z) for n,z in fam.items()}
    assert expressions(2,1,endpoint)[0]==[0]*5 and endpoint['q_alpha']==0
    # The endpoint is a genuine old solution, so global tuple bijection fails.
    degenerate=dict(endpoint,q_v=2)
    assert expressions(2,1,degenerate)[0]==[0]*5
    assert math.isqrt(1+(17*17-1)*2*2)**2 != 1+(17*17-1)*2*2
    # Positive rationals alone are also insufficient: all five equations hold
    # but the recovered u is negative. Two leaves are deliberately nonintegral.
    rational=dict(endpoint,q_b=1,q_alpha=Fraction(12,577),
                  q_sigma_plus=1+Fraction(12,577))
    rh,ra=expressions(2,1,rational)
    assert rh==[0]*5 and all(z>0 for z in rational.values())
    assert ra['U']/(ra['d']*ra['q_alpha'])==-577
    negative=dict(fixture(2,1,2,1,1)[0])
    negative['q_alpha']=-negative['q_alpha']
    negative['q_sigma_plus']=1-(negative['q_sigma_plus']-1)
    nh,na=expressions(2,1,negative)
    assert nh==[0]*5
    assert Fraction(na['U'],na['d']*na['q_alpha'])==-577
    assert negative['q_alpha']<0 and negative['q_sigma_plus']<0
    result['domain_challenges']=dict(zero_quotient_endpoint_excluded=True,
        zero_quotient_degeneracy_can_destroy_integer_u_reconstruction=True,
        positive_rational_leaves_can_admit_negative_u=True,
        negative_quotient_and_sigma_admit_negative_u_if_domains_dropped=True)
    rational_cases=0
    for numerator in range(-80,81):
        for denominator in range(1,65):
            z=Fraction(numerator,denominator)
            if (z*z).denominator==1: assert z.denominator==1
            rational_cases+=1
    sign_cases=0
    for alpha in range(2,18):
        for qa in range(1,12):
            for mag in range(alpha,alpha+12):
                assert alpha-qa*mag<=0
                sign_cases+=1
    result['rational_square_supplemental_cases']=rational_cases
    result['negative_u_sign_supplemental_cases']=sign_cases
    # General symbolic norm multiplication proves the Pell induction invariant.
    ir=Ring(('z','x','y'))
    z,x,y=[ir.var(n) for n in ir.names]
    xp,yp=z*x+(z*z-1)*y,x+z*y
    assert xp*xp-(z*z-1)*yp*yp-(x*x-(z*z-1)*y*y)==0
    result['general_pell_norm_identity']=True

    # Full native compositions, with all thirty-two declared independent variables.
    names=('g1','g2','g3','L','R','j','r','s')+tuple('left_'+n for n in LEAVES)+tuple('right_'+n for n in LEAVES)
    cr=Ring(names)
    cv={n:cr.var(n) for n in names}
    ha,aa=expressions(cr.const(2),cv['L'],{n:cv['left_'+n] for n in LEAVES})
    hb,ab=expressions(cr.const(2),cv['R'],{n:cv['right_'+n] for n in LEAVES})
    D=cv['g1']+cv['g2']+cv['g3']
    gap=[(20*cv['g1']-D)*aa['o']-2*D,(20*cv['g3']-D)*ab['o']-2*D]
    comps=[]
    interpolation_checks=0
    native_checks=0
    tables=[(0,set()),(0,{1}),(1,set()),(1,{1,4}),(1,{1,2,3,4}),
            (2,{1,3,5,7,9}),(2,set(range(1,10))),(3,{9,10,11,12})]
    for T,accepted in tables:
        ch,ci=compiler(T,accepted,cv['L'],cv['R'],cv['j'],cv['r'],cv['s'])
        cp=sos(ch)
        allh=gap+ha+hb+ch
        total=sos(allh)
        assert len(allh)==18 and len(names)-3==29 and total.names()==set(names)
        assert total.degree()==max(20,cp.degree())
        assert cp.degree()<=(2 if T==0 else 4*(T+1)**2-4)
        certificate={'left_J':4,'left_q_alpha':4,'left_d_yC_plus':8,'left_q_v':4}
        assert total.coefficient(certificate)==1
        K=T+1
        delta,V1,V2,nodes=ci
        for i,(a,b) in enumerate(nodes,1):
            assert V1.evaluate({'j':i})==delta*a and V2.evaluate({'j':i})==delta*b
            for L in range(1,K+3):
                for R in range(1,K+3):
                    r,s=L-a+1,R-b+1
                    if min(r,s)<=0: continue
                    vals={'L':L,'R':R,'j':i,'r':r,'s':s}
                    good=all((h.evaluate(vals) if isinstance(h,Poly) else h)==0 for h in ch)
                    want=(a==min(L,K) and b==min(R,K) and i in accepted)
                    assert good==want
                    interpolation_checks+=1
        # Exact full positive fixtures for small shifted counters, including exponent one.
        for L,R in ((1,1),(1,2),(2,1),(2,2)):
            va,_,_=fixture(2,L,2,1,1)
            vb,_,_=fixture(2,R,2,1,2)
            p,q=2**(L-1),2**(R-1)
            gaps=dict(g1=q*(p+2),g3=p*(q+2),g2=18*p*q-2*p-2*q)
            i=(min(L,K)-1)*K+min(R,K)
            values=dict(gaps,L=L,R=R,j=i,r=L-min(L,K)+1,s=R-min(R,K)+1)
            values.update({'left_'+n:v for n,v in va.items()})
            values.update({'right_'+n:v for n,v in vb.items()})
            assert all(v>0 for v in values.values())
            zeros=all((h.evaluate(values) if isinstance(h,Poly) else h)==0 for h in allh)
            assert zeros==(i in accepted)
            native_checks+=1
        comps.append(dict(T=T,accepted=sorted(accepted),witnesses=29,inputs=3,all_variables=32,
            residual_slots=18,compiler_degree=cp.degree(),degree=total.degree(),terms=len(total.terms)))
        print('Composed',T,sorted(accepted),'degree',total.degree(),flush=True)
    result.update(compositions=comps,interpolation_clipping_fixtures=interpolation_checks,
                  complete_native_fixtures=native_checks)
    # Literal trace-slot arithmetic, including T=0 and exact-first-halt addition.
    ledgers=[]
    for T in (0,1,2,7):
        for E,Z in ((1,0),(3,1),(7,3)):
            slots={'selectors':T*E,'one_hot':T,'counter_updates':2*T,
                   'zero_guards':T*Z,'state_links':T+1}
            assert sum(slots.values())==T*(E+Z+4)+1
            witnesses=T*(E+2)+26
            residuals=sum(slots.values())+12
            assert residuals==T*(E+Z+4)+13
            ledgers.append(dict(T=T,E=E,Z=Z,witnesses=witnesses,residuals=residuals,
                exact_first_halt_residuals=residuals+(T>=1),degree=20,trace_slots=slots))
    result['trace_ledgers']=ledgers
    after=snapshot(src)
    assert before==after, 'Source bytes/modes/sizes/mtimes changed'
    result['artifacts'].append(dump(out,'source.after.json',after))
    result['source_preserved']=True
    result['source_tree_entries']=len(before)
    result['success']=True
    dump(out,'results.json',result)
    print(json.dumps(dict(success=True,expansions=len(expansions),fixtures=len(fixture_records),
        compositions=len(comps),source_preserved=True),sort_keys=True),flush=True)

if __name__=='__main__': main()
