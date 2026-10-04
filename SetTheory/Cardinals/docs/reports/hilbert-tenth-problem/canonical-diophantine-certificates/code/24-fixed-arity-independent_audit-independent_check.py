#!/usr/bin/env python3
"""Fresh audit implementation. Never imports or executes the submitted builder/DAG.

The submitted JSON is parsed as syntax and symbolically normalized over Z. An
independent declarative specification is compared against every polynomial
clause. Separate finite arithmetic checks run only the functions written here.
"""
from collections import Counter, defaultdict, deque
from itertools import product
from math import comb, gcd, isqrt
from pathlib import Path
import hashlib
import json
import random

HERE = Path(__file__).resolve().parent
SUBMITTED = Path('/workspace/shared/sandpile-fixed-arity-20261004')
RNG = random.Random(4102026)


class Poly:
    """Sparse formal integer polynomial, never a numeric DAG evaluator."""
    def __init__(self, terms):
        self.t = {m:c for m,c in terms.items() if c}
    @staticmethod
    def lift(x):
        return x if isinstance(x, Poly) else Poly({():int(x)})
    def __add__(self, other):
        d = self.t.copy()
        for m,c in Poly.lift(other).t.items(): d[m] = d.get(m,0)+c
        return Poly(d)
    __radd__ = __add__
    def __neg__(self): return Poly({m:-c for m,c in self.t.items()})
    def __sub__(self, other): return self + -Poly.lift(other)
    def __rsub__(self, other): return Poly.lift(other) + -self
    def __mul__(self, other):
        d = defaultdict(int)
        for m,c in self.t.items():
            for n,e in Poly.lift(other).t.items():
                d[tuple(sorted(m+n))] += c*e
        return Poly(d)
    __rmul__ = __mul__
    def __eq__(self, other): return self.t == Poly.lift(other).t
    def degree(self): return max(map(len,self.t),default=0)


def symbol(name): return Poly({(name,):1})


class Specification:
    """The theorem's declarative equations, independent of source gate order."""
    def __init__(self):
        self.variables = set()
        self.equations = {}
        self.macros = {}
        self.ports = {}
    def positive(self, name):
        assert name not in self.variables, name
        self.variables.add(name)
        return symbol('witness:'+name)
    def natural(self, name): return self.positive(name+'.Plus')-1
    def equation(self, name, left, right):
        assert name not in self.equations, name
        self.equations[name] = Poly.lift(left)-right
    def power(self, name, base, exponent):
        base,exponent = Poly.lift(base),Poly.lift(exponent)
        out = self.positive(name+'.out')
        names = ['w','A0','mod','g','x','y','u','v','s','t','B0','S','qb','qv']
        w,a,mod,g,x,y,u,v,s,t,beta,slack,qb,qv = [self.positive(name+'.'+n) for n in names]
        a,beta = a+1,beta+1
        dwb,dwk,dyk,aa,ab,sa,sb,ta,tb,ra,rb = [self.natural(name+'.'+n) for n in
            ['dwb','dwk','dyk','alpha1','alpha2','sigma1','sigma2','tau1','tau2','rho1','rho2']]
        k,m = exponent+1,base*out
        pairs = [
            (x*x,1+(a*a-1)*y*y),
            (u*u,1+(a*a-1)*v*v),
            (s*s,1+(beta*beta-1)*t*t),
            (beta,1+4*y*qb),
            (beta+u*aa,a+u*ab),
            (v,y*y*qv),
            (s+u*sa,x+u*sb),
            (t+4*y*ta,k+4*y*tb),
            (y,k+dyk),
            (w,base+dwb),
            (w,k+dwk),
            (mod,m+slack),
            (a*a,1+((w+1)*(w+1)-1)*w*g*w*g),
            (2*a*base,mod+base*base+1),
            (x+mod*ra,y*(a-base)+m+mod*rb),
        ]
        for i,(l,r) in enumerate(pairs,1): self.equation(name+'.eq'+str(i),l,r)
        self.macros[name] = dict(kind='power',base=base,exponent=exponent,out=out)
        return out
    def geom(self, name, base, n):
        power = self.power(name+'.power',base,n)
        value = self.natural(name+'.value')
        self.equation(name+'.geometric',(base-1)*value+1,power)
        return value
    def subset(self, name, mask, value):
        L = self.power(name+'.L',2,mask+1)
        Y = self.power(name+'.Y',L,value)
        Z = self.power(name+'.Z',L+1,mask)
        q,o,r = [self.natural(name+'.'+n) for n in ['q','o','r']]
        sc,sr = [self.positive(name+'.'+n) for n in ['sc','sr']]
        self.equation(name+'.extract',Z,(q*L+2*o+1)*Y+r)
        self.equation(name+'.digit_bound',2*o+1+sc,L)
        self.equation(name+'.remainder_bound',r+sr,Y)
        self.macros[name] = dict(kind='subset',mask=mask,value=value)
    def intersect(self,name,x,y):
        z,a,c = [self.natural(name+'.'+n) for n in ['z','a','c']]
        self.equation(name+'.left_partition',x,z+a)
        self.equation(name+'.right_partition',y,z+c)
        self.subset(name+'.left',x,z)
        self.subset(name+'.right',y,z)
        self.subset(name+'.disjoint',a+c,a)
        self.macros[name] = dict(kind='and',left=x,right=y,out=z)
        return z
    def spread(self,name,value,base,n,stride):
        gap,slack = self.natural(name+'.stride_gap'),self.positive(name+'.range_slack')
        self.equation(name+'.stride_bound',stride,n+1+gap)
        P = self.power(name+'.range_power',base,n)
        self.equation(name+'.range_bound',value+slack,P)
        C = self.power(name+'.copy_base',base,stride-1)
        E = self.power(name+'.copy_power',C,n)
        G1,G2 = self.natural(name+'.copy_geometric'),self.natural(name+'.mask_geometric')
        self.equation(name+'.copy_geometric_eq',(C-1)*G1+1,E)
        self.equation(name+'.mask_geometric_eq',(base*C-1)*G2+1,E*P)
        out = self.intersect(name+'.select',value*G1,(base-1)*G2)
        self.macros[name] = dict(kind='spread',value=value,base=base,length=n,stride=stride,out=out)
        return out
    def stable_digits(self,name,mask,stream=None):
        a,c,d = [self.natural(name+'.bit'+str(i)) for i in range(3)]
        for suffix,value in [('allow0',a),('allow1',c),('allow2',d),('exclude67',c+d)]:
            self.subset(name+'.'+suffix,mask,value)
        out = a+2*c+4*d
        if stream is not None: self.equation(name+'.reconstruct',stream,out)
        return out
    def construct(self):
        p,q,r,d,e,f = [self.positive('input.'+n) for n in ['p','q','r','d','e','f']]
        tile,patch = self.natural('input.tile'),self.natural('input.patch')
        fields = [p-1,q-1,r-1,tile,d-1,e-1,f-1,patch]
        tail = fields[-1]
        for i in reversed(range(7)):
            code = symbol('input:InputPlus')-1 if i==0 else self.natural('input.pair'+str(i))
            self.equation('input.cantor'+str(i),2*code,(fields[i]+tail)*(fields[i]+tail+1)+2*tail)
            tail=code
        tx,ty,tz = [self.positive('box.t'+n)+1 for n in ['x','y','z']]
        ax,ay,az = p*d*tx,q*e*ty,r*f*tz
        A,B,C = 2*ax,2*ay,2*az
        tilemask = self.geom('tile.mask',32,p*q*r)
        self.stable_digits('tile.digits',tilemask,tile)
        patchmask = self.geom('patch.mask',32,d*e*f)
        self.subset('patch.digits',15*patchmask,patch)
        tr = self.power('tile.row_base',32,p)
        trv = self.spread('tile.rows',tile,tr,q*r,2*d*tx)
        tp = self.power('tile.plane_base',32,A*q)
        tpv = self.spread('tile.planes',trv,tp,r,2*e*ty)
        gx = self.geom('tile.repeatx',tr,2*d*tx)
        gy = self.geom('tile.repeaty',tp,2*e*ty)
        zr = self.power('tile.z_base',32,A*B*r)
        gz = self.geom('tile.repeatz',zr,2*f*tz)
        background = tpv*gx*gy*gz
        pr = self.power('patch.row_base',32,d)
        prv = self.spread('patch.rows',patch,pr,e*f,2*p*tx)
        pp = self.power('patch.plane_base',32,A*e)
        ppv = self.spread('patch.planes',prv,pp,f,2*q*ty)
        shift = self.power('patch.shift',32,ax+A*ay+A*B*az)
        additions = ppv*shift
        X = self.power('box.X',32,A)
        Y = self.power('box.Y',X,B)
        Z = self.power('box.Z',Y,C)
        J = self.natural('box.J')
        self.equation('box.J_eq',31*J+1,Z)
        Jx,Jy,Jz = [self.natural('box.J'+n) for n in ['x','y','z']]
        self.equation('box.Jx_eq',1024*(31*Jx+1),X)
        self.equation('box.Jy_eq',X*X*((X-1)*Jy+1),Y)
        self.equation('box.Jz_eq',Y*Y*((Y-1)*Jz+1),Z)
        interior = 32*X*Y*Jx*Jy*Jz
        U = self.natural('odometer.U')
        self.subset('odometer.binary_interior',interior,U)
        Ux,Uy,Uz = [self.natural('odometer.U'+n) for n in ['x','y','z']]
        for suffix,radix,quotient in [('x',32,Ux),('y',X,Uy),('z',Y,Uz)]:
            self.equation('odometer.div'+suffix,radix*quotient,U)
        F = self.stable_digits('endpoint',J)
        self.equation('sandpile.balance',background+additions+32*U+X*U+Y*U+Ux+Uy+Uz,6*U+F)
        self.ports = dict(p=p,q=q,r=r,d=d,e=e,f=f,tile=tile,patch=patch,A=A,B=B,C=C,
            background=background,additions=additions,interior_mask=interior,odometer=U,endpoint=F)
        return self


def audit_inert_source():
    data = (SUBMITTED/'evidence/polynomial-dag.json').read_bytes()
    submitted = json.loads(data)
    spec = Specification().construct()
    assert submitted['domain'] == 'InputPlus and every witness are positive integers'
    assert len(submitted['witnesses']) == len(set(submitted['witnesses']))
    assert set(submitted['witnesses']) == spec.variables
    names = [e[2] for e in submitted['equalities']]
    assert len(names) == len(set(names))
    assert set(names) == set(spec.equations)
    count = len(names)
    # An SOS with m equations has exactly 2m residual/square and m-1 sum gates.
    body = len(submitted['gates'])-(3*count-1)
    polys = {'input:InputPlus':symbol('input:InputPlus')}
    polys.update({'witness:'+w:symbol('witness:'+w) for w in spec.variables})
    degrees = {k:1 for k in polys}
    operations = Counter()
    def polynomial(ref):
        if ref.startswith('constant:'): return Poly.lift(int(ref.split(':',1)[1]))
        return polys[ref]
    def degree(ref):
        if ref.startswith('constant:'): int(ref.split(':',1)[1]); return 0
        return degrees[ref]
    for i,(op,left,right) in enumerate(submitted['gates']):
        assert op in ['+','-','*']
        dl,dr = degree(left),degree(right) # detects dangling/forward refs
        degrees['gate:'+str(i)] = dl+dr if op=='*' else max(dl,dr)
        operations[op] += 1
        if i<body:
            l,r = polynomial(left),polynomial(right)
            polys['gate:'+str(i)] = l+r if op=='+' else l-r if op=='-' else l*r
    for left,right,name in submitted['equalities']:
        assert polynomial(left)-polynomial(right) == spec.equations[name], name
    assert set(submitted['ports']) == set(spec.ports)
    for name,ref in submitted['ports'].items(): assert polynomial(ref)==spec.ports[name],name
    assert len(submitted['macros'])==len(spec.macros)
    assert {m['name'] for m in submitted['macros']}==set(spec.macros)
    for macro in submitted['macros']:
        intended=spec.macros[macro['name']]
        assert set(macro)-{'name'}==set(intended)
        for k,value in intended.items():
            assert macro[k]==value if k=='kind' else polynomial(macro[k])==value,(macro['name'],k)
    square_refs=[]
    for i,(left,right,name) in enumerate(submitted['equalities']):
        residual,square=body+2*i,body+2*i+1
        assert submitted['gates'][residual]==['-',left,right]
        assert submitted['gates'][square]==['*','gate:'+str(residual),'gate:'+str(residual)]
        square_refs.append('gate:'+str(square))
    total=square_refs[0]
    for i,square in enumerate(square_refs[1:]):
        index=body+2*count+i
        assert submitted['gates'][index]==['+',total,square]
        total='gate:'+str(index)
    assert submitted['output']==total
    reached=set(); pending=[total]
    while pending:
        ref=pending.pop()
        if ref in reached: continue
        reached.add(ref)
        if ref.startswith('gate:'):
            _,l,r=submitted['gates'][int(ref[5:])]; pending.extend([l,r])
    assert all('gate:'+str(i) in reached for i in range(len(submitted['gates'])))
    assert all('witness:'+w in reached for w in spec.variables)
    assert 'input:InputPlus' in reached
    macro_counts=Counter(m['kind'] for m in submitted['macros'])
    # Independently derived closed ledgers, not copied from the submitted receipt.
    assert len(spec.variables)==92*26+22*5+4*3+4*4+2*3+5+4+4+8+6+3==2566
    assert len(spec.equations)==92*15+22*3+4*2+4*4+5+1+7+4+3+1==1491
    assert macro_counts=={'power':92,'subset':22,'and':4,'spread':4}
    max_degree=max(p.degree() for p in spec.equations.values())
    leading={name:[{'variables':list(m),'coefficient':c} for m,c in p.t.items() if len(m)==max_degree]
        for name,p in spec.equations.items() if p.degree()==max_degree}
    assert set(leading)=={'patch.shift.eq8','patch.shift.eq9','patch.shift.eq11'}
    assert all(len(terms)==1 and terms[0]['coefficient']==-4 for terms in leading.values())
    return dict(sha256=hashlib.sha256(data).hexdigest(),positive_witnesses=len(spec.variables),
        equations=len(spec.equations),formal_clause_matches=len(spec.equations),port_matches=len(spec.ports),
        macro_interface_matches=len(spec.macros),macro_counts=dict(macro_counts),
        arithmetic_gates=len(submitted['gates']),body_gates=body,sos_gates=3*count-1,
        operations=dict(operations),degree_upper_bound=degrees[total],dead_gates=0,dead_witnesses=0,
        all_gates_polynomial=True,actual_equation_max_degree=max_degree,
        highest_residual_homogeneous_parts=leading,exact_sos_degree=2*max_degree,
        exact_degree_reason='Nonzero real homogeneous squares cannot sum identically to zero',
        leading_sos_coefficient=48)


def subset(m,x): return x>=0 and m>=0 and (m & x)==x
def geometric(b,n): return (b**n-1)//(b-1)
def digits(value,b,n): return [(value//b**i)%b for i in range(n)]
def pack(values,b=32):
    acc=0
    for value in reversed(values): acc=acc*b+value
    return acc
def spread(value,b,n,s):
    assert b>=2 and b&(b-1)==0 and n>=1 and s>=n+1 and 0<=value<b**n
    return value*geometric(b**(s-1),n) & ((b-1)*geometric(b**s,n))


def check_masks():
    total=valid=0
    for m in range(64):
        L=2**(m+1); Z=(L+1)**m
        for x in range(72):
            Y=L**x; div,r=divmod(Z,Y); q,c=divmod(div,L)
            expected=comb(m,x) if x<=m else 0
            assert c==expected and bool(c%2)==subset(m,x)
            if c%2:
                o=(c-1)//2; sc=L-c; sr=Y-r
                assert Z==(q*L+2*o+1)*Y+r and 2*o+1+sc==L and r+sr==Y
                assert min(q,o,r)>=0 and min(sc,sr)>0
                valid+=1
            total+=1
    triples=0
    for x,y,z in product(range(48),repeat=3):
        a,c=x-z,y-z
        recognized=min(a,c)>=0 and subset(x,z) and subset(y,z) and subset(a+c,a)
        assert recognized == (z==(x&y))
        triples+=1
    digit_cases=0
    for n in range(1,4):
        J=geometric(32,n)
        for arr in product(range(8),repeat=n):
            a,c,d=[pack([(v>>bit)&1 for v in arr]) for bit in range(3)]
            accepted=subset(J,a) and subset(J,c) and subset(J,d) and subset(J,c+d)
            assert accepted==all(v<=5 for v in arr)
            assert a+2*c+4*d==pack(arr)
            digit_cases+=1
        for arr in product(range(32),repeat=n):
            assert subset(15*J,pack(arr)) == all(v<=15 for v in arr)
            digit_cases+=1
        assert not subset(J,32**n) and not subset(15*J,32**n)
    return dict(binomial_cases=total,valid_subset_witnesses=valid,and_triples=triples,digit_cases=digit_cases)


def check_spreads():
    count=0
    for b,n in product([2,4,8,32],range(1,5)):
        size=b**n
        vals=range(size) if size<=256 else sorted({0,size-1,*[RNG.randrange(size) for _ in range(254)]})
        for s in sorted({n+1,n+2,2*n+1}):
            for v in vals:
                expected=sum(d*b**(s*i) for i,d in enumerate(digits(v,b,n)))
                assert spread(v,b,n,s)==expected
                count+=1
    # Outside the certified stride contract, the identity genuinely can fail.
    assert (3*geometric(2,2)&geometric(4,2)) != 1+4
    return dict(spread_cases=count,invalid_stride_counterexample=True)


def check_geometry():
    boxes=sites=0
    for p,q,r,d,e,f in product([1,2],repeat=6):
        tx=max(2,(q*r+2*d)//(2*d),(e*f+2*p)//(2*p)); ty=2; tz=2
        ax,ay,az=p*d*tx,q*e*ty,r*f*tz
        A,B,C=2*ax,2*ay,2*az; N=A*B*C
        tile=[RNG.randrange(6) for _ in range(p*q*r)]
        delta=[RNG.randrange(16) for _ in range(d*e*f)]
        T,D=pack(tile),pack(delta)
        rt=spread(T,32**p,q*r,A//p)
        et=spread(rt,32**(A*q),r,B//q)
        rp=spread(D,32**d,e*f,A//d)
        ep=spread(rp,32**(A*e),f,B//e)
        H=et*geometric(32**p,A//p)*geometric(32**(A*q),B//q)*geometric(32**(A*B*r),C//r)
        addition=ep*32**(ax+A*ay+A*B*az)
        coords=list(product(range(C),range(B),range(A)))
        expected_h=[tile[x%p+p*(y%q)+p*q*(z%r)] for z,y,x in coords]
        expected_d=[delta[(x-ax)+d*(y-ay)+d*e*(z-az)]
            if ax<=x<ax+d and ay<=y<ay+e and az<=z<az+f else 0 for z,y,x in coords]
        assert H==pack(expected_h) and addition==pack(expected_d)
        X,Y,Z=32**A,32**(A*B),32**N
        Jx,Jy,Jz=geometric(32,A-2),geometric(X,B-2),geometric(Y,C-2)
        assert 1024*(31*Jx+1)==X and X*X*((X-1)*Jy+1)==Y and Y*Y*((Y-1)*Jz+1)==Z
        interior=[int(0<x<A-1 and 0<y<B-1 and 0<z<C-1) for z,y,x in coords]
        I=32*X*Y*Jx*Jy*Jz
        assert I==pack(interior)
        arr=[RNG.randrange(2)*v for v in interior]; U=pack(arr)
        assert subset(I,U) and U%Y==U%X==U%32==0 and Y*U<Z
        strides=[(1,0,0),(0,1,0),(0,0,1),(-1,0,0),(0,-1,0),(0,0,-1)]
        streams=[32*U,X*U,Y*U,U//32,U//X,U//Y]
        values=[]
        for (dx,dy,dz),stream in zip(strides,streams):
            want=[arr[(x-dx)+A*(y-dy)+A*B*(z-dz)]
                if 0<=x-dx<A and 0<=y-dy<B and 0<=z-dz<C else 0 for z,y,x in coords]
            assert stream==pack(want)
            values.append(want)
        F=[RNG.randrange(6) for _ in coords]
        left=[expected_h[i]+expected_d[i]+sum(v[i] for v in values) for i in range(N)]
        right=[6*arr[i]+F[i] for i in range(N)]
        assert max(left)<=26 and max(right)<=11
        assert H+addition+sum(streams)==pack(left) and 6*U+pack(F)==pack(right)
        assert (pack(left)==pack(right))==(left==right)
        assert all(arr[i]==0 for i,v in enumerate(interior) if not v)
        sites+=N; boxes+=1
    # Empty interior geometric factors, although actual complete boxes have sides >=4.
    degenerate=0
    for A,B,C in product(range(2,5),repeat=3):
        X,Y=32**A,32**(A*B)
        I=32*X*Y*geometric(32,A-2)*geometric(X,B-2)*geometric(Y,C-2)
        assert I==pack([int(0<x<A-1 and 0<y<B-1 and 0<z<C-1)
            for z,y,x in product(range(C),range(B),range(A))])
        degenerate+=1
    return dict(input_dimension_fixtures=boxes,total_box_sites=sites,empty_interior_fixtures=degenerate,
        two_input_reshapes_per_fixture=True,six_neighbor_shifts_per_fixture=True)


STEPS=[(1,0,0),(-1,0,0),(0,1,0),(0,-1,0),(0,0,1),(0,0,-1)]
def neighbors(v):
    return [tuple(v[i]+step[i] for i in range(3)) for step in STEPS]
def stabilize(configuration):
    heights=defaultdict(int,configuration); odo=defaultdict(int)
    waiting=deque(v for v,h in configuration.items() if h>=6)
    while waiting:
        v=waiting.popleft()
        if heights[v]<6: continue
        heights[v]-=6; odo[v]+=1
        if heights[v]>=6: waiting.append(v)
        for w in neighbors(v):
            heights[w]+=1
            if heights[w]==6: waiting.append(w)
        assert sum(odo.values())<100 # proved ample for this finite fixture family
    return dict(heights),dict(odo)


def check_least_action():
    points=[(0,0,0),(1,0,0),(2,0,0)]
    universe=set(points)
    for p in points: universe.update(neighbors(p))
    instances=certificates=overfiring=0
    for heights in product(range(14),repeat=3):
        eta=dict(zip(points,heights)); final,true=stabilize(eta)
        found=False
        for mask in product([0,1],repeat=3):
            u=dict(zip(points,mask))
            F={v:eta.get(v,0)-6*u.get(v,0)+sum(u.get(w,0) for w in neighbors(v)) for v in universe}
            if all(0<=h<=5 for h in F.values()):
                found=True; certificates+=1
                assert all(n<=u.get(v,0) for v,n in true.items())
                overfiring+=int(any(u.get(v,0)>true.get(v,0) for v in universe))
        binary=all(n<=1 for n in true.values())
        assert found==binary
        instances+=1
    assert overfiring>0
    return dict(exhaustive_three_site_inputs=instances,binary_supersolution_certificates=certificates,
        nongenuine_supersolutions=overfiring)


def pell(a,n):
    D=a*a-1
    def mul(p,q): return (p[0]*q[0]+D*p[1]*q[1],p[0]*q[1]+p[1]*q[0])
    acc=(1,0); base=(a,1)
    while n:
        if n&1: acc=mul(acc,base)
        n//=2
        if n: base=mul(base,base)
    return acc


def check_power_witnesses():
    cases=[]
    for b,e in [(2,0),(3,0),(4,0),(5,0),(6,0),(2,1),(3,1)]:
        k=e+1; out=b**e; m=b*out; w=max(b,k)
        a,ag=pell(w+1,w); assert ag%w==0; g=ag//w
        x,y=pell(a,k); u,v=pell(a,2*k*y)
        assert gcd(u,4*y)==1
        beta=a+u*(((1-a)*pow(u,-1,4*y))%(4*y))
        s,t=pell(beta,k); mod=2*a*b-b*b-1
        assert (beta-1)%(4*y)==0 and v%(y*y)==0
        qb,qv=(beta-1)//(4*y),v//(y*y)
        def congruence(l,r,M):
            assert (r-l)%M==0
            q=(r-l)//M
            return max(q,0),max(-q,0)
        aa,ab=congruence(beta,a,u); sa,sb=congruence(s,x,u)
        ta,tb=congruence(t,k,4*y); ra,rb=congruence(x,y*(a-b)+m,mod)
        dwb,dwk,dyk,S=w-b,w-k,y-k,mod-m
        checks=[x*x==1+(a*a-1)*y*y,u*u==1+(a*a-1)*v*v,s*s==1+(beta*beta-1)*t*t,
            beta==1+4*y*qb,beta+u*aa==a+u*ab,v==y*y*qv,s+u*sa==x+u*sb,
            t+4*y*ta==k+4*y*tb,y==k+dyk,w==b+dwb,w==k+dwk,mod==m+S,
            a*a==1+((w+1)*(w+1)-1)*(w*g)*(w*g),2*a*b==mod+b*b+1,
            x+mod*ra==y*(a-b)+m+mod*rb]
        positive=[out,w,a-1,mod,g,x,y,u,v,s,t,beta-1,S,qb,qv]
        natural=[dwb,dwk,dyk,aa,ab,sa,sb,ta,tb,ra,rb]
        assert len(positive)+len(natural)==26 and min(positive)>0 and min(natural)>=0
        assert all(checks) and a>w>=b
        cases.append(dict(base=b,exponent=e,equations_passed=len(checks),positive_variables=26,
            maximum_witness_bits=max(v.bit_length() for v in positive+natural)))
    return cases


def pair(a,b): return (a+b)*(a+b+1)//2+b
def unpair(n):
    diagonal=(isqrt(8*n+1)-1)//2; b=n-diagonal*(diagonal+1)//2
    return diagonal-b,b
def check_pairing():
    cases=[[0]*8]+[[RNG.randrange(6) for _ in range(8)] for _ in range(256)]
    for fields in cases:
        n=fields[-1]
        for a in reversed(fields[:-1]): n=pair(a,n)
        decoded=[]; tail=n
        for _ in range(7): a,tail=unpair(tail); decoded.append(a)
        decoded.append(tail)
        assert decoded==fields
    assert pair(0,0)+1==1
    return dict(roundtrip_cases=len(cases),minimal_InputPlus=1)


def main():
    fetch=json.loads((HERE/'pell-pinned-fetch.json').read_text())
    copied=(SUBMITTED/'sources/pell-source.lean').read_bytes()
    assert fetch['content'].encode()==copied
    blob=hashlib.sha1(b'blob '+str(len(copied)).encode()+b'\0'+copied).hexdigest()
    assert blob==fetch['sha']
    report=dict(status='PASS',method='Formal polynomial identity comparison and separately authored finite tests; no submitted executable or arithmetic schedule run',
        dag=audit_inert_source(),masks=check_masks(),spreads=check_spreads(),geometry=check_geometry(),
        least_action=check_least_action(),power_witnesses=check_power_witnesses(),pairing=check_pairing(),
        pell_source=dict(url=fetch['display_url'],git_blob_sha=blob,sha256=hashlib.sha256(copied).hexdigest(),
            pinned_fetch_matches_local=True,lean_executed=False),
        checker_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
    (HERE/'audit-receipt.json').write_text(json.dumps(report,sort_keys=True,indent=2)+'\n')
    print(json.dumps(report,sort_keys=True,indent=2))


if __name__=='__main__': main()
