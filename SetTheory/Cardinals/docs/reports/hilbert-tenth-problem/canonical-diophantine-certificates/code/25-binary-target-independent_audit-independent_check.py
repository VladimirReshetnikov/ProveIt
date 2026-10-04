#!/usr/bin/env python3
"""Independently authored symbolic/finite audit; submitted files are inert data.

No upstream script is imported or executed, and no submitted arithmetic schedule
is numerically evaluated. Sparse polynomial normalization below is formal only.
"""
from pathlib import Path
from collections import Counter, defaultdict, deque
from itertools import product
from math import comb, isqrt
import hashlib
import json
import random

HERE = Path(__file__).resolve().parent
SOURCE = Path('/workspace/shared/sandpile-target-firing-20261004')
EXPECTED = '352b6dd9add46ed3c1c8532c21e9725249b28b3afba23003e31330b2503e0504'
RNG = random.Random(202610040430)

class Polynomial:
    def __init__(self, terms):
        self.terms = {monomial: c for monomial,c in terms.items() if c}
    @staticmethod
    def cast(value):
        return value if isinstance(value, Polynomial) else Polynomial({(): int(value)})
    def __add__(self, value):
        result = dict(self.terms)
        for monomial,c in self.cast(value).terms.items():
            result[monomial] = result.get(monomial, 0)+c
        return Polynomial(result)
    __radd__ = __add__
    def __neg__(self): return Polynomial({m:-c for m,c in self.terms.items()})
    def __sub__(self, value): return self+-self.cast(value)
    def __rsub__(self, value): return self.cast(value)+-self
    def __mul__(self, value):
        result = defaultdict(int)
        for m,c in self.terms.items():
            for n,d in self.cast(value).terms.items(): result[tuple(sorted(m+n))] += c*d
        return Polynomial(result)
    __rmul__ = __mul__
    def __eq__(self, value): return self.terms == self.cast(value).terms
    def degree(self): return max((len(m) for m in self.terms), default=0)

def variable(name): return Polynomial({(name,):1})

class Intended:
    """Declarative mathematics, insensitive to submitted arithmetic gate order."""
    def __init__(self):
        self.variables, self.clauses, self.interfaces, self.ports = set(), {}, {}, {}
    def pos(self, name):
        assert name not in self.variables
        self.variables.add(name)
        return variable('witness:'+name)
    def nat(self,name): return self.pos(name+'.Plus')-1
    def eq(self,name,left,right):
        assert name not in self.clauses
        self.clauses[name] = Polynomial.cast(left)-right
    def power(self,name,b,n):
        b,n = Polynomial.cast(b), Polynomial.cast(n)
        out = self.pos(name+'.out')
        a,beta = self.pos(name+'.aMinus1')+1,self.pos(name+'.betaMinus1')+1
        w,M,g,x,y,u,v,s,t,qb,qv,strict = [self.pos(name+'.'+k) for k in
            ['w','modulus','g','x','y','u','v','s','t','qb','qv','strict']]
        db,dn,dy,a1,a2,s1,s2,t1,t2,r1,r2 = [self.nat(name+'.'+k) for k in
            ['dwb','dwk','dyk','alpha1','alpha2','sigma1','sigma2','tau1','tau2','rho1','rho2']]
        k,m = n+1,b*out
        constraints = [
            (x*x,1+(a*a-1)*y*y), (u*u,1+(a*a-1)*v*v),
            (s*s,1+(beta*beta-1)*t*t), (beta,1+4*y*qb),
            (beta+u*a1,a+u*a2), (v,y*y*qv),
            (s+u*s1,x+u*s2), (t+4*y*t1,k+4*y*t2),
            (y,k+dy), (w,b+db), (w,k+dn), (M,m+strict),
            (a*a,1+((w+1)*(w+1)-1)*w*w*g*g),
            (2*a*b,M+b*b+1), (x+M*r1,y*(a-b)+m+M*r2)]
        for i,(l,r) in enumerate(constraints,1): self.eq(name+'.eq'+str(i),l,r)
        self.interfaces[name] = dict(kind='power',base=b,exponent=n,out=out)
        return out
    def geometric(self,name,b,n):
        power = self.power(name+'.power',b,n)
        result = self.nat(name+'.value')
        self.eq(name+'.equation',(b-1)*result+1,power)
        return result
    def sub(self,name,mask,value):
        mask,value = Polynomial.cast(mask),Polynomial.cast(value)
        L = self.power(name+'.radix',2,mask+1)
        Y = self.power(name+'.slot',L,value)
        Z = self.power(name+'.binomial',L+1,mask)
        q,h,r = [self.nat(name+'.'+x) for x in ['quotient','half','remainder']]
        dc,dr = [self.pos(name+'.'+x) for x in ['digit_gap','remainder_gap']]
        self.eq(name+'.extract',Z,(q*L+2*h+1)*Y+r)
        self.eq(name+'.digit_bound',2*h+1+dc,L)
        self.eq(name+'.remainder_bound',r+dr,Y)
        self.interfaces[name] = dict(kind='subset',mask=mask,value=value)
    def bitand(self,name,x,y):
        z,a,c = [self.nat(name+'.'+k) for k in ['common','left_only','right_only']]
        self.eq(name+'.left_partition',x,z+a)
        self.eq(name+'.right_partition',y,z+c)
        self.sub(name+'.left',x,z)
        self.sub(name+'.right',y,z)
        self.sub(name+'.disjoint',a+c,a)
        self.interfaces[name] = dict(kind='and',left=x,right=y,out=z)
        return z
    def spread(self,name,u,b,n,s):
        gap,strict = self.nat(name+'.stride_gap'),self.pos(name+'.range_gap')
        self.eq(name+'.stride_bound',s,n+1+gap)
        bn = self.power(name+'.range',b,n)
        self.eq(name+'.range_bound',u+strict,bn)
        step = self.power(name+'.copybase',b,s-1)
        stepn = self.power(name+'.copylimit',step,n)
        copy,mask = self.nat(name+'.copy'),self.nat(name+'.mask')
        self.eq(name+'.copy_equation',(step-1)*copy+1,stepn)
        self.eq(name+'.mask_equation',(b*step-1)*mask+1,stepn*bn)
        out = self.bitand(name+'.select',u*copy,(b-1)*mask)
        self.interfaces[name] = dict(kind='spread',value=u,base=b,length=n,stride=s,out=out)
        return out
    def construct(self):
        p,q,r,d,e,f = [self.pos('descriptor.'+x) for x in ['p','q','r','d','e','f']]
        T,D = self.nat('descriptor.tile'),self.nat('descriptor.patch')
        zs = [self.nat('target.zeta'+x) for x in ['x','y','z']]
        fields = [p-1,q-1,r-1,T,d-1,e-1,f-1,D,*zs]
        tail = fields[-1]
        for j in reversed(range(10)):
            code = variable('input:InputPlus')-1 if j==0 else self.nat('descriptor.pair'+str(j))
            self.eq('descriptor.cantor'+str(j),2*code,(fields[j]+tail)*(fields[j]+tail+1)+2*tail)
            tail = code
        tx,ty,tz = [self.pos('box.t'+x)+1 for x in ['x','y','z']]
        hx,hy,hz = p*d*tx,q*e*ty,r*f*tz
        A,B,C = 2*hx,2*hy,2*hz
        tilemask = self.geometric('tile.mask',32,p*q*r)
        bits = [self.nat('tile.bit'+str(i)) for i in range(3)]
        for i in range(3): self.sub('tile.allow'+str(i),tilemask,bits[i])
        self.sub('tile.exclude67',tilemask,bits[1]+bits[2])
        self.eq('tile.reconstruct',T,bits[0]+2*bits[1]+4*bits[2])
        patchmask = self.geometric('patch.mask',32,d*e*f)
        self.sub('patch.digits',15*patchmask,D)
        tr = self.power('tile.row_radix',32,p)
        tile_rows = self.spread('tile.rows',T,tr,q*r,2*d*tx)
        tp = self.power('tile.plane_radix',32,A*q)
        tile_planes = self.spread('tile.planes',tile_rows,tp,r,2*e*ty)
        gx = self.geometric('tile.repeat_x',tr,2*d*tx)
        gy = self.geometric('tile.repeat_y',tp,2*e*ty)
        zr = self.power('tile.z_radix',32,A*B*r)
        gz = self.geometric('tile.repeat_z',zr,2*f*tz)
        H = tile_planes*gx*gy*gz
        pr = self.power('patch.row_radix',32,d)
        patch_rows = self.spread('patch.rows',D,pr,e*f,2*p*tx)
        pp = self.power('patch.plane_radix',32,A*e)
        patch_planes = self.spread('patch.planes',patch_rows,pp,f,2*q*ty)
        shift = self.power('patch.shift',32,hx+A*hy+A*B*hz)
        Delta = patch_planes*shift
        X = self.power('box.X',32,A)
        Y = self.power('box.Y',X,B)
        Q = self.power('box.Q',Y,C)
        jx,jy,jz = [self.nat('box.j'+x) for x in ['x','y','z']]
        self.eq('box.jx_equation',1024*(31*jx+1),X)
        self.eq('box.jy_equation',X*X*((X-1)*jy+1),Y)
        self.eq('box.jz_equation',Y*Y*((Y-1)*jz+1),Q)
        I = 32*X*Y*jx*jy*jz
        K = self.pos('time.layers')
        W = self.power('time.endshift',Q,K)
        R = self.nat('time.repetition')
        self.eq('time.repetition_equation',(Q-1)*R+1,W)
        pre,event,final = [self.nat('time.'+x) for x in ['pre','new','final']]
        self.sub('time.pre_mask',I*R,pre)
        self.sub('time.new_mask',I*R,event)
        self.sub('time.final_mask',I,final)
        self.eq('time.recurrence',Q*(pre+event),pre+W*final)
        nx,ny,nz = [self.nat('time.negative_'+x) for x in ['x','y','z']]
        for axis,radix,quotient in [('x',32,nx),('y',X,ny),('z',Y,nz)]:
            self.eq('time.div_'+axis,radix*quotient,pre)
        available = (H+Delta)*R+32*pre+X*pre+Y*pre+nx+ny+nz
        selected = self.bitand('legality.select',available,31*event)
        slackbits = [self.nat('legality.bit'+str(i)) for i in range(5)]
        for i in range(5): self.sub('legality.allow'+str(i),event,slackbits[i])
        self.sub('legality.exclude24_31',event,slackbits[3]+slackbits[4])
        slack = sum((2**i)*v for i,v in enumerate(slackbits))
        self.eq('legality.threshold',selected,6*event+slack)
        local = []
        for axis,z,half,full in zip(['x','y','z'],zs,[hx,hy,hz],[A,B,C]):
            h,sign,ell = [self.nat('target.'+axis+'.'+k) for k in ['halfcode','sign','local']]
            upper = self.pos('target.'+axis+'.uppergap')
            self.eq('target.'+axis+'.zigzag',z,2*h+sign)
            self.eq('target.'+axis+'.sign_binary',sign*(sign-1),0)
            self.eq('target.'+axis+'.translate',ell+2*sign*h+sign,half+h)
            self.eq('target.'+axis+'.bound',ell+upper,full)
            local.append(ell)
        point = self.power('target.point',32,local[0]+A*local[1]+A*B*local[2])
        self.sub('target.fired',final,point)
        self.ports = dict(p=p,q=q,r=r,d=d,e=e,f=f,tile=T,patch=D,A=A,B=B,C=C,
            X=X,Y=Y,Q=Q,half_x=hx,half_y=hy,half_z=hz,background=H,additions=Delta,
            interior_mask=I,layers=K,endshift=W,repetition=R,pre=pre,new=event,final=final,
            available=available,selected=selected,legality_slack=slack,target_point=point)
        for axis,z,ell in zip(['x','y','z'],zs,local):
            self.ports['zeta_'+axis]=z; self.ports['local_'+axis]=ell
        return self

def symbolic_audit():
    raw = (SOURCE/'evidence/polynomial-dag.json').read_bytes()
    assert hashlib.sha256(raw).hexdigest()==EXPECTED
    dag = json.loads(raw)
    intended = Intended().construct()
    assert dag['schema']=='fixed-positive-integer-polynomial-dag-v1'
    assert dag['input']=='InputPlus'
    assert dag['domain']=='InputPlus and every witness are positive integers'
    assert len(dag['witnesses'])==len(set(dag['witnesses']))
    assert set(dag['witnesses'])==intended.variables
    labels = [e[2] for e in dag['equalities']]
    assert len(labels)==len(set(labels)) and set(labels)==set(intended.clauses)
    m = len(labels)
    body = len(dag['gates'])-3*m+1
    assert dag['body_gate_count']==body
    polynomials = {'input:InputPlus':variable('input:InputPlus')}
    polynomials.update({'witness:'+w:variable('witness:'+w) for w in intended.variables})
    bounds = {ref:1 for ref in polynomials}
    def formal(ref):
        return Polynomial.cast(int(ref[9:])) if ref.startswith('constant:') else polynomials[ref]
    def bound(ref): return 0 if ref.startswith('constant:') and isinstance(int(ref[9:]),int) else bounds[ref]
    for i,g in enumerate(dag['gates']):
        op,l,r = g
        assert op in ['+','-','*']
        dl,dr = bound(l),bound(r)
        ref = 'gate:'+str(i)
        bounds[ref] = dl+dr if op=='*' else max(dl,dr)
        if i<body:
            pl,pr = formal(l),formal(r)
            polynomials[ref] = pl+pr if op=='+' else pl-pr if op=='-' else pl*pr
    for l,r,name in dag['equalities']:
        assert formal(l)-formal(r)==intended.clauses[name],name
    assert set(dag['ports'])==set(intended.ports)
    for name,ref in dag['ports'].items(): assert formal(ref)==intended.ports[name],name
    assert len(dag['macros'])==len(intended.interfaces)
    assert {x['name'] for x in dag['macros']}==set(intended.interfaces)
    for interface in dag['macros']:
        spec = intended.interfaces[interface['name']]
        assert set(interface)=={'name',*spec}
        for key,value in spec.items():
            assert interface[key]==value if key=='kind' else formal(interface[key])==value,(interface['name'],key)
    squares = []
    for i,(l,r,name) in enumerate(dag['equalities']):
        j = body+2*i
        assert dag['gates'][j]==['-',l,r]
        assert dag['gates'][j+1]==['*','gate:'+str(j),'gate:'+str(j)]
        squares.append('gate:'+str(j+1))
    total = squares[0]
    for i,square in enumerate(squares[1:]):
        j = body+2*m+i
        assert dag['gates'][j]==['+',total,square]
        total = 'gate:'+str(j)
    assert dag['output']==total
    seen,pending = set(),[total]
    while pending:
        ref = pending.pop()
        if ref in seen: continue
        seen.add(ref)
        if ref.startswith('gate:'): pending.extend(dag['gates'][int(ref[5:])][1:])
    assert all('gate:'+str(i) in seen for i in range(len(dag['gates'])))
    assert all('witness:'+w in seen for w in intended.variables)
    assert 'input:InputPlus' in seen
    degree = max(p.degree() for p in intended.clauses.values())
    top = {name:[{'monomial':list(m),'coefficient':c} for m,c in p.terms.items() if len(m)==degree]
        for name,p in intended.clauses.items() if p.degree()==degree}
    assert degree==9 and set(top)=={'patch.shift.eq8','patch.shift.eq9','patch.shift.eq11'}
    assert all(len(v)==1 and v[0]['coefficient']==-4 for v in top.values())
    # Independent accounting by families, not the author's receipt.
    assert len(intended.variables)==118*26+30*5+5*3+4*4+5+3+5+3+8+12+11+9+3==3308
    assert m==118*15+30*3+5*2+4*4+5+1+10+3+1+1+3+1+12==1923
    counts = Counter(x['kind'] for x in dag['macros'])
    assert counts=={'power':118,'subset':30,'and':5,'spread':4}
    return dict(dag_sha256=EXPECTED,positive_witnesses=len(intended.variables),equalities=m,
        exact_formal_clause_matches=m,macro_interface_matches=len(intended.interfaces),port_matches=len(intended.ports),
        macro_counts=dict(counts),body_gates=body,sos_gates=3*m-1,gates=len(dag['gates']),
        body_counts=dict(Counter(g[0] for g in dag['gates'][:body])),sos_counts=dict(Counter(g[0] for g in dag['gates'][body:])),
        full_counts=dict(Counter(g[0] for g in dag['gates'])),dead_gates=0,dead_witnesses=0,
        syntactic_degree_upper_bound=bounds[total],max_residual_degree=degree,highest_residual_parts=top,
        exact_polynomial_degree=18,leading_sos_coefficient=48)

def pack(values,b=32):
    result=0
    for x in reversed(values): result=result*b+x
    return result

def unpack(value,n,b=32):
    result=[]
    for _ in range(n): value,digit=divmod(value,b); result.append(digit)
    assert value==0
    return result

def sub(mask,value): return value>=0 and mask>=0 and value&mask==value

def geom(b,n): return (b**n-1)//(b-1)

def spread(u,b,n,s): return u*geom(b**(s-1),n) & ((b-1)*geom(b**s,n))

def macro_cases():
    binomial=constructions=ands=spreads=0
    for m in range(40):
        L=2**(m+1); Z=(L+1)**m
        for x in range(47):
            Y=L**x; quotient,remainder=divmod(Z,Y); q,c=divmod(quotient,L)
            expected=comb(m,x) if x<=m else 0
            assert c==expected and bool(c&1)==sub(m,x)
            if c&1:
                h=(c-1)//2; dc=L-c; dr=Y-remainder
                assert min(q,h,remainder)>=0 and min(dc,dr)>0
                assert Z==(q*L+2*h+1)*Y+remainder
                constructions+=1
            binomial+=1
    for x,y,z in product(range(32),repeat=3):
        a,c=x-z,y-z
        accepted=min(a,c)>=0 and sub(x,z) and sub(y,z) and sub(a+c,a)
        assert accepted==(z==x&y)
        ands+=1
    for b,n in product([2,4,16,32],range(1,5)):
        values=range(b**n) if b**n<=128 else {0,b**n-1,*[RNG.randrange(b**n) for _ in range(100)]}
        for s in [n+1,n+2,2*n+3]:
            for u in values:
                expected=sum(v*b**(s*i) for i,v in enumerate(unpack(u,n,b)))
                assert spread(u,b,n,s)==expected
                spreads+=1
    assert spread(3,2,2,2)!=1+4
    return dict(binomial_extractions=binomial,valid_subset_constructions=constructions,and_triples=ands,spreads=spreads,
        invalid_stride_rejected_by_contract=True)

def recurrence_cases():
    count=accepted=0
    for n,K in [(1,1),(1,2),(1,3),(2,1),(2,2),(2,3),(3,2)]:
        Q=32**n
        for bits in product([0,1],repeat=2*n*K+n):
            pre=[bits[t*n:(t+1)*n] for t in range(K)]
            event=[bits[n*K+t*n:n*K+(t+1)*n] for t in range(K)]
            final=bits[2*n*K:]
            P,E,V=pack(sum((list(x) for x in pre),[])),pack(sum((list(x) for x in event),[])),pack(final)
            numeric=Q*(P+E)==P+Q**K*V
            semantic=all(x==0 for x in pre[0]) and all(
                pre[t+1][v]==pre[t][v]+event[t][v] for t in range(K-1) for v in range(n)) and all(
                final[v]==pre[-1][v]+event[-1][v] for v in range(n))
            assert numeric==semantic
            if numeric:
                assert all(sum(event[t][v] for t in range(K))==final[v]<=1 for v in range(n))
                accepted+=1
            count+=1
    # K=1 is honest: no prior support, even if one tries a mutually-supporting pair.
    assert 32**2*(0+pack([1,1]))==0+32**2*pack([1,1])
    return dict(exhaustive_candidate_tableaux=count,accepted_tableaux=accepted)

def slack_cases():
    plane_cases=threshold_cases=0
    for active in product([0,1],repeat=2):
        E=pack(active)
        for digits in product(range(32),repeat=2):
            bitplanes=[pack([(d>>i)&1 for d in digits]) for i in range(5)]
            ok=all(sub(E,x) for x in bitplanes) and sub(E,bitplanes[3]+bitplanes[4])
            expected=all((a and d<=23) or (not a and d==0) for a,d in zip(active,digits))
            assert ok==expected
            if ok:
                L=sum(2**i*x for i,x in enumerate(bitplanes))
                assert L==pack(digits) and all(d+6*a<32 for a,d in zip(active,digits))
            plane_cases+=1
        for values in product(range(27),repeat=2):
            selected=pack(values)&(31*E)
            required=[v-6 if a else 0 for a,v in zip(active,values)]
            feasible=all(0<=d<=23 for d in required)
            legal=all(not a or v>=6 for a,v in zip(active,values))
            assert feasible==legal
            if feasible: assert selected==6*E+pack(required)
            threshold_cases+=1
    return dict(bitplane_cases=plane_cases,legality_threshold_cases=threshold_cases)

def geometry_cases():
    tensors=spatial_sites=temporal_sites=temporal_boxes=0
    for p,q,r,d,e,f in product([1,2],repeat=6):
        tx=max(2,(q*r+1+2*d-1)//(2*d),(e*f+1+2*p-1)//(2*p))
        ty=max(2,(r+1+2*e-1)//(2*e),(f+1+2*q-1)//(2*q)); tz=2
        hx,hy,hz=p*d*tx,q*e*ty,r*f*tz; A,B,C=2*hx,2*hy,2*hz; N=A*B*C
        td=[RNG.randrange(6) for _ in range(p*q*r)]
        dd=[RNG.randrange(16) for _ in range(d*e*f)]
        tr=spread(pack(td),32**p,q*r,A//p)
        tp=spread(tr,32**(A*q),r,B//q)
        H=tp*geom(32**p,A//p)*geom(32**(A*q),B//q)*geom(32**(A*B*r),C//r)
        dr=spread(pack(dd),32**d,e*f,A//d)
        dp=spread(dr,32**(A*e),f,B//e)
        Delta=dp*32**(hx+A*hy+A*B*hz)
        hs=[]; ds=[]
        for z,y,x in product(range(C),range(B),range(A)):
            hs.append(td[(x-hx)%p+p*((y-hy)%q)+p*q*((z-hz)%r)])
            ds.append(dd[(x-hx)+d*(y-hy)+d*e*(z-hz)] if hx<=x<hx+d and hy<=y<hy+e and hz<=z<hz+f else 0)
        assert H==pack(hs) and Delta==pack(ds)
        assert all(0<=h+v<=20 for h,v in zip(hs,ds))
        tensors+=1; spatial_sites+=N
    for A,B,C,K in product(range(2,6),range(2,6),range(2,6),range(1,5)):
        N=A*B*C; X=32**A; Y=32**(A*B); Q=32**N; R=geom(Q,K)
        I=32*X*Y*geom(32,A-2)*geom(X,B-2)*geom(Y,C-2)
        coords=list(product(range(C),range(B),range(A)))
        interior=[i for i,(z,y,x) in enumerate(coords) if 0<x<A-1 and 0<y<B-1 and 0<z<C-1]
        assert I==sum(32**i for i in interior)
        stages={i:RNG.randrange(K+1) for i in interior} # K means never
        pre=[[int(i in stages and stages[i]<t) for i in range(N)] for t in range(K)]
        event=[[int(i in stages and stages[i]==t) for i in range(N)] for t in range(K)]
        final=[int(i in stages and stages[i]<K) for i in range(N)]
        P,E,V=pack(sum(pre,[])),pack(sum(event,[])),pack(final)
        assert sub(I*R,P) and sub(I*R,E) and sub(I,V)
        assert Q*(P+E)==P+Q**K*V
        assert P%Y==0 and P%X==0 and P%32==0
        shifts=[32*P,X*P,Y*P,P//32,P//X,P//Y]
        deltas=[(0,0,-1),(0,-1,0),(-1,0,0),(0,0,1),(0,1,0),(1,0,0)]
        for stream,(dz,dy,dx) in zip(shifts,deltas):
            wanted=[]
            for t in range(K):
                for z,y,x in coords:
                    xx,yy,zz=x+dx,y+dy,z+dz
                    wanted.append(pre[t][xx+A*yy+A*B*zz] if 0<=xx<A and 0<=yy<B and 0<=zz<C else 0)
            assert stream==pack(wanted)
        heights=[RNG.randrange(21) for _ in range(N)]
        available=pack(heights)*R+sum(shifts)
        expected=[]
        for t in range(K):
            for z,y,x in coords:
                neighbors=0
                for dz,dy,dx in deltas:
                    xx,yy,zz=x+dx,y+dy,z+dz
                    if 0<=xx<A and 0<=yy<B and 0<=zz<C: neighbors+=pre[t][xx+A*yy+A*B*zz]
                expected.append(heights[x+A*y+A*B*z]+neighbors)
        assert max(expected)<=26 and available==pack(expected)
        temporal_boxes+=1; temporal_sites+=N*K
    # Each forbidden face really prevents a wrap or makes division exact.
    A=B=C=4; N=A*B*C; Q=32**N
    examples={
        'x_upper_wrap': (A-1,1,A),
        'y_upper_wrap': (A*(B-1),A,A*B),
        'z_upper_time_wrap': (A*B*(C-1),A*B,N),
        'x_lower_wrap': (A,-1,A-1),
        'y_lower_wrap': (A*B,-A,A*B-A),
        'z_lower_time_wrap': (N,-A*B,N-A*B)}
    I=sum(32**(x+A*y+A*B*z) for z,y,x in product(range(1,3),repeat=3))
    for label,(index,step,wrong) in examples.items():
        value=32**index
        shifted=value*32**step if step>=0 else value//32**(-step)
        assert shifted==32**wrong and not sub(I*(1+Q),value)
    return dict(physical_tensors=tensors,physical_tensor_sites=spatial_sites,temporal_boxes=temporal_boxes,
        exact_temporal_site_checks=temporal_sites,boundary_wrap_counterexamples=len(examples))

def binary_reachable(heights):
    # Three collinear active sites; zero exterior sites receive at most one chip
    # from this line and are never unstable, so their omission is exact.
    seen={0}; queue=deque([0])
    while queue:
        fired=queue.popleft()
        for i,h in enumerate(heights):
            neighbors=sum((fired>>j)&1 for j in range(3) if abs(i-j)==1)
            if not ((fired>>i)&1) and h+neighbors>=6:
                nxt=fired|1<<i
                if nxt not in seen: seen.add(nxt); queue.append(nxt)
    return seen

def adversarial_tableaux():
    candidates=target_comparisons=accepted=0
    A,B,C,K=5,3,3,3; N=A*B*C; X=32**A; Y=32**(A*B); Q=32**N
    R=geom(Q,K); sites=[x+A+A*B for x in [1,2,3]]
    templates=[]
    for stages in product(range(4),repeat=3):
        pre=[[int(stages[j]<t) for j in range(3)] for t in range(K)]
        event=[[int(stages[j]==t) for j in range(3)] for t in range(K)]
        P=sum(pre[t][j]*32**(sites[j]+N*t) for t in range(K) for j in range(3))
        E=sum(event[t][j]*32**(sites[j]+N*t) for t in range(K) for j in range(3))
        V=sum(int(stages[j]<K)*32**sites[j] for j in range(3))
        assert Q*(P+E)==P+Q**K*V
        neighbor_stream=32*P+X*P+Y*P+P//32+P//X+P//Y
        templates.append((stages,pre,event,E,V,neighbor_stream))
    for heights in product(range(14),repeat=3):
        H=sum(heights[j]*32**sites[j] for j in range(3))
        reachable=binary_reachable(heights); recognized=set()
        for stages,pre,event,E,V,neighbors in templates:
            selected=(H*R+neighbors)&(31*E)
            slacks=[]; direct=True
            for t in range(K):
                row=[]
                for j,h in enumerate(heights):
                    available=h+sum(pre[t][i] for i in range(3) if abs(i-j)==1)
                    row.append(available-6 if event[t][j] else 0)
                    if event[t][j] and available<6: direct=False
                slacks.append(row)
            packed_ok=all(0<=d<=23 for row in slacks for d in row)
            if packed_ok:
                L=sum(slacks[t][j]*32**(sites[j]+N*t) for t in range(K) for j in range(3))
                bitplanes=[sum(((slacks[t][j]>>k)&1)*32**(sites[j]+N*t) for t in range(K) for j in range(3)) for k in range(5)]
                packed_ok=selected==6*E+L and all(sub(E,b) for b in bitplanes) and sub(E,bitplanes[3]+bitplanes[4])
            assert packed_ok==direct
            if packed_ok:
                fired=sum(int(stages[j]<K)<<j for j in range(3))
                assert fired in reachable
                recognized.add(fired); accepted+=1
            candidates+=1
        assert recognized==reachable
        for target in range(3):
            assert any(mask>>target&1 for mask in recognized)==any(mask>>target&1 for mask in reachable)
            target_comparisons+=1
    assert binary_reachable((5,5,0))=={0}
    assert binary_reachable((12,4,0))=={0,1}
    # Full physical replay of the ordinary repeated-toppling separator.
    height={(0,0,0):12,(1,0,0):4}; sequence=[(0,0,0),(0,0,0),(1,0,0)]
    for v in sequence:
        assert height.get(v,0)>=6
        height[v]-=6
        for axis in range(3):
            for delta in [-1,1]:
                u=list(v); u[axis]+=delta; u=tuple(u)
                height[u]=height.get(u,0)+1
    # A target can be legally reached while global evolution never terminates:
    # all-5 periodic background plus a single extra chip has expanding fronts.
    infinite={(0,0,0):6}; fired=[]
    for step in range(8):
        v=(step,0,0)
        assert infinite.get(v,5)>=6
        infinite[v]=infinite.get(v,5)-6; fired.append(v)
        for axis in range(3):
            for delta in [-1,1]:
                u=list(v); u[axis]+=delta; u=tuple(u)
                infinite[u]=infinite.get(u,5)+1
    assert len(set(fired))==8
    return dict(height_triples=14**3,packed_layer_candidates=candidates,accepted_layer_candidates=accepted,
        target_existence_comparisons=target_comparisons,mutual_support_rejected=True,
        repeated_firing_separator=dict(tile=0,patch_dimensions=[2,1,1],patch_digits=[12,4],target=[1,0,0],legal_sequence=[[0,0,0],[0,0,0],[1,0,0]],binary_target_rejected=True),
        nonstabilizing_background_binary_prefix_length=8)

def target_and_input_cases():
    decoded=bounded=points=pairings=0
    for zeta in range(160):
        candidates=[(h,s) for h in range(81) for s in range(5) if zeta==2*h+s and s*(s-1)==0]
        assert candidates==[(zeta//2,zeta%2)]
        h,s=candidates[0]; coordinate=h-2*s*h-s
        expected=zeta//2 if zeta%2==0 else -(zeta+1)//2
        assert coordinate==expected; decoded+=1
        for half in range(2,17):
            ell=half+coordinate; gap=2*half-ell
            feasible=ell>=0 and gap>0
            assert feasible==(-half<=coordinate<half)
            if feasible: assert ell+2*s*h+s==half+h and ell+gap==2*half
            bounded+=1
    for A,B,C in product(range(2,7),repeat=3):
        indexset=set()
        for z,y,x in product(range(C),range(B),range(A)):
            index=x+A*y+A*B*z
            assert index not in indexset; indexset.add(index)
            point=32**index
            assert point.bit_count()==1
            fullmask=geom(32,A*B*C)
            assert sub(fullmask,point)
            points+=1
        assert indexset==set(range(A*B*C))
    def pair(a,b): return (a+b)*(a+b+1)//2+b
    def unpair(code):
        total=(isqrt(8*code+1)-1)//2
        right=code-total*(total+1)//2
        return total-right,right
    samples=[[0]*11]+[[RNG.randrange(20) for _ in range(11)] for _ in range(256)]
    for fields in samples:
        code=fields[-1]
        for x in reversed(fields[:-1]): code=pair(x,code)
        InputPlus=code+1; tail=InputPlus-1; restored=[]
        for _ in range(10):
            a,tail=unpair(tail); restored.append(a)
        restored.append(tail)
        assert restored==fields and InputPlus>=1
        pairings+=1
    assert pair(0,0)==0
    return dict(zigzag_unique_decodes=decoded,coordinate_bound_cases=bounded,unique_point_positions=points,
        eleven_field_cantor_round_trips=pairings,all_zero_shifted_input=1)

def main():
    result={'symbolic':symbolic_audit(), 'macros':macro_cases(), 'recurrence':recurrence_cases(),
        'slack':slack_cases(),'geometry':geometry_cases(),'adversarial':adversarial_tableaux(),
        'target_and_input':target_and_input_cases()}
    result['checker_sha256']=hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    result['source_pins']={name:hashlib.sha256((SOURCE/name).read_bytes()).hexdigest() for name in
        ['ARCHITECTURE.md','build_target_certificate.py','evidence/polynomial-dag.json']}
    out=json.dumps(result,sort_keys=True,indent=2)+'\n'
    (HERE/'audit-receipt.json').write_text(out)
    print(out,end='')

if __name__=='__main__': main()
