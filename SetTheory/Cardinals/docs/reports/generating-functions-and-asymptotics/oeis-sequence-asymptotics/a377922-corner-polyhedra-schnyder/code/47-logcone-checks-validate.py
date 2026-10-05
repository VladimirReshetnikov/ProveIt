#!/usr/bin/env python3
"""Exact, standalone finite/algebraic certificates. No Python assert statements.

Dependency: SymPy 1.14.0. No network or input outside this directory is used.
An explicit CheckFailure stays active under python -O. See README.md for scope.
"""
from __future__ import annotations
import argparse
from collections import defaultdict
from fractions import Fraction
import json
from math import comb
from pathlib import Path
import re
import sys
import sympy as S
import verify_sleeve

class CheckFailure(Exception):
    pass

def require(condition, code, detail=''):
    if not bool(condition):
        raise CheckFailure(code + (': ' + detail if detail else ''))

def equal(actual, expected, code):
    if isinstance(actual, S.MatrixBase):
        require(actual.shape == expected.shape and all(S.cancel(x) == 0 for x in actual-expected), code)
    else:
        require(S.cancel(actual-expected) == 0, code, f'{actual} != {expected}')

def keys(value, expected, location):
    require(type(value) is dict, 'schema.type', location)
    require(set(value) == set(expected.split()), 'schema.keys', location)

def integer(value, location, lower=None, upper=None):
    require(type(value) is int, 'schema.integer', location)
    require(lower is None or value >= lower, 'schema.range', location)
    require(upper is None or value <= upper, 'schema.range', location)

def array(value, length, location):
    require(type(value) is list and len(value) == length, 'schema.length', location)

def rational(value, location):
    require(type(value) is str and re.fullmatch(r'-?(?:0|[1-9][0-9]*)(?:/[1-9][0-9]*)?', value) is not None,
            'schema.rational', location)
    f = Fraction(value)
    require(str(f) == value, 'schema.canonical_rational', location)
    return S.Rational(f.numerator, f.denominator)

def matrix_schema(value, location):
    array(value, 2, location)
    for row in value:
        array(row, 2, location)
        for item in row:
            rational(item, location)

def duplicate_reject(pairs):
    out = {}
    for k, v in pairs:
        require(k not in out, 'schema.duplicate', k)
        out[k] = v
    return out

def load_fixture(path):
    try:
        f = json.loads(path.read_text(), object_pairs_hook=duplicate_reject)
    except (json.JSONDecodeError, UnicodeError) as e:
        raise CheckFailure('schema.json: ' + str(e)) from e
    keys(f, 'schema_version models counting sequences scope sleeve', 'root')
    integer(f['schema_version'], 'schema_version')
    require(f['schema_version'] == 1, 'schema.version')
    keys(f['models'], 'corner schnyder', 'models')
    for name, m in f['models'].items():
        keys(m, 'gamma kernel Q drift corrector covariance phase_covariances rho cos_angle derivative_order moment_base moment_bound fourier_edges seeds', name)
        for k in ['gamma','rho','cos_angle','moment_base','moment_bound']:
            rational(m[k], name+'.'+k)
        for k in ['Q','drift','corrector','covariance']:
            matrix_schema(m[k], name+'.'+k)
        array(m['phase_covariances'], 2, name+'.phase_covariances')
        for matrix in m['phase_covariances']:
            matrix_schema(matrix, name+'.phase_covariances')
        integer(m['derivative_order'], name+'.derivative_order', 0, 20)
        array(m['kernel'], 2, name+'.kernel')
        for row in m['kernel']:
            array(row, 2, name+'.kernel')
            for entry in row:
                keys(entry, 'numerator denominator', name+'.kernel.entry')
                for part in entry.values():
                    require(type(part) is list and 1 <= len(part) <= 20, 'schema.polynomial', name)
                    seen = set()
                    for term in part:
                        array(term, 3, name+'.kernel.term')
                        require(rational(term[0],name) != 0, 'schema.zero_term', name)
                        integer(term[1],name,0,20); integer(term[2],name,0,20)
                        require(tuple(term[1:]) not in seen, 'schema.duplicate_monomial', name)
                        seen.add(tuple(term[1:]))
        array(m['fourier_edges'],3,name+'.fourier_edges')
        for e in m['fourier_edges']:
            array(e,4,name+'.fourier_edge')
            for a in e: integer(a,name+'.fourier_edge',-100,100)
            require(e[0] in (0,1) and e[1] in (0,1), 'schema.phase',name)
        array(m['seeds'],2,name+'.seeds')
        for seed in m['seeds']:
            keys(seed,'direction start end segments',name+'.seed')
            require(seed['direction'] in ('forward','dual'),'schema.direction',name)
            for k in ['start','end']: integer(seed[k],name+'.seed',0,1)
            array(seed['segments'],2 if name=='corner' else 3,name+'.seed.segments')
            for segment in seed['segments']:
                keys(segment,'repeat edges',name+'.seed.segment')
                array(segment['repeat'],2,name+'.seed.repeat')
                for a in segment['repeat']: integer(a,name+'.seed.repeat',-100,100)
                require(type(segment['edges']) is list and 1 <= len(segment['edges']) <= 4,'schema.seed_edges',name)
                for e in segment['edges']:
                    keys(e,'from to dx dy',name+'.seed.edge')
                    integer(e['from'],name,0,1);integer(e['to'],name,0,1)
                    for k in ['dx','dy']:
                        array(e[k],2,name)
                        for a in e[k]:integer(a,name,-100,100)
    c=f['counting']
    keys(c,'corner_endpoint_factor schnyder_endpoint_factor schnyder_aggregate_shift schnyder_se_shift corner_sandwich_shifts schnyder_positive_weights schnyder_positive_start a377921_weights a377921_positive_start a377921_window_divisor','counting')
    for k in ['corner_endpoint_factor','schnyder_endpoint_factor']:rational(c[k],k)
    for k in ['schnyder_aggregate_shift','schnyder_se_shift','schnyder_positive_start','a377921_positive_start','a377921_window_divisor']:integer(c[k],k,0,100)
    for k,n in [('corner_sandwich_shifts',2),('schnyder_positive_weights',3),('a377921_weights',4)]:
        array(c[k],n,k)
        for a in c[k]:integer(a,k,-10,10)
    keys(f['sequences'],'A377922 A377920 A377921','sequences')
    for k,n in [('A377922',32),('A377920',31),('A377921',16)]:
        array(f['sequences'][k],n,k)
        for a in f['sequences'][k]:integer(a,k,0)
    keys(f['scope'],'symbolic_all_H_seeds finite_corner_kernel_horizon finite_schnyder_kernel_horizon asymptotic_certified','scope')
    for k in ['symbolic_all_H_seeds','asymptotic_certified']:
        require(type(f['scope'][k]) is bool,'schema.boolean',k)
    for k in ['finite_corner_kernel_horizon','finite_schnyder_kernel_horizon']:
        integer(f['scope'][k],k,1,100)
    require(f['scope']=={'symbolic_all_H_seeds':True,'finite_corner_kernel_horizon':12,'finite_schnyder_kernel_horizon':12,'asymptotic_certified':False},'schema.scope')
    verify_sleeve.schema(f['sleeve'],keys,array,integer,require)
    return f

u,v=S.symbols('u v',positive=True)
H=S.symbols('H',integer=True,positive=True)
r=S.symbols('r',integer=True,nonnegative=True)

def rat(x):return S.Rational(x)
def mat(x):return S.Matrix([[rat(a) for a in row] for row in x])
def at(e):return S.cancel(e.subs({u:1,v:1}))
def DX(e,x):return x*S.diff(e,x)
def kernel_fixture(k):
    def polynomial(terms):return sum(rat(c)*u**a*v**b for c,a,b in terms)
    return S.Matrix([[polynomial(e['numerator'])/polynomial(e['denominator']) for e in row] for row in k])

def reconstruct_kernels():
    z=S.Rational(1,3); D=(1-z/u)*(1-z*v)
    P=S.Matrix([[z*v/D,1/(z*v)+z/(u*D)],[u/z+z*v/D,z/(u*D)]])/S.Rational(9,2)
    a,b=S.symbols('a b',positive=True)
    F=S.Matrix([[a**-2*b**2,a**-1*b**3],[a**-3*b,a**-2*b**2]])/(1-a**-2-b**2)
    J=S.Matrix([[0,a/b],[a/b,0]])
    F0=F.subs({a:2,b:S.Rational(1,2)})
    equal(F0,S.ones(2)/8,'normalization.schnyder.faces')
    equal(F0*S.ones(2,1),S.ones(2,1)/4,'normalization.schnyder.face_rows')
    A=J*(S.eye(2)-F).inv()
    G=S.Matrix(2,2,lambda c,d:S.cancel(A[c,d].subs({a:2*S.sqrt(u),b:S.sqrt(v)/2})*u**S.Rational(c-d,2)*v**S.Rational(d-c,2)/S.Rational(16,3)))
    B=3/(8*(8*u-2*u*v-v-2))
    equal(G,S.Matrix([[B,S.Rational(3,4)+v*B],[S.Rational(3,4)*u/v+u*B,u*v*B]]),'kernel.schnyder.coefficient_decomposition')
    return {'corner':P,'schnyder':G}

def algebra(f,kernels,summary):
    pi=S.Matrix([[S.Rational(1,2),S.Rational(1,2)]])
    for name,M in kernels.items():
        m=f['models'][name]
        equal(rat(m['gamma']),S.Rational(9,2) if name=='corner' else S.Rational(16,3),'normalization.'+name+'.gamma')
        equal(M,kernel_fixture(m['kernel']),'kernel.'+name)
        Q=M.applyfunc(at)
        equal(Q,mat(m['Q']),'normalization.'+name+'.Q')
        equal(Q*S.ones(2,1),S.ones(2,1),'normalization.'+name+'.row_sums')
        equal(pi*Q,pi,'normalization.'+name+'.stationarity')
        require(all(q>0 for q in Q),'normalization.'+name+'.primitive')
        D=[M.applyfunc(lambda e:at(DX(e,x))) for x in [u,v]]
        drift=S.Matrix.hstack(*(d*S.ones(2,1) for d in D))
        equal(drift,mat(m['drift']),'drift.'+name)
        equal(pi*drift,S.zeros(1,2),'drift.'+name+'.stationary_zero')
        h=(S.eye(2)-Q+S.ones(2,1)*pi).inv()*drift
        equal(h,mat(m['corrector']),'corrector.'+name)
        equal(pi*h,S.zeros(1,2),'corrector.'+name+'.mean_zero')
        equal(drift+Q*h-h,S.zeros(2),'corrector.'+name+'.poisson')
        phase=[]
        for c in range(2):
            C=S.zeros(2)
            for i in range(2):
                for j in range(2):
                    for d in range(2):
                        hi=h[d,i]-h[c,i];hj=h[d,j]-h[c,j]
                        C[i,j]+=at(DX(DX(M[c,d],[u,v][i]),[u,v][j]))+hi*D[j][c,d]+hj*D[i][c,d]+hi*hj*Q[c,d]
            C=C.applyfunc(S.cancel)
            equal(C,mat(m['phase_covariances'][c]),'phase_covariance.'+name+f'.{c}')
            phase.append(C)
        C=(phase[0]+phase[1])/2
        equal(C,mat(m['covariance']),'covariance.'+name)
        require(C[0,0]>0 and C.det()>0,'covariance.'+name+'.positive_definite')
        require(phase[0]!=phase[1],'phase_covariance.'+name+'.nonconstant')
        # Separate spectral construction: direct closed-form Perron root, not h.
        lam=S.cancel((S.trace(M)+S.sqrt((M[0,0]-M[1,1])**2+4*M[0,1]*M[1,0]))/2)
        equal(at(lam),1,'spectral.'+name+'.PF_normalization')
        for x in [u,v]:equal(at(DX(lam,x)),0,'spectral.'+name+'.zero_drift')
        Hess=S.Matrix(2,2,lambda i,j:at(DX(DX(S.log(lam),[u,v][i]),[u,v][j])))
        equal(Hess,C,'spectral.'+name+'.covariance_crosscheck')
        equal(C[0,1]/S.sqrt(C[0,0]*C[1,1]),rat(m['rho']),'correlation.'+name)
        equal(rat(m['cos_angle']),-rat(m['rho']),'angle.'+name+'.cosine')
        summary['models'][name]={'Q':str(Q),'conditional_drift':str(drift),'corrector':str(h),'covariance':str(C),'phase_covariances':[str(a) for a in phase],'physical_covariance':str(4*C),'rho':m['rho']}

def affine(coeff):return coeff[0]*H+coeff[1]
def nonnegative_all_H(expr,strict=False):
    p=S.Poly(S.expand(expr.subs(H,H+1)),H)
    return all(c>=0 for c in p.all_coeffs()) and (not strict or p.eval(0)>0)

def integral_all_H(expr):
    p=S.Poly(S.expand(expr),H)
    return p.degree() <= 1 and all(c.q==1 for c in p.all_coeffs())

def support(name,c,d,dx,dy):
    # A sufficient support witness, exact for all P edges used here; each G
    # witness is realized by SE followed by zero or one weighted face step.
    if not integral_all_H(dx) or not integral_all_H(dy):return False
    if name=='corner':
        if c==0 and d==1 and dx==0 and dy==-1:return True
        if c==1 and d==0 and dx==1 and dy==0:return True
        if c==0 and d==0:return nonnegative_all_H(-dx) and nonnegative_all_H(dy,True)
        if c==1 and d==1:return nonnegative_all_H(-dx,True) and nonnegative_all_H(dy)
        if c==0 and d==1:return nonnegative_all_H(-dx,True) and nonnegative_all_H(dy)
        if c==1 and d==0:return nonnegative_all_H(-dx) and nonnegative_all_H(dy,True)
    if name=='schnyder':
        X=2*dx+d-c;Y=2*dy-d+c;e=1-c
        if d==e and X==1 and Y==-1:return True
        loss=1-X;gain=Y+1
        offsets=(2,2) if e==d else ((1,3) if e==0 else (3,1))
        ell=(loss-offsets[0])/2; rr=(gain-offsets[1])/2
        return integral_all_H(ell) and integral_all_H(rr) and nonnegative_all_H(ell) and nonnegative_all_H(rr)
    return False

def support_and_seeds(f,summary):
    for name,m in f['models'].items():
        rows=[]
        for c,d,x,y in m['fourier_edges']:
            require(c==d and support(name,c,d,S.Integer(x),S.Integer(y)),'fourier.'+name+'.support')
            rows.append([x,y,-1])
        determinant=S.Matrix(rows).det()
        require(abs(determinant)==1,'fourier.'+name+'.unimodular')
        summary['models'][name]['fourier_determinant']=int(determinant)
        require([a['direction'] for a in m['seeds']]==['forward','dual'],'seed.'+name+'.directions')
        seedresults=[]
        for seed in m['seeds']:
            label='seed.'+name+'.'+seed['direction']
            require(seed['start']==(0 if seed['direction']=='forward' else 1),label+'.start_phase')
            x=y=S.Integer(0);phase=seed['start'];length=S.Integer(0)
            for segment in seed['segments']:
                count=affine(segment['repeat'])
                require(integral_all_H(count) and nonnegative_all_H(count,True),label+'.repeat')
                edges=segment['edges']; bx=sum(affine(e['dx']) for e in edges); by=sum(affine(e['dy']) for e in edges)
                startphase=phase;px=py=S.Integer(0)
                for e in edges:
                    require(e['from']==phase,label+'.phase_continuity')
                    dx=affine(e['dx']);dy=affine(e['dy'])
                    c,d=e['from'],e['to']
                    if seed['direction']=='dual': c,d,dx,dy=d,c,-dx,-dy
                    require(support(name,c,d,dx,dy),label+'.support')
                    px+=affine(e['dx']);py+=affine(e['dy']);phase=e['to']
                    # Every point after an edge in every repetition: affine in
                    # repetition index. Its extrema are at 0 and count-1.
                    for index in [S.Integer(0),count-1]:
                        require(nonnegative_all_H(S.expand(x+index*bx+px)) and nonnegative_all_H(S.expand(y+index*by+py)),label+'.quadrant')
                require(count==1 or phase==startphase,label+'.repeat_phase')
                x=S.expand(x+count*bx);y=S.expand(y+count*by);length+=count*len(edges)
            equal(x,H,label+'.endpoint_x');equal(y,H,label+'.endpoint_y')
            require(phase==seed['end'],label+'.endpoint_phase')
            seedresults.append({'direction':seed['direction'],'endpoint':'(H,H)','end_phase':phase,'length':str(S.expand(length)),'range':'every integer H >= 1'})
        summary['models'][name]['seeds']=seedresults

def exponential_and_angles(f,summary):
    for name,m in f['models'].items():
        R=rat(m['moment_base']); require(R>1,'moment.'+name+'.positive_parameter')
        if name=='corner':
            require(R<3,'moment.corner.geometric_convergence')
            bound=S.Rational(2,3)*R+S.Rational(4,27)*R/(1-R/3)**2
        else:
            require(R**2<2,'moment.schnyder.face_convergence')
            face=R**4/(8*(1-R**2/2))
            require(face<1,'moment.schnyder.aggregate_convergence')
            bound=S.Rational(3,4)*R**2/(1-face)
            summary['models'][name]['face_exponential_row_sum']=str(face)
        equal(bound,rat(m['moment_bound']),'moment.'+name+'.bound')
        summary['models'][name]['exponential_certificate']={'exp_t':str(R),'bound':str(S.cancel(bound)),'norm':'quotient l1 displacement' if name=='corner' else 'sum of elementary physical l1 lengths'}
        c=rat(m['cos_angle'])
        require(0<c<1 and (2*c).q>1,'angle.'+name+'.rational_noninteger_twice_cos')
        if name=='corner':
            require(c>S.Rational(1,2) and c*c<S.Rational(1,2),'angle.corner.exact_interval')
            order=4
        else:
            require(c*c<S.Rational(3,4) and 4*c-1>0 and (4*c-1)**2>5,'angle.schnyder.exact_interval')
            order=6
        require(m['derivative_order']==order,'angle.'+name+'.derivative_order')
        summary['models'][name]['alpha_interval']=f'{order} < alpha < {order+1}'
        summary['models'][name]['twice_cos_angle']=str(2*c)

# The two enumerators below do not use the rational transition matrices.
def original_corner(horizon):
    dp={(0,0):1};p=[0];b=[0]
    # Keep terminal y<=1 at every time <=horizon. A y-coordinate above
    # horizon+1-k cannot fall to 0 or 1 by any certified terminal time.
    for k in range(1,horizon+1):
        nd=defaultdict(int); cap=horizon+1-k
        for (x,y),w in dp.items():
            if y and y-1<=cap:nd[x+1,y-1]+=w
            for loss in range(x+1):
                for rise in range(cap-y+1):
                    if (loss+rise)%2:continue
                    if y%2==0 and rise==0:continue
                    if y%2==1 and loss==0:continue
                    nd[x-loss,y+rise]+=w
        dp=nd
        require(all(x>=2 and x%2==0 for (x,y),w in dp.items() if y==0),'enumeration.corner.axis_endpoints')
        p.append(sum(w for (x,y),w in dp.items() if y==0));b.append(dp.get((1,1),0))
    return p,b

def original_schnyder(horizon):
    max_se=horizon+2;dp={(0,2):1};sp={}
    for k in range(1,max_se+1):
        se=defaultdict(int);cap=max_se-k
        for (x,y),w in dp.items():
            if y>=1 and y-1<=cap:se[x+1,y-1]+=w
        if k>=2:sp[k-2]=se.get((2,0),0)
        closure=defaultdict(int,se)
        # Every face lowers x strictly; decreasing x is a topological order.
        for x in range(k,-1,-1):
            for y in range(cap+1):
                w=closure.get((x,y),0)
                if not w:continue
                for ell in range(x//2+1):
                    for rr in range((cap-y)//2+1):
                        weight=comb(ell+rr,rr)
                        possibilities=[(2*ell+2,2*rr+2), (2*ell+1,2*rr+3) if y%2==0 else (2*ell+3,2*rr+1)]
                        for loss,rise in possibilities:
                            if loss<=x and y+rise<=cap:closure[x-loss,y+rise]+=w*weight
        dp=closure
    return [sp[n] for n in range(horizon+1)]

def quotient_transitions(name,x,y,c,cap,coeff):
    if name=='corner':
        if c==0 and y>=1:yield (x,y-1,1),Fraction(2,3)
        if c==1:yield (x+1,y,0),Fraction(2,3)
        for i in range(x+1):
            for j in range(cap-y+1):
                if c==0:
                    if j>=1:yield (x-i,y+j,0),Fraction(2,27)*Fraction(1,3)**(i+j-1)
                    if i>=1:yield (x-i,y+j,1),Fraction(2,27)*Fraction(1,3)**(i+j-1)
                else:
                    if i>=1:yield (x-i,y+j,1),Fraction(2,27)*Fraction(1,3)**(i+j-1)
                    if j>=1:yield (x-i,y+j,0),Fraction(2,27)*Fraction(1,3)**(i+j-1)
    else:
        if c==0:yield (x,y,1),Fraction(3,4)
        elif y>=1:yield (x+1,y-1,0),Fraction(3,4)
        for i in range(x+1):
            for j in range(cap-y+1):
                if c==0:
                    if i>=1:yield (x-i,y+j,0),Fraction(3,64)*coeff[i-1,j]
                    if i>=1 and j>=1:yield (x-i,y+j,1),Fraction(3,64)*coeff[i-1,j-1]
                else:
                    yield (x-i,y+j,0),Fraction(3,64)*coeff[i,j]
                    if j>=1:yield (x-i,y+j,1),Fraction(3,64)*coeff[i,j-1]

def quotient_endpoint_probabilities(name,horizon):
    # Independent rational series recurrence for 1/(1-v/4-u^-1/4-u^-1*v/8).
    coeff={}
    for i in range(horizon+1):
        for j in range(horizon+1):
            coeff[i,j]=Fraction(i==0 and j==0)+Fraction(1,4)*(coeff.get((i-1,j),0)+coeff.get((i,j-1),0))+Fraction(1,8)*coeff.get((i-1,j-1),0)
    dp={(0,0,0):Fraction(1)};out=[Fraction(0)]
    for k in range(1,horizon+1):
        cap=horizon-k;nd=defaultdict(Fraction)
        for (x,y,c),w in dp.items():
            for state,prob in quotient_transitions(name,x,y,c,cap,coeff):
                if state[1]<=cap:nd[state]+=w*prob
        dp=nd;out.append(dp.get((0,0,1),Fraction(0)))
    return out

def counting(f,summary):
    c=f['counting'];p,b=original_corner(32)
    require(p[:32]==f['sequences']['A377922'],'sequence.A377922')
    sp=original_schnyder(30)
    require(c['schnyder_positive_start']==4,'count.schnyder.positive_start')
    weights=c['schnyder_positive_weights']
    # Exceptional sizes 0..3 are supplied by the source identity.
    av=[0,0,3,2]+[sum(weights[j]*sp[n-j] for j in range(3)) for n in range(4,31)]
    require(av==f['sequences']['A377920'],'sequence.A377920')
    require(weights==[1,2,1],'count.schnyder.positive_weights')
    require(c['corner_sandwich_shifts']==[-1,1],'count.corner.shifts')
    require(all(b[n-1]<=p[n]<=b[n+1] for n in range(1,32)),'count.corner.finite_sandwich')
    # Exact endpoint tilts: physical net (1,1) for P; (1,-1) for S.
    equal(rat(c['corner_endpoint_factor']),S.Rational(1,3)**S.Rational(1-1,2),'count.corner.endpoint_factor')
    equal(rat(c['schnyder_endpoint_factor']),S.Integer(2)**1*S.Rational(1,2)**-1,'count.schnyder.endpoint_factor')
    require(c['schnyder_aggregate_shift']==1 and c['schnyder_se_shift']==2,'count.schnyder.time_shift')
    for name in ['corner','schnyder']:
        horizon=f['scope']['finite_'+name+'_kernel_horizon'];probs=quotient_endpoint_probabilities(name,horizon)
        gamma=Fraction(f['models'][name]['gamma']); factor=Fraction(c[name+'_endpoint_factor'])
        for k in range(1,horizon+1):
            count=b[k] if name=='corner' else sp[k-c['schnyder_aggregate_shift']]
            require(probs[k]*gamma**k==factor*count,'count.'+name+'.kernel_endpoint',f'time {k}')
        summary['models'][name]['endpoint_probability_horizon']=horizon
    # Structural seed of corner injections: (1,1) --SE--> (2,0), and
    # (2i+2,0) --face(-2i-1,1)--> (1,1), for every integer i>=0.
    require(support('corner',1,0,S.Integer(1),S.Integer(0)),'count.corner.lower_injection_support')
    require(support('corner',0,1,-H,S.Integer(0)),'count.corner.upper_injection_support')
    # Reconstruct B using the full formal polynomial identity, including n=2,3.
    t=S.symbols('t');poly=(1+t)**3-1-3*t
    require(c['a377921_weights']==[1,3,3,1] and c['a377921_positive_start']==4,'count.A377921.convolution')
    bv=[]
    for n in range(len(av)):
        correction=int(S.expand(poly).coeff(t,n))
        value=av[n]-correction-sum(c['a377921_weights'][j]*bv[n-j] for j in range(1,4) if n>=j)
        require(value>=0,'count.A377921.nonnegative_reconstruction',f'n={n}')
        bv.append(value)
    require(bv[:16]==f['sequences']['A377921'],'sequence.A377921')
    divisor=c['a377921_window_divisor']
    require(divisor==sum(c['a377921_weights']),'count.A377921.window_divisor')
    for n in range(4,len(av)):
        require(bv[n]<=av[n] and max(bv[n-3:n+1])*divisor>=av[n],'count.A377921.finite_window',f'n={n}')
    # First-crossing functions are step functions. Test every breakpoint y
    # induced by either prefix, and by a_n/8, plus every open cell midpoint.
    limit=Fraction(max(av),divisor)
    breakpoints={Fraction(1),limit}
    for z in av+bv:
        if 1<=z<=limit:breakpoints.add(Fraction(z))
    for z in av:
        if 1<=Fraction(z,divisor)<=limit:breakpoints.add(Fraction(z,divisor))
    points=sorted(breakpoints)
    probes=sorted(set(points+[ (a+b)/2 for a,b in zip(points,points[1:]) ]))
    def first(seq,target):return next((n for n,x in enumerate(seq) if x>=target),None)
    for y in probes:
        na=first(av,y);nb=first(bv,y);na8=first(av,divisor*y)
        require(None not in (na,nb,na8) and na<=nb<=na8,'count.A377921.finite_inverse',str(y))
    sleeve=f['sleeve']
    for n in range(sleeve['comparison_start'],len(av)):
        require(av[n-sleeve['comparison_shift']]<=bv[n]<=av[n],'count.A377921.sleeve_sandwich',f'n={n}')
    summary['sleeve']['finite_comparison_indices']='8..30'
    summary['counts']={'A377922_posted_terms':32,'A377920_posted_terms':31,'A377921_recorded_terms':16,'A377921_reconstructed_terms':31,'A377921_window_indices':'4..30','A377921_inverse_probes':len(probes),'A377921_inverse_y_interval':['1',str(limit)],'corner_sandwich_indices':'1..31','corner_fixed_endpoint_counts':b,'schnyder_subfamily_counts':sp,'A377921_reconstructed':bv}

def run(fixture):
    f=load_fixture(fixture)
    summary={'status':'PASS','arithmetic':'exact integers and rationals; symbolic derivatives and identities','python_optimized':not __debug__,'sympy_version':S.__version__,'models':{},'not_certified':['FCLT','unrestricted or killed LLT','cone survival or fixed-endpoint asymptotics','non-D-finiteness without analytic hypotheses','all-n coefficient exponent for A377921 without the report surgery and analytic proofs','full multiplicative equivalents or amplitudes','current completeness of live OEIS entries']}
    summary['sleeve']=verify_sleeve.verify(f['sleeve'],require)
    kernels=reconstruct_kernels();algebra(f,kernels,summary);support_and_seeds(f,summary);exponential_and_angles(f,summary);counting(f,summary)
    return summary

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--fixtures',type=Path,default=Path(__file__).with_name('fixtures.json'))
    parser.add_argument('--json',type=Path)
    args=parser.parse_args()
    try:
        result=run(args.fixtures)
    except CheckFailure as e:
        print('CHECK FAILED '+str(e),file=sys.stderr);return 2
    if args.json:args.json.write_text(json.dumps(result,indent=2)+'\n')
    print('PASS exact kernels, normalization, drift, Poisson correctors, two covariance methods, phase covariances')
    print('PASS rational exponential certificates, unimodular Fourier witnesses, symbolic all-H forward/dual seeds')
    print('PASS endpoint factors/time shifts, 32 A377922 and 31 A377920 terms, 16 recorded A377921 terms')
    print('PASS sleeve colors/root/annulus/size and finite A377921 six-shift comparison')
    print('PASS finite A377921 positive convolution/window/inverse sandwich, exact angle/order inequalities')
    print('SCOPE analytic cone, FCLT, LLT and asymptotic implications are NOT finitely certified')
    print('MODE '+('python -O' if not __debug__ else 'ordinary Python')+'; SymPy '+S.__version__)
    return 0

if __name__=='__main__':sys.exit(main())
