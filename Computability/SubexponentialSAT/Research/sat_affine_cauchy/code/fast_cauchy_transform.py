#!/usr/bin/env python3
"""Precision-safe Cauchy feature transforms over Z/(2**p).

Theorem prototype: classical product trees + monic multipoint evaluation,
with explicit guards for the repository's normalized rational Newton basis.
No claim that this changes the SAT exponent. Python integer multiplication
implements polynomial convolution via Kronecker substitution; it is not FFT
code, and timings include tree construction and guard bits.
"""
from __future__ import annotations
import argparse, json, math, random, time
from fractions import Fraction
from pathlib import Path


def v2(n: int) -> int:
    if not n:
        raise ValueError('valuation of zero')
    return (abs(n) & -abs(n)).bit_length() - 1


def batch_inverse(units, modulus):
    """One inverse of a product of units, then O(n) multiplies."""
    prefix=[1]
    for u in units:
        if not (u & 1): raise ValueError('nonunit in inverse batch')
        prefix.append(prefix[-1]*u % modulus)
    inverse=pow(prefix[-1],-1,modulus)
    ans=[0]*len(units)
    for j in range(len(units)-1,-1,-1):
        ans[j]=inverse*prefix[j] % modulus
        inverse=inverse*units[j] % modulus
    return ans


def trim(a):
    while len(a)>1 and a[-1]==0: a.pop()
    return a

class Poly:
    def __init__(self, p):
        self.p=p; self.mod=1<<p; self.mask=self.mod-1
        self.muls=0; self.packed_muls=0
    def add(self,a,b):
        c=[0]*max(len(a),len(b))
        for j in range(len(c)): c[j]=((a[j] if j<len(a) else 0)+(b[j] if j<len(b) else 0))&self.mask
        return trim(c)
    def mul(self,a,b,cap=None):
        self.muls+=1
        if cap is not None: a=a[:cap]; b=b[:cap]
        if not a or not b: return [0]
        n=len(a)+len(b)-1
        if len(a)*len(b)<=64:
            out=[0]*n
            for i,x in enumerate(a):
                for j,y in enumerate(b): out[i+j]+=x*y
            out=[x&self.mask for x in out]
        else:
            self.packed_muls+=1
            # Each convolution coefficient < min(len(a),len(b))*2**(2p).
            width=(2*self.p+min(len(a),len(b)).bit_length()+7)//8
            av=int.from_bytes(b''.join(int(x&self.mask).to_bytes(width,'little') for x in a),'little')
            bv=int.from_bytes(b''.join(int(x&self.mask).to_bytes(width,'little') for x in b),'little')
            packed=(av*bv).to_bytes(n*width,'little')
            out=[int.from_bytes(packed[i*width:(i+1)*width],'little')&self.mask for i in range(n)]
        if cap is not None: out=out[:cap]
        return trim(out or [0])
    def inv_series(self,a,n):
        if a[0]%2==0: raise ValueError('nonunit constant term')
        g=[pow(a[0],-1,self.mod)]
        while len(g)<n:
            m=min(2*len(g),n)
            ag=self.mul(a[:m],g,m)
            q=[(-x)&self.mask for x in ag]+[0]*(m-len(ag))
            q[0]=(q[0]+2)&self.mask
            g=self.mul(g,q,m); g += [0]*(m-len(g))
        return g[:n]
    def rem(self,a,b):
        a=trim(list(a)); b=trim(list(b))
        if len(a)<len(b): return a
        if b[-1]!=1: raise ValueError('divisor must be monic')
        if len(b)<=9:
            c=a[:]
            for i in range(len(c)-len(b),-1,-1):
                q=c[i+len(b)-1]
                for j,x in enumerate(b): c[i+j]=(c[i+j]-q*x)&self.mask
            return trim(c[:len(b)-1] or [0])
        qlen=len(a)-len(b)+1
        inv=self.inv_series(list(reversed(b))[:qlen],qlen)
        qr=self.mul(list(reversed(a))[:qlen],inv,qlen)
        qr += [0]*(qlen-len(qr))
        q=list(reversed(qr))
        qb=self.mul(q,b)
        return trim([((a[i] if i<len(a) else 0)-(qb[i] if i<len(qb) else 0))&self.mask for i in range(len(b)-1)] or [0])
    def product_tree(self,points):
        if len(points)==1: return ([-points[0]&self.mask,1],None,None)
        k=len(points)//2
        l=self.product_tree(points[:k]); r=self.product_tree(points[k:])
        return (self.mul(l[0],r[0]),l,r)
    def evaluate(self,poly,points):
        if not points: return []
        tr=self.product_tree(points)
        def descend(t,a):
            b=self.rem(a,t[0])
            if t[1] is None: return [b[0]]
            return descend(t[1],b)+descend(t[2],b)
        return descend(tr,poly)


def basis_tree(ring,nodes,T,weights=None):
    """C=sum_b w_b A_[0,b) B_(b,n); C=C_left B_right+A_left C_right."""
    if len(nodes)==1:
        return {'A':[-nodes[0]&ring.mask,1], 'B':[(T-nodes[0])&ring.mask,1],
                'C':[weights[0]&ring.mask] if weights is not None else None,
                'n':1,'left':None,'right':None}
    k=len(nodes)//2
    l=basis_tree(ring,nodes[:k],T,weights[:k] if weights is not None else None)
    r=basis_tree(ring,nodes[k:],T,weights[k:] if weights is not None else None)
    c=None if weights is None else ring.add(ring.mul(l['C'],r['B']),ring.mul(l['A'],r['C']))
    return {'A':ring.mul(l['A'],r['A']),'B':ring.mul(l['B'],r['B']),'C':c,
            'n':len(nodes),'left':l,'right':r}


def moments(ring,points,weights,n):
    """Coefficients of sum_j weights[j]/(1-points[j] z), no division by nodes."""
    def build(xs,ws):
        if len(xs)==1: return [ws[0]&ring.mask],[1,(-xs[0])&ring.mask]
        k=len(xs)//2
        nl,dl=build(xs[:k],ws[:k]); nr,dr=build(xs[k:],ws[k:])
        return ring.add(ring.mul(nl,dr,n),ring.mul(nr,dl,n)),ring.mul(dl,dr,n)
    if not points: return [0]*n
    num,den=build(points,weights)
    ans=ring.mul(num,ring.inv_series(den,n),n)
    return ans+[0]*(n-len(ans))


def transpose_basis(ring,tree,dual):
    """Transpose the division-free Newton conversion using correlations."""
    if tree['n']==1: return [dual[0]&ring.mask]
    l=tree['left']; r=tree['right']; n=tree['n']
    def correlate(poly,size):
        cv=ring.mul(list(reversed(dual)),poly)
        return [cv[n-1-j] if n-1-j<len(cv) else 0 for j in range(size)]
    return transpose_basis(ring,l,correlate(r['B'],l['n']))+transpose_basis(ring,r,correlate(l['A'],r['n']))


def slots(a,i):
    R=1<<i
    return [(j%R)+2*R*(j//R) for j in range(1<<(a-1))]


def exponents(B,i):
    R=1<<i
    return [2*(b//R)-(b//R).bit_count() for b in range(B)]


def guards(B,i,ports):
    es=exponents(B,i); H=es[-1] if es else 0
    # Sum min(i,v2(s_j-s_h)); count congruent indices at every level.
    ks=[]
    for j in ports:
        k=0
        for d in range(1,i+1):
            r=j% (1<<d)
            if r<B: k+=(B-1-r)//(1<<d)+1
        ks.append(k)
    return es,H,ks,max(ks,default=0)


def synthesize(coeffs,a,i,T,p,sign=1,ports=None,return_meta=False):
    """Return sum_b coeffs[b] F_b(sign*s_j) modulo 2**p."""
    ss=slots(a,i); B=len(coeffs)
    if not (0<B<=len(ss)) or v2(T)!=i: raise ValueError('invalid domain')
    if sign not in (-1,1): raise ValueError('bad sign')
    if ports is None: ports=list(range(len(ss)))
    es,H,ks,kmax=guards(B,i,ports)
    P=p+H+kmax
    ring=Poly(P)
    nd=[sign*x for x in ss[:B]]; xs=[sign*ss[j] for j in ports]
    weights=[(c*(1<<(H-es[b]))*T)&ring.mask for b,c in enumerate(coeffs)]
    tr=basis_tree(ring,nd,T,weights)
    nums=ring.evaluate(tr['C'],xs); dens=ring.evaluate(tr['B'],xs)
    mask=(1<<p)-1; out=[]
    inverses=batch_inverse([d>>k for d,k in zip(dens,ks)],1<<p)
    for n,inv,k in zip(nums,inverses,ks):
        if n% (1<<(H+k)): raise ArithmeticError('failed integrality guard')
        out.append(((n>>(H+k))*inv)&mask)
    meta={'working_precision':P,'guard':H+kmax,'poly_multiplications':ring.muls,'packed_multiplications':ring.packed_muls}
    return (out,meta) if return_meta else out


def analyze(values,a,i,T,p,sign=-1,ports=None,B=None,return_meta=False):
    """Return all source forms sum_j values[j] G_b(s_j) modulo 2**p.

    sign=-1 gives G; sign=1 is the transpose F transform. Denominator
    preparation gets an additional kmax guard before its unit divisions.
    """
    ss=slots(a,i)
    if ports is None: ports=list(range(len(ss)))
    if len(values)!=len(ports): raise ValueError('shape mismatch')
    if B is None: B=len(ss)
    if not (0<B<=len(ss)) or v2(T)!=i: raise ValueError('invalid domain')
    es,H,ks,kmax=guards(B,i,ports)
    P=p+H+kmax; Phigh=p+H+2*kmax
    high=Poly(Phigh); ring=Poly(P)
    nd=[sign*x for x in ss[:B]]; xs=[sign*ss[j] for j in ports]
    tr=basis_tree(high,nd,T)
    dens=high.evaluate(tr['B'],xs)
    weights=[]
    inverses=batch_inverse([(d>>k)&ring.mask for d,k in zip(dens,ks)],ring.mod)
    for value,inv,k in zip(values,inverses,ks):
        weights.append((value*(1<<(kmax-k))*inv)&ring.mask)
    def reduce_tree(t):
        t['A']=[x&ring.mask for x in t['A']]; t['B']=[x&ring.mask for x in t['B']]
        if t['left'] is not None: reduce_tree(t['left']); reduce_tree(t['right'])
    reduce_tree(tr)
    mom=moments(ring,xs,weights,B)
    dual=transpose_basis(ring,tr,mom)
    mask=(1<<p)-1; out=[]
    for b,z in enumerate(dual):
        n=(T*z)&ring.mask; shift=kmax+es[b]
        if n% (1<<shift): raise ArithmeticError('failed transpose integrality guard')
        out.append((n>>shift)&mask)
    meta={'working_precision':Phigh,'core_precision':P,'guard':H+2*kmax,
          'poly_multiplications':ring.muls+high.muls,'packed_multiplications':ring.packed_muls+high.packed_muls}
    return (out,meta) if return_meta else out


def odd_level_transform(values,a,T,p,sign=-1,transpose=True,return_meta=False):
    """One-convolution specialization for i=0 and all N ports/modes.

    Exact factorization into diagonal scalings and a Toeplitz matrix after
    clearing factorial powers of two. Core precision p+2*v2((N-1)!).
    """
    N=1<<(a-1)
    if len(values)!=N or not T&1 or sign not in (-1,1): raise ValueError('invalid odd-level input')
    f=[j-j.bit_count() for j in range(N)]; K=f[-1]
    P=p+2*K; ring=Poly(P)
    odd=[1]*N; D=[0]*N; d=1
    for j in range(N):
        if j: odd[j]=odd[j-1]*(j>>v2(j))&ring.mask
        d=d*(T+2*sign*j)&ring.mask; D[j]=d
    inv=batch_inverse(D+odd,ring.mod)
    u=[odd[j]*inv[j]&ring.mask for j in range(N)]
    v=[(D[j-1] if j else 1)*inv[N+j]&ring.mask for j in range(N)]
    kernel=[(v[j]<<(K-f[j]))&ring.mask for j in range(N)]
    mask=(1<<p)-1; out=[]
    if transpose:
        av=[(values[j]*u[j]<<f[j])&ring.mask for j in range(N)]
        cv=ring.mul(list(reversed(av)),kernel)
        for b in range(N):
            z=cv[N-1-b]*T*(sign if b%2 else 1)&ring.mask
            shift=K+f[b]
            if z%(1<<shift): raise ArithmeticError('odd transpose divisibility')
            out.append((z>>shift)&mask)
    else:
        cvect=[(values[b]*T*(sign if b%2 else 1)<<(K-f[b]))&ring.mask for b in range(N)]
        cv=ring.mul(cvect,kernel,N); cv += [0]*(N-len(cv))
        for j in range(N):
            z=cv[j]*u[j]&ring.mask; shift=2*K-f[j]
            if z%(1<<shift): raise ArithmeticError('odd synthesis divisibility')
            out.append((z>>shift)&mask)
    meta={'working_precision':P,'guard':2*K,'poly_multiplications':ring.muls,'packed_multiplications':ring.packed_muls}
    return (out,meta) if return_meta else out


def dense_fraction(a,i,T,B=None,sign=1,ports=None):
    ss=slots(a,i)
    if B is None: B=len(ss)
    if ports is None: ports=list(range(len(ss)))
    es=exponents(B,i); out=[]
    for j in ports:
        row=[]; prefix=Fraction(1)
        for b in range(B):
            d=sign*(ss[j]-ss[b])
            row.append(prefix*Fraction(T,T+d)/(1<<es[b]))
            prefix*=Fraction(d,T+d)
        out.append(row)
    return out


def residue(x,p):
    if x.denominator%2==0: raise ArithmeticError('nonintegral oracle feature')
    return x.numerator*pow(x.denominator,-1,1<<p)% (1<<p)


def dense_apply(values,a,i,T,p,sign=-1,ports=None,B=None,transpose=True):
    """Quadratic streamed recurrence, valuations exact and unit arithmetic mod 2**p.

    One batch inversion prepares denominators; no dense output is stored.
    Prefix units update using fused numerator/denominator ratios.
    """
    ss=slots(a,i); N=len(ss)
    if ports is None: ports=list(range(N))
    if B is None: B=N
    es=exponents(B,i); mod=1<<p; mask=mod-1
    # Every actual difference belongs to [-2**a+1, 2**a-1].
    ds=list(range(-(1<<a)+1,1<<a))
    ds=[d for d in ds if T+d]
    units=[(T+d)>>v2(T+d) for d in ds]
    prefixes=[1]
    for u in units: prefixes.append(prefixes[-1]*u&mask)
    inv=pow(prefixes[-1],-1,mod); inverses=[0]*len(ds)
    for j in range(len(ds)-1,-1,-1):
        inverses[j]=inv*prefixes[j]&mask
        inv=inv*units[j]&mask
    den={d:(v2(T+d),u) for d,u in zip(ds,inverses)}
    ratio={d:(((d>>v2(d))*den[d][1])&mask) for d in ds if d}
    tunit=T>>i
    out=[0]*(B if transpose else len(ports))
    for rowidx,j in enumerate(ports):
        val=0; unit=1
        for b in range(min(B,j+1)):
            d=sign*(ss[j]-ss[b]); vd,idn=den[d]
            exp=val+i-vd-es[b]
            if exp<0: raise ArithmeticError('negative normalized valuation')
            feat=unit*tunit*idn&mask
            feat=(feat<<exp)&mask
            if transpose: out[b]=(out[b]+values[rowidx]*feat)&mask
            else: out[rowidx]=(out[rowidx]+values[b]*feat)&mask
            if b<j:
                unit=unit*ratio[d]&mask
                val+=v2(d)-vd
    return out


def run_checks():
    rng=random.Random(873211)
    count=0; features=0; checks=[]
    for a in range(1,6):
        N=1<<(a-1)
        for i in range(a):
            for tunit in (-3,1,5):
                T=(tunit<<i)+(1<<(a+1))
                for B in sorted({1,N,max(1,N//2+1)}):
                    ports=[j for j in range(N) if rng.randrange(3)!=0] or [N-1]
                    p=rng.randrange(1,40)
                    for sign in (-1,1):
                        matrix=dense_fraction(a,i,T,B,sign,ports)
                        coeff=[rng.randrange(1<<p) for _ in range(B)]
                        vals=[rng.randrange(1<<p) for _ in ports]
                        oracle_s=[sum(residue(row[b],p)*coeff[b] for b in range(B))%(1<<p) for row in matrix]
                        oracle_a=[sum(residue(matrix[j][b],p)*vals[j] for j in range(len(ports)))%(1<<p) for b in range(B)]
                        actual_s,sm=synthesize(coeff,a,i,T,p,sign,ports,True)
                        actual_a,am=analyze(vals,a,i,T,p,sign,ports,B,True)
                        dense_s=dense_apply(coeff,a,i,T,p,sign,ports,B,False)
                        dense_a=dense_apply(vals,a,i,T,p,sign,ports,B,True)
                        if actual_s!=oracle_s or actual_a!=oracle_a or dense_s!=oracle_s or dense_a!=oracle_a:
                            raise AssertionError((a,i,T,B,p,sign,ports,actual_s,oracle_s,actual_a,oracle_a))
                        if sm['guard']>2*B+i or am['guard']>2*B+2*i: raise AssertionError('guard bound')
                        if sum(x*y for x,y in zip(vals,actual_s))%(1<<p)!=sum(x*y for x,y in zip(coeff,actual_a))%(1<<p): raise AssertionError('adjoint')
                        count+=1; features+=len(ports)*B
    # Larger independent recurrence cross-checks, including low-precision guards.
    for a in (6,7,8):
        N=1<<(a-1)
        for i in (0,a//2,a-1):
            for p in (1,7,4*N):
                T=(1<<i)+(1<<(a+1)); B=N-3
                vals=[rng.randrange(1<<p) for _ in range(N)]
                expected=dense_apply(vals,a,i,T,p,B=B)
                actual,meta=analyze(vals,a,i,T,p,B=B,return_meta=True)
                if actual!=expected: raise AssertionError(('large',a,i,p))
                checks.append({'N':N,'i':i,'p':p,'B':B,**meta})
    for a in range(1,9):
        N=1<<(a-1)
        for p in (1,7,4*N):
            for sign in (-1,1):
                T=1+(1<<(a+1)); vals=[rng.randrange(1<<p) for _ in range(N)]
                for transpose in (True,False):
                    actual=odd_level_transform(vals,a,T,p,sign,transpose)
                    expected=dense_apply(vals,a,0,T,p,sign,transpose=transpose)
                    if actual!=expected: raise AssertionError(('odd-level',a,p,sign,transpose))
    return {'odd_level_cases':8*3*2*2,'fraction_cases':count,'fraction_feature_entries':features,'larger_recurrence_cases':len(checks),'larger_cases':checks,'all_passed':True}


def benchmark():
    rng=random.Random(113); rows=[]
    for N in (32,64,128,256,512):
        a=N.bit_length(); i=0; T=1+(1<<(a+1)); p=4*N
        vals=[rng.randrange(1<<p) for _ in range(N)]
        times={}
        for key,fn in [('quadratic',lambda:dense_apply(vals,a,i,T,p)),('product_tree',lambda:analyze(vals,a,i,T,p)),('one_convolution',lambda:odd_level_transform(vals,a,T,p))]:
            runs=[]
            for rep in range(3):
                start=time.perf_counter(); result=fn(); runs.append(time.perf_counter()-start)
            times[key]=runs
            if key=='quadratic': expected=result
            elif result!=expected: raise AssertionError('benchmark mismatch')
        _,meta=analyze(vals,a,i,T,p,return_meta=True)
        q=sorted(times['quadratic'])[1]; f=sorted(times['product_tree'])[1]; c=sorted(times['one_convolution'])[1]
        rows.append({'N':N,'p':p,'i':i,'median_quadratic_seconds':q,'median_product_tree_seconds':f,'ratio_quadratic_over_tree':q/f,'median_one_convolution_seconds':c,'ratio_quadratic_over_convolution':q/c,'one_convolution_guard':2*((N-1)-(N-1).bit_count()),'one_convolution_working_precision':p+2*((N-1)-(N-1).bit_count()),'samples':times,**meta})
    return rows

if __name__=='__main__':
    parser=argparse.ArgumentParser(); parser.add_argument('--benchmark',action='store_true'); parser.add_argument('--output',default='fast_cauchy_results.json'); args=parser.parse_args()
    result={'checks':run_checks()}
    if args.benchmark: result['benchmarks']=benchmark()
    Path(args.output).write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({'checks_passed':result['checks']['all_passed'],'fraction_cases':result['checks']['fraction_cases'],'fraction_feature_entries':result['checks']['fraction_feature_entries'],'larger_recurrence_cases':result['checks']['larger_recurrence_cases'],'benchmarks':result.get('benchmarks',[])},indent=2))
