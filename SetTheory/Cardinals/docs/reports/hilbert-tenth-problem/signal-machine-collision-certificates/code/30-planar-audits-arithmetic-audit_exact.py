#!/usr/bin/env python3
"""Independent Report 60 audit. Never imports or runs any author executable.

Source equations are transcribed from the frozen PROOF.md, not loaded from its
checker. SymPy is used only as an independent exact polynomial engine. Fraction
arithmetic and direct 2x2 products provide separate arithmetic evidence.
"""
from pathlib import Path
from fractions import Fraction as F
from math import gcd, lcm
from functools import reduce
import hashlib
import json
import stat
import argparse
import sympy as sp

HERE = None  # Explicit fresh output directory, assigned by main.
ROOTS = {}   # Explicit relocated source roots; no location fallback.


def mm(a, b):
    return tuple(tuple(sum(a[i][k]*b[k][j] for k in range(2)) for j in range(2)) for i in range(2))


def mv(a, x):
    return tuple(sum(a[i][j]*x[j] for j in range(2)) for i in range(2))


def inv(a):
    det = a[0][0]*a[1][1]-a[0][1]*a[1][0]
    return ((a[1][1]/det, -a[0][1]/det), (-a[1][0]/det, a[0][0]/det))


def primitive(x):
    b = lcm(*(v.denominator for v in x))
    uv = [int(v*b) for v in x]
    assert gcd(gcd(*uv), b) == 1
    return *uv, b


def whole_q(b, q):
    m = 0
    while b % q == 0:
        b //= q
        m += 1
    return m, b


def beta_matrix_power(p, q, n):
    # Multiplication by beta in the integral basis (1,beta), using binary power.
    x = (1, 0)
    matrix = ((0, -q*q), (1, p))
    while n:
        if n & 1:
            x = mv(matrix, x)
        matrix = mm(matrix, matrix)
        n >>= 1
    return x


def accepted_by_gates(x, p, q, radius_deficit=0):
    u,v,b = primitive(x)
    m,r = whole_q(b,q)
    c,d = beta_matrix_power(p,q,m+1)
    return ((radius_deficit**2+(u-b)**2+v*v)>0 and
            (radius_deficit**2+(r-1)**2+(q*u-c)**2+(v-d)**2)>0)


def arithmetic_tests():
    result = dict(traces=0, powers=0, reverse_powers=0, factorizations=0,
                  point_grid=0, basis_instances=0, exhaustive_extractions=0)
    for q in range(2, 46):
        for p in range(1-2*q, 2*q):
            if gcd(p,q) != 1:
                continue
            result['traces'] += 1
            C = ((F(0),F(-1)), (F(1),F(p,q)))
            Ci = inv(C)
            x = y = (F(1),F(0))
            for n in range(37):
                u,v,b = primitive(x)
                assert b == (1 if n == 0 else q**(n-1))
                assert not accepted_by_gates(x,p,q)
                if n:
                    c,d = beta_matrix_power(p,q,n)
                    assert x == (F(c,q**n), F(d,q**(n-1)))
                    assert c % q == 0 and gcd(d,q)==1
                    P=q**(n-1); H=2*q*q*P; R=4*H+abs(p)+1
                    modulus=R*R-p*R+q*q
                    assert abs(c)<=H and abs(d)<=H
                    assert modulus>2*H*(1+R) and 2*H<R
                    assert (pow(R,n,modulus)-c-R*d)%modulus==0
                    assert accepted_by_gates(y,p,q)
                    result['reverse_powers'] += 1
                result['powers'] += 1
                x=mv(C,x); y=mv(Ci,y)
            for b in range(1,200):
                m,r=whole_q(b,q)
                k,s=divmod(r,q)
                assert b==q**m*r and k>=0 and 0<s<q
                result['factorizations'] += 1

    # Independent exact grid: direct companion powers, with the proven
    # denominator upper bound allowing a genuinely complete finite comparison.
    for p,q in [(1,2),(-3,2),(5,6),(-11,12),(17,25),(-61,32),(91,64)]:
        C=((F(0),F(-1)),(F(1),F(p,q)))
        for den in range(1,13):
            bound=den.bit_length()+2
            x=(F(1),F(0)); orbit=set()
            for _ in range(bound):
                orbit.add(x); x=mv(C,x)
            for u in range(-8,9):
                for v in range(-8,9):
                    point=(F(u,den),F(v,den))
                    assert accepted_by_gates(point,p,q)==(point not in orbit)
                    result['point_grid'] += 1
        for s in [((F(1,7),F(2,3)),(F(-5,4),F(3,8))),
                  ((F(2),F(1)),(F(1),F(1)))]:
            B=mm(mm(s,C),inv(s)); z=mv(s,(F(1),F(0)))
            assert (z,mv(B,z)) == ((s[0][0],s[1][0]),(s[0][1],s[1][1]))
            x=z
            for _ in range(25):
                assert not accepted_by_gates(mv(inv(s),x),p,q)
                x=mv(B,x)
                result['basis_instances'] += 1
    for q in (2,3):
        for p in range(1-2*q,2*q):
            if gcd(p,q)!=1:
                continue
            for m in (0,1):
                H=2*q*q*q**m; R=4*H+abs(p)+1; modulus=R*R-p*R+q*q
                target=pow(R,m+1,modulus)
                found=[(c,d) for c in range(-H,H+1) for d in range(-H,H+1)
                       if (c+R*d-target)%modulus==0]
                assert found==[beta_matrix_power(p,q,m+1)]
                result['exhaustive_extractions'] += 1
    return result


class Equations:
    def __init__(self, inputs):
        self.inputs=list(inputs)
        self.leaves=[]
        self.adapters={}
        self.rows=[]

    def variable(self,name,domain='positive'):
        if domain=='positive':
            leaves=[sp.Symbol(name,integer=True)]
            expr=leaves[0]
        elif domain=='natural':
            leaves=[sp.Symbol(name+'_shift',integer=True)]
            expr=leaves[0]-1
        else:
            leaves=[sp.Symbol(name+'_pos',integer=True),sp.Symbol(name+'_neg',integer=True)]
            expr=leaves[0]-leaves[1]
        assert not set(leaves).intersection(self.leaves+self.inputs)
        self.leaves.extend(leaves)
        self.adapters[name]={'domain':domain,'expression':str(expr),'positive_leaves':list(map(str,leaves))}
        return expr

    def record(self,name,left,right):
        self.rows.append((name,sp.expand(left-right)))

    def power(self,tag,base,exponent):
        v={n:self.variable(tag+n) for n in ['out','w','mod','g','x','y','u','v','s','t','qb','qv','j']}
        alpha=self.variable(tag+'alpha_leaf')+1
        beta=self.variable(tag+'beta_leaf')+1
        n={x:self.variable(tag+x,'natural') for x in ['dwbase','dwindex','dyindex','a1','a2','s1','s2','t1','t2','r1','r2']}
        out,w,M,g,x,y,u,vv,s,t,qb,qv,j=[v[x] for x in ['out','w','mod','g','x','y','u','v','s','t','qb','qv','j']]
        index=exponent+1; product=base*out
        pairs=[(x*x,1+(alpha*alpha-1)*y*y),
               (u*u,1+(alpha*alpha-1)*vv*vv),
               (s*s,1+(beta*beta-1)*t*t),
               (beta,1+4*y*qb),
               (beta+u*n['a1'],alpha+u*n['a2']),
               (vv,y*y*qv),
               (s+u*n['s1'],x+u*n['s2']),
               (t+4*y*n['t1'],index+4*y*n['t2']),
               (y,index+n['dyindex']),
               (w,base+n['dwbase']),
               (w,index+n['dwindex']),
               (M,product+j),
               (alpha*alpha,1+((w+1)**2-1)*(w*g)**2),
               (2*alpha*base,M+base*base+1),
               (x+M*n['r1'],y*(alpha-base)+product+M*n['r2'])]
        for i,(lhs,rhs) in enumerate(pairs,1):
            self.record(tag+f'eq{i:02}',lhs,rhs)
        return out


def build_schema(p,q,input_style,kernel=True,contacts=1,physical=None):
    if input_style=='five':
        aa=sp.symbols('a1:6',integer=True)
        X,Y,N=aa[0]-aa[1],aa[2]-aa[3],aa[4]
    else:
        aa=sp.symbols('g1:4',integer=True)
        X=2*aa[0]-aa[1]-aa[2]; Y=aa[0]+aa[1]-2*aa[2]; N=3*sum(aa)
    eq=Equations(aa)
    if physical is None:
        metric=sp.Matrix([[2*q,p],[p,2*q]]); ar=2*q
        bases=[(sp.eye(2),1)]*contacts
    else:
        metric,ar,bases=physical
        contacts=len(bases)
    d=eq.variable('radius','natural') if kernel else sp.Integer(0)
    if kernel:
        eq.record('radius_constraint',ar*N*N-(sp.Matrix([[X,Y]])*metric*sp.Matrix([X,Y]))[0],d)
    for j,(M,den) in enumerate(bases):
        tag=f'c{j}_'
        natural={n:eq.variable(tag+n,'natural') for n in ['m','k','lowC','highC','lowD','highD']}
        pos={n:eq.variable(tag+n) for n in ['h','b','r','s','t','jzero','jpos']}
        signed={n:eq.variable(tag+n,'signed') for n in ['u','v','e1','e2','e3','C','D','quot']}
        m,k,lc,hc,ld,hd=[natural[n] for n in ['m','k','lowC','highC','lowD','highD']]
        h,b,r,s,t,jzero,jpos=[pos[n] for n in ['h','b','r','s','t','jzero','jpos']]
        u,v,e1,e2,e3,C,D,quot=[signed[n] for n in ['u','v','e1','e2','e3','C','D','quot']]
        P=eq.power(tag+'qpower_',sp.Integer(q),m)
        H=2*q*q*P; R=4*H+abs(p)+1
        T=eq.power(tag+'rpower_',R,m+1)
        uv=M*sp.Matrix([X,Y]); W=den*N
        pairs=[(uv[0],h*u),(uv[1],h*v),(W,h*b),(e1*u+e2*v+e3*b,1),
               (b,P*r),(r,q*k+s),(s+t,q),(C+H,lc),(H-C,hc),(D+H,ld),(H-D,hd),
               (T-C-R*D,quot*(R*R-p*R+q*q)),
               (d*d+(u-b)**2+v*v,jzero),(d*d+(r-1)**2+(q*u-C)**2+(v-D)**2,jpos)]
        for i,(lhs,rhs) in enumerate(pairs,1):
            eq.record(tag+f'outer{i:02}',lhs,rhs)
    gens=eq.inputs+eq.leaves
    Fpoly=sp.Poly(sp.Add(*(sp.expand(expr**2) for _,expr in eq.rows)),*gens)
    result={'input_style':input_style,'kernel':kernel,'contacts':contacts,
            'inputs':list(map(str,eq.inputs)),'positive_witnesses':len(eq.leaves),
            'equations':len(eq.rows),'degree':Fpoly.total_degree(),'monomials':len(Fpoly.terms()),
            'residuals':[{ 'name':name,'degree':sp.Poly(ex,*gens).total_degree(),'expanded':str(ex)} for name,ex in eq.rows],
            'adapters':eq.adapters,'top_coefficients':{}}
    assert len(eq.leaves)==81*contacts+int(kernel)
    assert len(eq.rows)==44*contacts+int(kernel)
    assert Fpoly.total_degree()==12
    for j in range(contacts):
        for power in ('qpower_','rpower_'):
            tag=f'c{j}_'+power
            coeff=Fpoly.coeff_monomial(sp.Symbol(tag+'w',integer=True)**8*sp.Symbol(tag+'g',integer=True)**4)
            assert coeff==1
            result['top_coefficients'][tag+'w^8*g^4']=int(coeff)
    return result


def physical_geometry():
    source_name='five-signal-planar-realization60-20261004'
    relative=Path('evidence/elliptic_conjugate_lambda_1.json')
    path=ROOTS[source_name]/relative
    raw=json.loads(path.read_text())
    A=sp.Matrix([[sp.Rational(x) for x in row] for row in raw['matrix']])
    trace=sp.trace(A); p,q=map(int,sp.fraction(trace))
    z=sp.Matrix([1,0]); S=sp.Matrix.hstack(z,A*z)
    Q=S.inv().T*sp.Matrix([[1,trace/2],[trace/2,1]])*S.inv()
    assert A.T*Q*A==Q and Q.det()>0 and Q[0,0]>0
    records=[]
    for item in raw['guard_rows']:
        b,c,d=map(sp.Rational,item['row'])
        assert b>0
        h=sp.Matrix([[-c,-d]])
        if h==sp.zeros(1,2): continue
        norm=(h*Q.inv()*h.T)[0]
        radius=b*b/norm
        point=b/norm*Q.inv()*h.T
        assert (point.T*Q*point)[0]==radius
        records.append((radius,point,item['name']))
    radius=min(x[0] for x in records)
    contacts=[]
    for r,z,name in records:
        if r==radius and z not in contacts:contacts.append(z)
    scale=sp.ilcm(*[x.q for x in list(Q)+[radius]])
    G=scale*Q; ar=scale*radius
    bases=[]
    for z in contacts:
        S=sp.Matrix.hstack(z,A.inv()*z)
        t=sp.ilcm(*[x.q for x in S.inv()]); M=t*S.inv()
        assert all(x.q==1 for x in M)
        bases.append((M,t))
    report={'source':str(Path(source_name)/relative),'source_sha256':hashlib.sha256(path.read_bytes()).hexdigest(),
            'matrix':str(A),'trace':str(trace),'Q':str(Q),'radius_squared':str(radius),
            'integer_radius_scale':int(scale),'G':str(G),'a':str(ar),
            'contacts':[list(map(str,z)) for z in contacts],
            'contact_integer_basis_data':[{'M':str(M),'t':str(t)} for M,t in bases],
            'gap_input_aliases':{'X':'2*g1-g2-g3','Y':'g1+g2-2*g3','N':'3*(g1+g2+g3)'}}
    return p,q,(G,ar,bases),report


def pell(a,n):
    # Exact multiplication in Z[sqrt(a^2-1)], with binary powering.
    pair=(1,0); power=(a,1); D=a*a-1
    def product(x,y):return (x[0]*y[0]+D*x[1]*y[1],x[0]*y[1]+x[1]*y[0])
    while n:
        if n&1:pair=product(pair,power)
        power=product(power,power);n>>=1
    return pair


def constructive_power_samples():
    reports=[]
    for B,e in [(2,0),(2,1),(3,0),(3,1),(4,0),(6,0)]:
        k=e+1; out=B**e; m=B*out; w=max(B,k)
        alpha,inner_y=pell(w+1,w); assert inner_y%w==0
        g=inner_y//w; M=2*alpha*B-B*B-1
        x,y=pell(alpha,k); u,v=pell(alpha,2*k*y)
        modulus=4*y
        beta=(alpha+u*((1-alpha)*pow(u,-1,modulus)%modulus))%(u*modulus)
        assert beta>1
        s,t=pell(beta,k)
        assert (beta-1)%modulus==0 and v%(y*y)==0
        qb=(beta-1)//modulus; qv=v//(y*y)
        def split(n):return max(-n,0),max(n,0)
        a1,a2=split((beta-alpha)//u)
        s1,s2=split((s-x)//u)
        t1,t2=split((t-k)//modulus)
        r1,r2=split((x-y*(alpha-B)-m)//M)
        residuals=[x*x-1-(alpha*alpha-1)*y*y,
                   u*u-1-(alpha*alpha-1)*v*v,
                   s*s-1-(beta*beta-1)*t*t,
                   beta-1-4*y*qb,beta+u*a1-alpha-u*a2,v-y*y*qv,
                   s+u*s1-x-u*s2,t+4*y*t1-k-4*y*t2,y-k-(y-k),
                   w-B-(w-B),w-k-(w-k),M-m-(M-m),
                   alpha*alpha-1-((w+1)**2-1)*(w*g)**2,
                   2*alpha*B-M-B*B-1,x+M*r1-y*(alpha-B)-m-M*r2]
        assert residuals==[0]*15
        pos=[out,w,M,g,x,y,u,v,s,t,qb,qv,M-m,alpha-1,beta-1]
        nat=[w-B,w-k,y-k,a1,a2,s1,s2,t1,t2,r1,r2]
        assert min(pos)>0 and min(nat)>=0
        reports.append({'base':B,'exponent':e,'output':out,'all_residuals_zero':True,
                        'positive_leaves':len(pos)+len(nat),'largest_leaf_bits':max(x.bit_length() for x in pos+nat)})
    return reports


def source_state(manifest):
    observed={}
    # These are logical paths in the original frozen manifest. Only the
    # explicitly selected relocated root is ever used for filesystem reads.
    for name,expected in manifest.items():
        relative=Path(name).relative_to('/workspace/shared')
        root=ROOTS[relative.parts[0]]
        p=(root/Path(*relative.parts[1:])).resolve(strict=True)
        if not p.is_relative_to(root):raise ValueError('Source path escapes selected root')
        if not p.is_file():raise FileNotFoundError(p)
        st=p.stat()
        item=dict(bytes=st.st_size,mode=oct(stat.S_IMODE(st.st_mode)),mtime_ns=st.st_mtime_ns,
                  sha256=hashlib.sha256(p.read_bytes()).hexdigest())
        assert item['bytes']==expected['bytes'] and item['sha256']==expected['sha256'],str(p)
        observed[str(relative)]=item
    return observed


def check_unchanged(before,manifest):
    after=source_state(manifest)
    assert after==before,'A source changed during the audit'
    (HERE/'OBSERVED_SOURCES_AFTER.json').write_text(json.dumps(after,indent=2)+'\n')
    return len(after)


def main():
    global HERE,ROOTS
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--certificate-root',required=True,type=Path)
    parser.add_argument('--classification-root',required=True,type=Path)
    parser.add_argument('--physical-root',required=True,type=Path)
    parser.add_argument('--family59-root',required=True,type=Path)
    parser.add_argument('--source-manifest',required=True,type=Path)
    parser.add_argument('--output',required=True,type=Path)
    args=parser.parse_args()
    ROOTS={
        'elliptic-positive-certificate60-20261004':args.certificate_root.resolve(strict=True),
        'planar-strict-kernel-classification-20261004':args.classification_root.resolve(strict=True),
        'five-signal-planar-realization60-20261004':args.physical_root.resolve(strict=True),
        'five-signal-rotation-family59-20261004':args.family59_root.resolve(strict=True),
    }
    manifest_path=args.source_manifest.resolve(strict=True)
    manifest=json.loads(manifest_path.read_text())
    HERE=args.output.resolve()
    protected=list(ROOTS.values())+[Path(__file__).resolve().parent,manifest_path.parent]
    if any(HERE.is_relative_to(root) or root.is_relative_to(HERE) for root in protected):
        raise ValueError('Output must be external to every immutable input root')
    # A replay is never allowed to reuse a prior evidence directory.
    HERE.mkdir(parents=True,exist_ok=False)
    before=source_state(manifest)
    (HERE/'OBSERVED_SOURCES_BEFORE.json').write_text(json.dumps(before,indent=2)+'\n')
    receipt={'implementation':'independent exact Fraction/SymPy audit; all author programs remain inert',
             'sympy_version':sp.__version__,
             'source_manifest_sha256':hashlib.sha256(manifest_path.read_bytes()).hexdigest()}
    receipt['arithmetic']=arithmetic_tests()
    schemas={
        'one_contact_five_input_kernel':build_schema(-5,6,'five'),
        'one_contact_five_input_avoidance':build_schema(-5,6,'five',False),
        'two_contact_three_gap_kernel':build_schema(1,2,'three',contacts=2),
    }
    p,q,geometry,report=physical_geometry()
    schemas['physical_three_gap_kernel']=build_schema(p,q,'three',physical=geometry)
    receipt['physical_geometry']=report
    receipt['constructive_power_samples']=constructive_power_samples()
    receipt['schemas']={name:{k:v for k,v in data.items() if k not in ('residuals','adapters')} for name,data in schemas.items()}
    (HERE/'RECONSTRUCTED_SCHEMAS.json').write_text(json.dumps(schemas,indent=2)+'\n')
    receipt['unchanged_source_files']=check_unchanged(before,manifest)
    receipt['all_checks_passed']=True
    (HERE/'EXACT_RECEIPT.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps(receipt,indent=2))


if __name__=='__main__':main()
