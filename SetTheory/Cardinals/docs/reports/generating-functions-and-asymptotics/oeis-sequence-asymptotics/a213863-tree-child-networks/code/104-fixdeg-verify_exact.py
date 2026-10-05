#!/usr/bin/env python3
"""Independent finite exact checks for the fixed-d tree-child amplitude report.

No derivation program is imported or executed. Passing does not prove the report's
infinite-dimensional estimates or enclose its limiting amplitudes.
"""
from __future__ import annotations
import argparse, ast, hashlib, json, platform, sys, time
from datetime import datetime, timezone
from fractions import Fraction as F
from math import comb, factorial, prod
from pathlib import Path
import sympy as S

ROOT=Path(__file__).resolve().parent
INPUTS=('formal_coefficients.json','reference_sequences.json','ternary_degree6.json')
D_VALUES=tuple(range(2,13))
STARTUP = 9
M = 5
x,k,c,t,q,al=S.symbols('x k c t q al')
GATES=0
class VerificationError(RuntimeError): pass

def require(condition,label):
    global GATES
    GATES+=1
    if condition is not True and condition != S.true: raise VerificationError(label)
def equal(left,right,label): require(S.cancel(S.expand(left-right))==0,label)

def strict_json(path):
    def unique(pairs):
        out={}
        for key,val in pairs:
            require(key not in out,'duplicate JSON key: '+key);out[key]=val
        return out
    def nonfinite(value): raise VerificationError('nonfinite JSON constant: '+value)
    try: return json.loads(path.read_text(encoding='utf-8'),object_pairs_hook=unique,parse_constant=nonfinite)
    except (OSError,json.JSONDecodeError) as error: raise VerificationError('invalid JSON input: '+path.name) from error

def expression(text):
    require(type(text) is str and len(text)<=20000,'expression string schema')
    symbols={'x':x,'k':k,'c':c,'t':t,'q':q,'al':al}
    def visit(node):
        if isinstance(node,ast.Constant) and type(node.value) is int:
            require(abs(node.value)<=10**30,'integer expression bound');return S.Integer(node.value)
        if isinstance(node,ast.Name) and node.id in symbols:return symbols[node.id]
        if isinstance(node,ast.UnaryOp) and isinstance(node.op,(ast.UAdd,ast.USub)):
            val=visit(node.operand);return val if isinstance(node.op,ast.UAdd) else -val
        if isinstance(node,ast.BinOp):
            left,right=visit(node.left),visit(node.right)
            if isinstance(node.op,ast.Add):return left+right
            if isinstance(node.op,ast.Sub):return left-right
            if isinstance(node.op,ast.Mult):return left*right
            if isinstance(node.op,ast.Div):
                require(right!=0,'nonzero expression denominator');return left/right
            if isinstance(node.op,ast.Pow):
                require(right.is_Integer is True and abs(right)<=32,'bounded integer exponent');return left**right
        raise VerificationError('unsupported expression syntax')
    try:return visit(ast.parse(text,mode='eval').body)
    except (SyntaxError,RecursionError) as error:raise VerificationError('malformed arithmetic expression') from error

def load():
    manifest=strict_json(ROOT/'input_manifest.json')
    require(type(manifest) is dict and set(manifest)=={'schema','algorithm','files'},'manifest schema')
    require(type(manifest['schema']) is int and manifest['schema']==1 and manifest['algorithm']=='sha256','manifest version')
    require(type(manifest['files']) is dict and set(manifest['files'])==set(INPUTS),'manifest file set')
    require({p.name for p in (ROOT/'inputs').iterdir()}==set(INPUTS),'input directory file set')
    for name in INPUTS:
        p=ROOT/'inputs'/name
        require(p.is_file() and not p.is_symlink(),'regular local input: '+name)
        require(type(manifest['files'][name]) is str and len(manifest['files'][name])==64,'digest schema')
        require(hashlib.sha256(p.read_bytes()).hexdigest()==manifest['files'][name],'input SHA-256 mismatch: '+name)
    data=strict_json(ROOT/'inputs/formal_coefficients.json')
    require(type(data) is dict and set(data)=={'schema','degree','f','sigma','carrier','endpoint'},'formal object schema')
    require(type(data['schema']) is int and data['schema']==1,'formal schema version')
    require(type(data['degree']) is int and data['degree']==5,'formal degree coverage')
    require(type(data['f']) is list and len(data['f'])==4,'profile count')
    require(type(data['sigma']) is list and len(data['sigma'])==6,'sigma count')
    require(type(data['carrier']) is list and len(data['carrier'])==2,'carrier count')
    require(type(data['endpoint']) is list and len(data['endpoint'])==2,'endpoint count')
    fs=[]
    for pair in data['f']:
        require(type(pair) is list and len(pair)==2,'profile pair schema')
        fp=tuple(expression(z) for z in pair)
        for value in fp:
            require(value.free_symbols<={x,k,c},'profile variable set')
            numerator,denominator=S.fraction(S.cancel(value))
            require(denominator.free_symbols<={c},'profile denominator variables')
            require(S.Poly(numerator,x,k,c).domain in (S.QQ,S.ZZ),'rational profile coefficients')
        fs.append(fp)
    sig=[expression(z) for z in data['sigma']]
    carrier=[expression(z) for z in data['carrier']]
    endpoint=[expression(z) for z in data['endpoint']]
    require(all(z.free_symbols<={k,c} for z in sig+carrier),'scalar variable set')
    require(all(z.free_symbols<={q,al} for z in endpoint),'endpoint variable set')
    sequences=strict_json(ROOT/'inputs/reference_sequences.json')
    require(type(sequences) is dict and set(sequences)=={'schema','indices','values'},'sequence object schema')
    require(type(sequences['schema']) is int and sequences['schema']==1,'sequence schema version')
    require(sequences['indices']==list(range(7)) and all(type(j) is int for j in sequences['indices']),'sequence index coverage')
    require(type(sequences['values']) is dict and set(sequences['values'])=={str(d) for d in D_VALUES},'sequence d coverage')
    for values in sequences['values'].values():
        require(type(values) is list and len(values)==7 and all(type(v) is int and v>0 for v in values),'sequence values schema')
    ternary=strict_json(ROOT/'inputs/ternary_degree6.json')
    require(type(ternary) is dict and set(ternary)=={'schema','d','degree','f','sigma','carrier','normalizer_log_n','log_endpoint_t'},'ternary object schema')
    require(type(ternary['schema']) is int and ternary['schema']==1 and type(ternary['d']) is int and ternary['d']==3,'ternary schema version')
    require(type(ternary['degree']) is int and ternary['degree']==6,'ternary degree coverage')
    require(type(ternary['f']) is list and len(ternary['f'])==5,'ternary profile count')
    require(type(ternary['sigma']) is list and len(ternary['sigma'])==7,'ternary scalar count')
    require(type(ternary['carrier']) is list and len(ternary['carrier'])==3,'ternary carrier count')
    require(type(ternary['log_endpoint_t']) is list and len(ternary['log_endpoint_t'])==3,'ternary endpoint count')
    tf=[]
    for pair in ternary['f']:
        require(type(pair) is list and len(pair)==2,'ternary profile pair schema')
        vals=tuple(expression(value) for value in pair)
        for val in vals:
            require(val.free_symbols<={x,k} and S.Poly(val,x,k).domain in (S.QQ,S.ZZ),'ternary profile polynomial')
        tf.append(vals)
    ternary['f']=tf
    for key in ('sigma','carrier','log_endpoint_t'):
        ternary[key]=[expression(value) for value in ternary[key]]
        require(all(val.free_symbols<={k} and S.Poly(val,k).domain in (S.QQ,S.ZZ) for val in ternary[key]),'ternary scalar polynomial')
    ternary['normalizer_log_n']=expression(ternary['normalizer_log_n'])
    require(ternary['normalizer_log_n'].is_Rational is True,'ternary normalizer rational')
    return fs,sig,carrier,endpoint,sequences['values'],ternary

def coeff(d,n,j):
    r=d-1;a=d+1;z=a*n+r*j;P=a*(n+j)
    A=prod((F(z+i,P+i) for i in range(1,r+1)),start=F(1))
    B=F(z+r,z)
    C=prod((F(z+i-1,P+i) for i in range(1,r+1)),start=F(1))
    U=F(z+r-1,z-1)
    return A,B,C,U

def symedge(d,n,j):
    r=d-1;a=d+1;z=a*n+r*j
    first=prod((F(z+i,a*(n+j)+i) for i in range(1,r+1)),start=F(1))
    second=prod((F(z-d+i,a*(n+j-1)+i) for i in range(1,r+1)),start=F(1))
    return first*second*F(z-r,z)*F(z-d,z-1)

def naive_edge(d,n,j):
    r=d-1;a=d+1;z=a*n+r*j
    numerator=prod(z+i for i in range(1,r+1))*prod(z-i for i in range(1,r+1))*(z-r)*(z-d)
    return F(numerator,(a*(n+j))**r*(a*(n+j-1))**r*z*(z-1))

def finite(sequences):
    require(type(STARTUP) is int and STARTUP==9,'startup coverage configuration')
    require(D_VALUES==tuple(range(2,13)),'d coverage configuration')
    count=0;obstructions=[]
    for d in D_VALUES:
        r=d-1;a=d+1
        rows={1:[0,1]}
        for n in range(2,2*STARTUP+2):
            old=rows[n-1]
            rows[n]=[0]+[comb(d*n+j-2,r)*sum(old[1:min(j,n-1)+1]) for j in range(1,n+1)]
        require([1]+[sum(rows[n]) for n in range(1,7)]==sequences[str(d)],'reference sequence d='+str(d))
        def B(p,z):return rows[p+1][z+1] if 0<=z<=p else 0
        G=[1]
        for p in range(1,2*STARTUP+1):G.append(G[-1]*comb(a*p+r,r))
        for n in range(1,STARTUP+1):
            require(F(B(n,n),comb(a*n+r,r))==sum(rows[n]),'endpoint sequence identity')
        def yy(N,h):
            if h<0 or h>N or (N-h)%2 or N<0:return F(0)
            p,z=(N+h)//2,(N-h)//2
            return F(B(p,z),G[p])
        require(yy(0,0)==1 and yy(2,0)==1,'exact startup normalization')
        for N in range(1,2*STARTUP+1):
            for h in range(N%2,N+1,2):
                uu=prod((F(a*N+r*h+2*i,a*(N+h)+2*i) for i in range(1,r+1)),start=F(1))
                vv=F(a*N+r*h+2*r,a*N+r*h)
                require(yy(N,h)==uu*yy(N-1,h-1)+vv*yy(N-1,h+1),'one-step recurrence')
        e=[F(1)]
        previous_s=[F(1)]
        for n in range(1,STARTUP+1):
            new=[];squares=[F(1)]
            for j in range(n+1):
                A,Bb,C,U=coeff(d,n,j)
                require(Bb*C==A,'telescoping gauge identity')
                D=A;L=F(0)
                if j:
                    Ap,Bp,Cp,Up=coeff(d,n,j-1)
                    L=A*Cp;D+=A*Up
                    z=a*n+r*j
                    require(L*Bp*Up==A*Ap*F(z-1,z-d),'positive Gram edge')
                    require(D==A+A*F(z-1,z-d),'positive Gram diagonal')
                    edge=symedge(d,n,j)
                    require(edge==L/(Bp*Up),'symmetrizer factor identity')
                    require(0<edge<=1,'symmetrizer factor bounds')
                    squares.append(squares[-1]*edge)
                else:require(D==1,'exact lower diagonal')
                val=L*(e[j-1] if j else 0)+D*(e[j] if j<n else 0)+Bb*U*(e[j+1] if j+1<n else 0)
                require(val==yy(2*n,2*j),'two-step recurrence')
                if j<n:require(0<previous_s[j]/squares[j]<=1,'repaired inter-time contraction')
                new.append(val);count+=1
            e=new;previous_s=squares
    for d in (6,10):
        n=1000
        require(naive_edge(d,n-1,1)>naive_edge(d,n,1),'naive gauge obstruction d='+str(d))
        require(symedge(d,n-1,1)<symedge(d,n,1),'repaired gauge monotonicity d='+str(d))
        obstructions.append({'d':d,'n':n,'naive_R_squared_greater_than_one':True,'repaired_R_squared_less_than_one':True})
    return {'d_values':list(D_VALUES),'two_step_depth':STARTUP,'two_step_coordinates':count,'naive_obstruction_checks':obstructions}

# The formal verifier below uses only direct polynomial composition and Taylor
# differentiation; it never solves the triangular system that made the inputs.
def add(aa,bb):return [S.expand(a+b) for a,b in zip(aa,bb)]
def multiply(aa,bb,m):
    return [S.expand(sum(aa[i]*bb[j-i] for i in range(j+1) if i<len(aa) and j-i<len(bb))) for j in range(m+1)]
def series(expr,m):return [S.expand(S.series(expr,t,0,m+1).removeO()).coeff(t,j) for j in range(m+1)]
def deriv(pair,slope):
    p,z=pair
    return (S.diff(p,x)+(slope*x+k)*z,p+S.diff(z,x))
def shifted(fs,sign,m,slope):
    stretch=[S.S(0)]*(m+1)
    for j in range(m//3+1):stretch[3*j]=S.rf(S.Rational(1,3),j)/S.factorial(j)
    change=[S.expand(x*stretch[j]+(sign*stretch[j-1] if j else 0)-(x if j==0 else 0)) for j in range(m+1)]
    out=[[S.S(0)]*(m+1) for _ in range(2)]
    for idx,pair in enumerate(fs):
        fac=[S.S(0)]*(m+1)
        for j in range((m-idx)//3+1):fac[idx+3*j]=S.rf(S.Rational(idx,3),j)/S.factorial(j)
        power=[S.S(1)]+[S.S(0)]*m
        dpair=pair
        for order in range(m-idx+1):
            aa=multiply(fac,power,m)
            for comp in range(2):
                for j in range(m+1):out[comp][j]+=aa[j]*dpair[comp]/S.factorial(order)
            dpair=deriv(dpair,slope);power=multiply(power,change,m)
    return [[S.expand(z) for z in row] for row in out]

def formal(fs,sig):
    require(type(M) is int and M==5,'formal checker coverage')
    equal(fs[0][0],1,'initial profile P');equal(fs[0][1],0,'initial profile Q')
    for j,(p,z) in enumerate(fs[1:],1):
        equal(z.subs(x,0),0,'boundary profile '+str(j))
        equal((p+S.diff(z,x)).subs(x,0),0,'derivative gauge profile '+str(j))
    u=[1,0,-c*x,c,c*(3*c+2)*x*x/4,-c*(5*c+2)*x/4]
    v=[1,0,0,c,0,-c*c*x/2]
    minus=shifted(fs,-1,M,c);plus=shifted(fs,1,M,c)
    for comp in range(2):
        right=add(multiply(u,minus[comp],M),multiply(v,plus[comp],M))
        left=multiply(sig,[fp[comp] for fp in fs],M)
        for j in range(M+1):equal(left[j],right[j],'formal pair recurrence degree '+str(j)+' component '+str(comp))
    # Independently expand finite products; this checks the generic weight jet.
    for d in (2,3,4,6,10):
        r=d-1;a=d+1;slope=S.Rational(2*r,a)
        exact_u=[S.S(1)]+[S.S(0)]*M
        for i in range(1,r+1):
            factor=(a+r*x*t*t+(2*i-r)*t**3)/(a+a*x*t*t+(2*i-a)*t**3)
            exact_u=multiply(exact_u,series(factor,M),M)
        exact_v=series((a+r*x*t*t+r*t**3)/(a+r*x*t*t-r*t**3),M)
        for j in range(M+1):
            equal(exact_u[j],S.sympify(u[j]).subs(c,slope),'finite-d U coefficient')
            equal(exact_v[j],S.sympify(v[j]).subs(c,slope),'finite-d V coefficient')
    # Generic factor deficits are the algebraic reason for monotonicity.
    rr,nn,jj,ii=S.symbols('r n j i',positive=True);aa=rr+2;zz=aa*nn+rr*jj
    pairs=[(zz+ii,aa*(nn+jj)+ii,2*jj),(zz-(rr+1)+ii,aa*(nn+jj-1)+ii,2*jj-1),(zz-rr,zz,rr),(zz-rr-1,zz-1,rr)]
    for numerator,denominator,gap in pairs:
        equal(denominator-numerator,gap,'generic factor deficit')
        equal(S.diff(numerator/denominator,nn),aa*gap/denominator**2,'generic factor monotonic derivative')
    return {'degree':M,'profile_count':len(fs),'generic_pair_residuals':2*(M+1),'finite_product_d_values':[2,3,4,6,10],'generic_monotone_factor_identities':4}

def endpoint(sig,carrier,coefficients):
    h1,h2=carrier
    ss=sum(sig[j]*t**j for j in range(M+1))
    eta=3*c/4-S.Rational(1,6)
    rhs=(3*k/(2*t))*(1-(1-t**3)**S.Rational(1,3))-eta*S.log(1-t**3)+h1*t*(1-(1-t**3)**(-S.Rational(1,3)))+h2*t*t*(1-(1-t**3)**(-S.Rational(2,3)))
    difference=S.series(S.log(ss/2)-rhs,t,0,6).removeO().expand()
    for j in range(6):equal(difference.coeff(t,j),0,'scalar carrier difference degree '+str(j))
    # A(t)/(A'(0)t)=1+k*t^2/6+O(t^3). Higher profiles have
    # zero value and derivative, so they enter at t^3 or later here.
    substitutions={c:2*q**3,k:2**S.Rational(2,3)*al*q*q}
    first=S.simplify(h1.subs(substitutions)*2**(-S.Rational(1,3)))
    second=S.simplify((h2+h1*h1/2+k/6).subs(substitutions)*2**(-S.Rational(2,3)))
    equal(first,coefficients[0],'first endpoint coefficient')
    equal(second,coefficients[1],'second endpoint coefficient')
    rr=S.symbols('r');aa=rr+2;delta=rr*(rr+1)/(2*aa);zeta=3*rr/(2*aa)
    equal(delta-rr+zeta-S.Rational(1,2),-(rr*rr+rr+2)/(2*aa),'word polynomial exponent')
    equal(delta-2*rr+zeta-S.Rational(1,2),-(rr+1)*(3*rr+2)/(2*aa),'network polynomial exponent')
    equal((6*rr/aa)/4,zeta,'frozen scalar product exponent')
    # The second binary logarithmic correction vanishes exactly.
    equal((coefficients[1]-coefficients[0]**2/2).subs(q,3**(-S.Rational(1,3))),0,'binary second correction specialization')
    return {'carrier_degrees':[4,5],'endpoint_coefficients':2,'exact_exponent_identities':3,'binary_specialization':True}

def ternary_check(data):
    depth=6;fs=data['f'];sig=data['sigma'];hh=data['carrier']
    equal(fs[0][0],1,'ternary initial profile');equal(fs[0][1],0,'ternary initial derivative profile')
    for j,(pp,qq) in enumerate(fs[1:],1):
        equal(qq.subs(x,0),0,'ternary boundary profile')
        equal((pp+S.diff(qq,x)).subs(x,0),0,'ternary derivative gauge')
    uu=[S.S(1)]+[S.S(0)]*depth
    for i in (1,2):uu=multiply(uu,series((4+2*x*t*t+(2*i-2)*t**3)/(4+4*x*t*t+(2*i-4)*t**3),depth),depth)
    vv=series((4+2*x*t*t+2*t**3)/(4+2*x*t*t-2*t**3),depth)
    minus=shifted(fs,-1,depth,S.S(1));plus=shifted(fs,1,depth,S.S(1))
    for component in range(2):
        right=add(multiply(uu,minus[component],depth),multiply(vv,plus[component],depth))
        left=multiply(sig,[pair[component] for pair in fs],depth)
        for j in range(depth+1):equal(left[j],right[j],'ternary formal pair recurrence degree '+str(j))
    scalar=sum(sig[j]*t**j for j in range(depth+1))
    rhs=3*k/(2*t)*(1-(1-t**3)**S.Rational(1,3))-S.Rational(7,12)*S.log(1-t**3)
    for j,h in enumerate(hh,1):rhs+=h*t**j*(1-(1-t**3)**(-S.Rational(j,3)))
    difference=S.series(S.log(scalar/2)-rhs,t,0,7).removeO().expand()
    for j in range(7):equal(difference.coeff(t,j),0,'ternary carrier difference degree '+str(j))
    # Independently generate the normalized Airy solution by its ODE.
    coeffs=[S.S(0),S.S(1)]
    for j in range(7):coeffs.append(S.expand((k*coeffs[j]+(coeffs[j-1] if j else 0))/((j+1)*(j+2))))
    airy=sum(coeffs[j]*x**j for j in range(len(coeffs)))
    total=sum(t**j*(pp*airy+qq*S.diff(airy,x)).subs(x,t) for j,(pp,qq) in enumerate(fs))
    endpoint_series=S.series(total/t,t,0,4).removeO()
    endpoint_log=S.series(S.log(endpoint_series),t,0,4).removeO().expand()
    gamma_log=sum((v*v-v)/2 for v in (S.Rational(1,4),S.Rational(1,2)))
    equal(gamma_log,data['normalizer_log_n'],'ternary exact gamma normalizer')
    # n^-1=2t^3 because this is the even-time carrier N=2n.
    canonical=S.expand(endpoint_log+sum(hh[j-1]*t**j for j in range(1,4))+2*gamma_log*t**3)
    for j in range(1,4):equal(canonical.coeff(t,j),data['log_endpoint_t'][j-1],'ternary logarithmic endpoint coefficient '+str(j))
    return {'degree':6,'profile_count':5,'pair_residuals':14,'log_coefficients_t':[str(v) for v in data['log_endpoint_t']],'gamma_normalizer_log_n':str(gamma_log),'n_cubic_log_coefficient':str(S.expand(data['log_endpoint_t'][2]/2))}

def main():
    parser=argparse.ArgumentParser();parser.add_argument('--section',choices=['all','finite','formal','endpoint','ternary'],default='all');parser.add_argument('--output',type=Path,default=ROOT/'results/verification.json');args=parser.parse_args()
    result={'schema':1,'status':'FAIL','optimization':sys.flags.optimize,'python':platform.python_version(),'sympy':S.__version__,'started_utc':datetime.now(timezone.utc).isoformat(),'checks':{}}
    start=time.monotonic()
    try:
        fs,sig,carrier,co,seq,ternary=load()
        if args.section in ('all','finite'):result['checks']['finite']=finite(seq)
        if args.section in ('all','formal'):result['checks']['formal']=formal(fs,sig)
        if args.section in ('all','endpoint'):result['checks']['endpoint']=endpoint(sig,carrier,co)
        if args.section in ('all','ternary'):result['checks']['ternary']=ternary_check(ternary)
        result['status']='PASS'
    except Exception as error:
        result['error_type']=type(error).__name__;result['error']=str(error)
        print('FAIL '+str(error),file=sys.stderr)
    result['gates']=GATES;result['elapsed_seconds']=round(time.monotonic()-start,6)
    args.output.parent.mkdir(parents=True,exist_ok=True);args.output.write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print(json.dumps(result,sort_keys=True))
    return 0 if result['status']=='PASS' else 1
if __name__=='__main__':sys.exit(main())
