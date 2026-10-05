#!/usr/bin/env python3
"""Exact finite DFA checks. Passing is not an analytic proof of asymptotics."""
import argparse
import ast
from collections import defaultdict
from fractions import Fraction as F
import hashlib
import json
from math import factorial
from pathlib import Path
import platform
import sys
import sympy as S
from formal_engine import (VerificationError, require, zero, x, k, t, a, ORDER,
    derivative, airy_operator, recurrence_rhs, construct, integrate_endpoint,
    direct_ratio, ratio_from_log)

ROOT = Path(__file__).resolve().parent
REPORT = ROOT.parent
n, m, N, h, L, r, s = S.symbols('n m N h L r s')
SYMBOLS = {str(z): z for z in (x,k,t,a,n,m,N,h,L,r,s)}
# Exact release pins. The program never regenerates or rewrites its inputs.
PINNED_INPUTS = {'exact.json': '05a1062a8e96d0cb259fb33b208501a5e0587fb153c8cd9e766ce69e092bc7e7', 'formal_7.json': 'db4a250810fce53db8baf384622d4c1ba8730fbb8eefcf3f8bba2b3a9b1321be', 'endpoint_7.json': '685e3d6ffc3ffd55d44cc7af7a4d28d9b5e944492f66ed9e4ca9dbc66f9f3d74', 'inverse.json': '484741e867e0f33786446808078fd64199110b2cf61d417a9327ab66880f7404', 'dependencies.json': 'c02620e20e3d0e3eb24a7e591f9e1ceb5f57744fb401aa0be4046a01dd01a317'}
PINNED_DEPENDENCIES = {
    'dependencies/relaxed_tree_amplitude.pdf': '4684736e1fdfb4ccf63962a7c1c21b14f00e76832ef97d7e808867d97c29d2e3',
    'dependencies/relaxed_tree_amplitude_sources.zip': '72e791418b8b1cf401a2b3b1a0441a24cb95d2aee1eb2f36fdcb0f04e05b3f40',
}
DATA_NAMES = ('exact.json','formal_7.json','endpoint_7.json','inverse.json','dependencies.json')
SOURCE_NAMES = frozenset(('README.md','requirements.txt','formal_engine.py','verify.py','negative_tests.py','replay.sh',*(f'data/{name}' for name in DATA_NAMES)))

def emit(message):
    print(message, flush=True)

def exact_keys(obj, keys, label):
    require(type(obj) is dict and set(obj)==set(keys), f'{label}: incorrect object keys')

def exact_list(obj, size, label):
    require(type(obj) is list and len(obj)==size, f'{label}: expected {size} entries')

def unique_object(pairs):
    obj = {}
    for key, value in pairs:
        require(key not in obj, f'duplicate JSON key: {key}')
        obj[key] = value
    return obj

def decode_json(content, label):
    try:
        return json.loads(content, object_pairs_hook=unique_object,
            parse_constant=lambda v: (_ for _ in ()).throw(VerificationError(f'{label}: forbidden nonfinite value')))
    except (UnicodeError, json.JSONDecodeError) as error:
        raise VerificationError(f'{label}: invalid JSON: {error}') from error

def expression(text, symbols, label, polynomial=False):
    """Parse a small exact arithmetic language; never eval/sympify input strings."""
    require(type(text) is str and 0<len(text)<=20000, f'{label}: expression string required')
    names = {str(z):z for z in symbols}
    try:
        tree = ast.parse(text,mode='eval')
    except (SyntaxError,ValueError,RecursionError) as error:
        raise VerificationError(f'{label}: invalid expression syntax') from error
    require(sum(1 for _ in ast.walk(tree))<=4000, f'{label}: expression too large')
    def convert(node):
        if isinstance(node,ast.Constant) and type(node.value) is int:
            require(abs(node.value)<=10**30, f'{label}: integer too large')
            return S.Integer(node.value)
        if isinstance(node,ast.Name) and node.id in names:
            return names[node.id]
        if isinstance(node,ast.UnaryOp) and isinstance(node.op,(ast.UAdd,ast.USub)):
            val=convert(node.operand)
            return val if isinstance(node.op,ast.UAdd) else -val
        if isinstance(node,ast.BinOp) and isinstance(node.op,(ast.Add,ast.Sub,ast.Mult,ast.Div,ast.Pow)):
            left,right=convert(node.left),convert(node.right)
            if isinstance(node.op,ast.Add): return left+right
            if isinstance(node.op,ast.Sub): return left-right
            if isinstance(node.op,ast.Mult): return left*right
            if isinstance(node.op,ast.Div):
                require(right!=0,f'{label}: zero denominator')
                if polynomial:
                    require(right.is_Rational is True,f'{label}: polynomial denominator must be rational')
                return left/right
            require(right.is_Integer is True and 0<=right<=32,f'{label}: power outside integer range 0..32')
            return left**right
        raise VerificationError(f'{label}: unsupported expression syntax')
    try:
        result = S.cancel(convert(tree.body))
        require(not result.has(S.zoo,S.nan,S.oo,-S.oo),f'{label}: nonfinite expression')
        num,den = S.fraction(result)
        for part in (num,den):
            if symbols:
                poly=S.Poly(part,*symbols,domain=S.QQ)
                require(poly.total_degree()<=64,f'{label}: degree limit exceeded')
            else:
                require(part.is_Rational is True,f'{label}: rational value required')
        return S.expand(result) if polynomial else result
    except (S.PolynomialError,S.CoercionFailed,ValueError,TypeError,RecursionError) as error:
        raise VerificationError(f'{label}: invalid exact expression') from error

def eq(left,right,label):
    require(S.cancel(left-right)==0,f'{label}: nonzero exact residual {S.factor(left-right)}')

def rat(expr,values):
    result=expr.subs(values)
    require(result.is_Rational is True,f'non-rational finite evaluation: {result}')
    return F(int(S.numer(result)),int(S.denom(result)))

def check_content_pin(content, expected, label):
    require(hashlib.sha256(content).hexdigest()==expected,f'{label}: SHA-256 mismatch')

def check_package_integrity(package_root=ROOT):
    manifest=decode_json((package_root/'manifest.json').read_bytes(),'source manifest')
    exact_keys(manifest,('schema','algorithm','files'),'source manifest')
    require(type(manifest['schema']) is int and manifest['schema']==1 and manifest['algorithm']=='sha256','source manifest schema/algorithm')
    require(type(manifest['files']) is dict and set(manifest['files'])==SOURCE_NAMES,'source manifest incomplete or unexpected')
    for name,digest in manifest['files'].items():
        require(type(digest) is str and len(digest)==64 and all(c in '0123456789abcdef' for c in digest),'source manifest hash format')
        path=package_root/name
        require(path.is_file() and not path.is_symlink(),f'{name}: missing regular source file')
        check_content_pin(path.read_bytes(),digest,f'source {name}')
    emit(f'PASS source-package manifest: {len(SOURCE_NAMES)} files')

def load_all():
    check_package_integrity()
    require(set(PINNED_INPUTS)==set(DATA_NAMES),'input pin registry incomplete')
    data={}
    for name in DATA_NAMES:
        path=ROOT/'data'/name
        require(path.is_file() and not path.is_symlink(),f'{name}: missing regular immutable input')
        content=path.read_bytes()
        check_content_pin(content,PINNED_INPUTS[name],name)
        data[name]=decode_json(content,name)
    emit(f'PASS immutable JSON input hashes: {len(data)} files')
    return data

def check_dependencies(data,report_root=REPORT):
    exact_keys(data,('schema','dependencies'),'dependencies')
    require(type(data['schema']) is int and data['schema']==1,'dependencies: unsupported schema')
    exact_list(data['dependencies'],2,'dependencies')
    observed={}
    for entry in data['dependencies']:
        exact_keys(entry,('path','sha256'),'dependency entry')
        path,digest=entry['path'],entry['sha256']
        require(type(path) is str and path in PINNED_DEPENDENCIES,'unexpected dependency path')
        require(path not in observed,'duplicate dependency')
        require(digest==PINNED_DEPENDENCIES[path],f'{path}: changed declared pin')
        source=report_root/path
        require(source.is_file() and not source.is_symlink(),f'{path}: missing regular dependency')
        check_content_pin(source.read_bytes(),digest,path)
        observed[path]=digest
    require(observed==PINNED_DEPENDENCIES,'dependency registry incomplete')
    emit('PASS relaxed dependency integrity: both pinned PDF and source ZIP match SHA-256')

def parse_exact(raw):
    exact_keys(raw,('schema','triangle_max_n','diagonal_counts','proposition5','uniform_B','startup_e',
        'rotated','odd_even','memory','gauge','formal_rational'),'exact')
    require(type(raw['schema']) is int and raw['schema']==1 and type(raw['triangle_max_n']) is int and raw['triangle_max_n']==36,'exact: schema or range')
    exact_list(raw['diagonal_counts'],10,'diagonal_counts')
    require(all(type(v) is int and v>0 for v in raw['diagonal_counts']),'diagonal_counts: positive integers required')
    exact_list(raw['startup_e'],6,'startup_e')
    groups={
        'proposition5': ('left','up','lag','negative_seed'),
        'uniform_B': ('left','up','lag'),
        'rotated': ('left','right','lag'),
        'odd_even': ('a','g','p','q'),
        'memory': ('L','D','P','Q','W','B_row0','F_row0','B_sign','F_sign','A_input_end','B_input_end','F_input_end'),
        'gauge': ('j_squared','R_squared','P_over_j_squared','W_over_j_squared'),
        'formal_rational': ('W','D'),
    }
    out={}
    for group,keys in groups.items():
        exact_keys(raw[group],keys,group)
        out[group]={}
        for key in keys:
            if key in ('B_sign','F_sign'):
                require(type(raw[group][key]) is int and raw[group][key] in (-1,1),f'{group}/{key}: invalid sign')
                out[group][key]=S.Integer(raw[group][key])
            else:
                out[group][key]=expression(raw[group][key],tuple(SYMBOLS.values()),f'{group}/{key}')
    return out

def check_triangle(raw):
    d=parse_exact(raw)
    source=d['proposition5']
    for key,expected in [('left',2),('up',m+1),('lag',-m),('negative_seed',1)]:
        eq(source[key],expected,f'Proposition 5/{key}')
    for key,expected in [('left',source['left']/2),('up',source['up']),('lag',source['lag']/2)]:
        eq(d['uniform_B'][key],expected,f'uniform B/{key}')
    b=defaultdict(int)
    maxn=raw['triangle_max_n']
    for nn in range(-1,maxn+1): b[nn,0]=1
    for nn in range(1,maxn+1):
        for mm in range(1,nn+1):
            b[nn,mm]=2*b[nn,mm-1]+(mm+1)*b[nn-1,mm]-mm*b[nn-2,mm-1]
            require(type(b[nn,mm]) is int and b[nn,mm]>=0,f'counting triangle {(nn,mm)}')
    require([b[j,j] for j in range(10)]==raw['diagonal_counts'],'Proposition 5 diagonal mismatch')
    require(b[-1,0]==1 and b[1,1]==1,'negative-index startup seed lost')
    relaxed=defaultdict(int)
    for nn in range(maxn+1):
        relaxed[nn,0]=1
        for mm in range(1,nn+1):
            relaxed[nn,mm]=relaxed[nn,mm-1]+(mm+1)*relaxed[nn-1,mm]
            require(0<=b[nn,mm]<=2**mm*relaxed[nn,mm],f'counting domination {(nn,mm)}')
    def B(nn,mm):
        if (nn,mm)==(-1,0): return F(b[-1,0])
        if mm<0 or nn<mm: return F(0)
        return F(b[nn,mm],2**mm)
    require(B(-1,0)==1,'uniform B negative seed')
    # The negative-index seed belongs to B; the rotated e domain starts at N=0.
    for nn in range(1,maxn+1):
        for mm in range(1,nn+1):
            lag=B(nn-2,mm-1)
            rhs=B(nn,mm-1)+(mm+1)*B(nn-1,mm)-F(mm,2)*lag
            require(B(nn,mm)==rhs,f'uniform B recurrence {(nn,mm)}')
    def e(T,H):
        if T<0 or H<0 or H>T or (T-H)%2: return F(0)
        nn,mm=(T+H)//2,(T-H)//2
        require(nn<=maxn,'checker triangle bounds exceeded')
        return B(nn,mm)/factorial(nn)
    observed=set()
    for entry in raw['startup_e']:
        exact_list(entry,3,'startup entry')
        T,H,value=entry
        require(type(T) is int and type(H) is int and (T,H) not in observed,'startup coordinates malformed or duplicate')
        observed.add((T,H))
        require(e(T,H)==rat(expression(value,(),'startup'),{}),f'startup e({T},{H})')
    require(observed=={(0,0),(1,1),(2,0),(2,2),(3,1),(3,3)},'startup support incomplete')
    rotated=d['rotated']
    # Uniform normalization plus factorial ratios, before any finite evaluations.
    eq(rotated['left'],((N-h)/2+1)/((N+h)/2),'rotated left derivation')
    eq(rotated['right'],1,'rotated right derivation')
    eq(rotated['lag'],-((N-h)/4)/(((N+h)/2)*((N+h)/2-1)),'rotated lag derivation')
    total=0
    for T in range(3,maxn+1):
        for H in range(T+1):
            if (T-H)%2: continue
            vals={N:T,h:H}
            rhs=rat(rotated['left'],vals)*e(T-1,H-1)+e(T-1,H+1)+rat(rotated['lag'],vals)*e(T-3,H-1)
            require(e(T,H)==rhs,f'rotated recurrence {(T,H)}')
            require(e(T,T)==F(1,factorial(T)),f'top-edge factorial {T}')
            if H==0: require(e(T,0)==e(T-1,1),f'row zero {T}')
            total+=1
    for nn in range(19):
        require(b[nn,nn]==2**nn*factorial(nn)*e(2*nn,0),f'diagonal conversion {nn}')
    emit(f'PASS Proposition 5: {maxn} rows; diagonal {raw["diagonal_counts"]}')
    emit(f'PASS uniform B, startup, support, domination, factorial edge; {total} rotated sites through N=36')
    return d,e

def check_elimination(raw,e=None):
    d=parse_exact(raw)
    oe,mem=d['odd_even'],d['memory']
    aa,gg,pp,qq=[oe[key] for key in ('a','g','p','q')]
    rot=d['rotated']
    for key,left,right in [
        ('even a',aa,rot['left'].subs({N:2*n,h:2*k})),
        ('even g',gg,-rot['lag'].subs({N:2*n,h:2*k})),
        ('odd p',pp,rot['left'].subs({N:2*n-1,h:2*k+1})),
        ('odd q',qq,-rot['lag'].subs({N:2*n-1,h:2*k+1}))]: eq(left,right,key)
    identities={
        'L': aa*pp.subs(k,k-1), 'D':aa+pp,
        'P':aa*qq.subs(k,k-1)+gg*pp.subs({n:n-1,k:k-1}, simultaneous=True),
        'Q':qq+gg, 'W':gg*qq.subs({n:n-1,k:k-1}, simultaneous=True),
        'B_row0':qq.subs(k,0),'F_row0':0,
        'B_sign':-1,'F_sign':1,
        'A_input_end':n-1,'B_input_end':n-2,'F_input_end':n-3,
    }
    for key,expected in identities.items(): eq(mem[key],expected,f'elimination/{key}')
    eq(pp.subs(k,0),1,'exceptional row-zero p')
    sites=0
    for nn in range(4,37):
        Aend,Bend,Fend=[int(mem[key].subs(n,nn)) for key in ('A_input_end','B_input_end','F_input_end')]
        for kk in range(nn+1):
            if kk==0:
                require(rat(mem['B_row0'],{n:nn})==F(1,2*nn),'origin memory')
                require(rat(mem['F_row0'],{n:nn})==0,'origin third lag')
            else:
                vals={n:nn,k:kk}
                for key,index,end in [('L',kk-1,Aend),('D',kk,Aend),('P',kk-1,Bend),('Q',kk,Bend),('W',kk-1,Fend)]:
                    if 0<=index<=end:
                        require(rat(mem[key],vals)>=0,f'actual nonnegative {key} row {(nn,kk)}')
            if e is not None and nn<=18:
                u=lambda time,height:e(2*time,2*height)
                if kk==0:
                    rhs=u(nn-1,0)+u(nn-1,1)-rat(mem['B_row0'],{n:nn})*u(nn-2,0)
                else:
                    c={key:rat(mem[key],{n:nn,k:kk}) for key in ('L','D','P','Q','W')}
                    rhs=c['L']*u(nn-1,kk-1)+c['D']*u(nn-1,kk)+u(nn-1,kk+1)-c['P']*u(nn-2,kk-1)-c['Q']*u(nn-2,kk)+c['W']*u(nn-3,kk-1)
                require(u(nn,kk)==rhs,f'exact three-lag recurrence {(nn,kk)}')
                sites+=1
    # An unsupported diagonal must stay absent, even though its raw formula is negative.
    require(rat(mem['Q'],{n:8,k:8})<0 and int(mem['B_input_end'].subs(n,8))<8,'support trap not detected')
    emit(f'PASS five symbolic elimination identities, signs, exceptional row zero; support/nonnegativity through n=36; {sites} exact sites through n=18')
    return d

def gauge_squared(nn,kk):
    require(nn>=1 and 0<=kk<=nn,'factorial gauge domain')
    return F(factorial(nn)**2,factorial(nn-kk)**2)*F(factorial(nn-1)*factorial(nn),factorial(nn+kk-1)*factorial(nn+kk))

def check_gauge(raw):
    d=parse_exact(raw)
    mem,g=d['memory'],d['gauge']
    eq(g['j_squared'],mem['L'],'j squared')
    eq(mem['P']**2/g['j_squared'],g['P_over_j_squared'],'P/j squared cancellation')
    eq(mem['W']**2/g['j_squared'],g['W_over_j_squared'],'W/j squared cancellation')
    R2=g['R_squared']
    eq(R2,((n-k)/n)**2*(n+k)*(n+k-1)/(n*(n-1)),'factorial gauge ratio squared')
    comparisons=0
    for nn in range(4,37):
        for kk in range(nn):
            r2=rat(R2,{n:nn,k:kk})
            require(r2==gauge_squared(nn-1,kk)/gauge_squared(nn,kk),f'gauge ratio {(nn,kk)}')
            require(0<r2<=1,f'gauge contraction {(nn,kk)}')
        for kk in range(1,nn+1):
            j2=rat(g['j_squared'],{n:nn,k:kk})
            require(j2==gauge_squared(nn,kk)/gauge_squared(nn,kk-1),f'Jacobi adjacent gauge {(nn,kk)}')
        for kk in range(nn+1):
            vals={n:nn,k:kk}
            if kk<=nn-2:
                coeff=rat(mem['B_row0'] if kk==0 else mem['Q'],vals)
                actual=coeff**2*gauge_squared(nn-2,kk)/gauge_squared(nn,kk)
                factored=coeff**2*rat(R2,vals)*rat(R2,{n:nn-1,k:kk})
                require(actual==factored,f'conjugated diagonal {(nn,kk)}')
                comparisons+=1
            if 1<=kk<=nn-1:
                coeff=rat(mem['P'],vals)
                actual=coeff**2*gauge_squared(nn-2,kk-1)/gauge_squared(nn,kk)
                factored=rat(g['P_over_j_squared'],vals)*rat(R2,{n:nn,k:kk-1})*rat(R2,{n:nn-1,k:kk-1})
                require(actual==factored,f'conjugated lower memory {(nn,kk)}')
                comparisons+=1
            if 1<=kk<=nn-2:
                coeff=rat(mem['W'],vals)
                actual=coeff**2*gauge_squared(nn-3,kk-1)/gauge_squared(nn,kk)
                factored=rat(g['W_over_j_squared'],vals)
                for lag in range(3): factored*=rat(R2,{n:nn-lag,k:kk-1})
                require(actual==factored,f'conjugated third lag {(nn,kk)}')
                comparisons+=1
    emit(f'PASS gauge conjugation and cancellation identities; {comparisons} exact nonnegative squared-entry comparisons through n=36')

def load_formal(raw):
    exact_keys(raw,('D',),'formal')
    d=raw['D']; exact_keys(d,('f','sigma'),'formal/D')
    exact_list(d['f'],6,'formal profiles'); exact_list(d['sigma'],8,'formal sigma')
    profiles=[]
    for j,pair in enumerate(d['f']):
        exact_list(pair,2,f'formal f{j}')
        parsed=[expression(val,(x,k),f'formal f{j}/{c}',True) for c,val in enumerate(pair)]
        require(all(S.Poly(val,x).degree()<=2*j+2 for val in parsed),f'formal f{j}: degree')
        profiles.append(parsed)
    sigma=[expression(val,(k,),f'sigma{j}',True) for j,val in enumerate(d['sigma'])]
    require(profiles[0]==[S.S.One,S.S.Zero] and sigma[:3]==[S.S(2),S.S.Zero,k],'formal normalization')
    return profiles,sigma

def check_formal(raw,exact,regenerate=True):
    profiles,sigma=load_formal(raw)
    d=parse_exact(exact)
    for key,original in [('W',d['rotated']['left']),('D',-d['rotated']['lag'])]:
        eq(d['formal_rational'][key],original.subs({N:t**-3,h:x/t-1}),f'formal rational {key}')
    rhs=recurrence_rhs(profiles,sigma,'D',ORDER)
    for c in range(2):
        for degree in range(ORDER+1):
            lhs=sum(sigma[degree-j]*profiles[j][c] for j in range(len(profiles)) if 0<=degree-j<len(sigma))
            eq(rhs[c][degree],lhs,f'finished formal residual component {c}, t^{degree}')
    for j,(p,q) in enumerate(profiles):
        eq(q.subs(x,0),0,f'ghost boundary f{j}')
        if j: eq((p+S.diff(q,x)).subs(x,0),0,f'profile gauge f{j}')
    eq(sigma[3],S.Rational(29,12),'DFA sigma3')
    if regenerate:
        calculated,calcsigma=construct('D')
        for j,(found,wanted) in enumerate(zip(calculated,profiles)):
            for c in range(2): eq(found[c],wanted[c],f'independent construction f{j}/{c}')
        for j,(found,wanted) in enumerate(zip(calcsigma,sigma)):
            eq(found,wanted,f'independent construction sigma{j}')
        emit('PASS all five triangular and generic exact linear solves reproduce immutable profiles and sigma')
    # The polynomial operator is checked on a finite basis; the report proves arbitrary degree.
    for degree in range(13):
        monomial=x**degree
        image=S.diff(monomial,x,3)-4*(2*x+k)*S.diff(monomial,x)-4*monomial
        require(S.Poly(image,x).degree()<=degree,'polynomial operator triangularity')
        eq(S.expand(image).coeff(x,degree),-4*(2*degree+1),f'polynomial operator diagonal {degree}')
    emit('PASS finished Airy-pair recurrence: both components through t^7; all ghost/gauge conditions; operator basis degrees 0..12')
    return profiles,sigma

def load_endpoint(raw):
    exact_keys(raw,('D',),'endpoint')
    d=raw['D']; exact_keys(d,('log_correction','multiplicative','ratio'),'endpoint/D')
    result={}
    for name,length in [('log_correction',4),('multiplicative',5),('ratio',8)]:
        exact_list(d[name],length,f'endpoint/{name}')
        result[name]=[expression(val,(a,),f'endpoint/{name}/{j}',True) for j,val in enumerate(d[name])]
    return result

def check_endpoint(raw,formal):
    expected=load_endpoint(raw)
    profiles,sigma=load_formal(formal)
    E,logs,multiplicative=integrate_endpoint(profiles,sigma)
    ratios=ratio_from_log(logs,'D')
    other=direct_ratio(E,sigma)
    for group,computed in [('log_correction',logs),('multiplicative',multiplicative),('ratio',ratios)]:
        for j,(wanted,found) in enumerate(zip(expected[group],computed)):
            eq(found,wanted,f'endpoint {group}/{j}')
    for j,(first,second) in enumerate(zip(ratios,other)):
        eq(first,second,f'direct discrete-carrier ratio/{j}')
    eq(S.Rational(29,24)-S.Rational(1,3),S.Rational(7,8),'endpoint exponent')
    emit('PASS carrier discrete integration; endpoint log/multiplicative through n^(-4/3); independent ratio through n^(-7/3)')
    return expected

def check_inverse(raw,endpoint):
    exact_keys(raw,('schema','endpoint_log_power','stirling_log_power','combined_log_power','first_log_correction',
        'newton_error_X_exponent','newton_error_L_exponent','second_correction','tested_J_range'),'inverse')
    require(type(raw['schema']) is int and raw['schema']==1,'inverse schema')
    eq(expression(raw['endpoint_log_power'],(),'endpoint power'),S.Rational(7,8),'inverse endpoint power')
    eq(expression(raw['stirling_log_power'],(),'Stirling power'),S.Rational(1,2),'inverse Stirling power')
    q=expression(raw['combined_log_power'],(),'combined power')
    eq(q,S.Rational(7,8)+S.Rational(1,2),'inverse combined power')
    d1=expression(raw['first_log_correction'],(a,),'inverse d1',True)
    eq(d1,load_endpoint(endpoint)['log_correction'][0],'inverse d1 transcription')
    # These labels state the general exponent law. Exact evaluations below test it.
    require(raw['newton_error_X_exponent']=='1-2**(k+1)/3','Newton X exponent transcription')
    require(raw['newton_error_L_exponent']=='1-2**(k+1)','Newton L exponent transcription')
    exact_list(raw['tested_J_range'],2,'inverse J range')
    require(raw['tested_J_range']==[0,128],'inverse tested range changed')
    correction=expression(raw['second_correction'],(a,L),'second inverse correction')
    # At order X^(-1/3), h0=-3a X^(1/3)/L. The quadratic G0 term,
    # derivative of 3a X^(1/3), d1 term and L*h1 must cancel exactly.
    eq(L*correction+d1-3*a*a/L+S.Rational(9,2)*a*a/L**2,0,'inverse second-correction Taylor residual')
    for J in range(129):
        # K = ceil(log2(J+4))-1, computed using integer bit_length.
        K=(J+3).bit_length()-1
        require(2**(K+1)>=J+4,'Newton K exponent insufficient')
        require(K==0 or 2**K<J+4,'Newton K not minimal')
        rX,rL=F(1,3),-1
        for step in range(K+1):
            require(rX==1-F(2**(step+1),3) and rL==1-2**(step+1),'Newton exponent recurrence')
            rX,rL=2*rX-1,2*rL-1
        require(1-F(2**(K+1),3)<=-F(J+1,3),'Newton final power target')
        R=max(0,(J+3)//6)
        require(2*R+1>=F(J+1,3),'Stirling remainder power target')
        require(R==0 or 2*(R-1)+1<F(J+1,3),'Stirling truncation not minimal')
    # Formal leading inverse: W*exp(W)=8Y/e implies X=Y/W and
    # log(8X)=W+1, so X(log(8X)-1)=Y. This is an identity, not
    # a numerical or interval evaluation of Lambert W.
    X,Y,W=S.symbols('X Y W',nonzero=True)
    eq((X*(L-1)).subs({X:Y/W,L:W+1}),Y,'Lambert leading inverse algebra')
    positiveX=S.Symbol('positiveX',positive=True)
    ds=load_endpoint(endpoint)['log_correction']
    Fj=S.loggamma(positiveX+1)+positiveX*S.log(8)+3*a*positiveX**S.Rational(1,3)+S.Rational(7,8)*S.log(positiveX)+sum(v*positiveX**(-S.Rational(j,3)) for j,v in enumerate(ds,1))
    expected_derivative=S.polygamma(0,positiveX+1)+S.log(8)+a*positiveX**(-S.Rational(2,3))+S.Rational(7,8)/positiveX-sum(S.Rational(j,3)*v*positiveX**(-S.Rational(j,3)-1) for j,v in enumerate(ds,1))
    eq(S.diff(Fj,positiveX),expected_derivative,'inverse F_J derivative through J=4')
    emit('PASS inverse transcription: 11/8 logarithmic power, d1, second Taylor correction, Lambert identity; Newton/Stirling inequalities J=0..128')

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--section',choices=('all','integrity','exact','formal','endpoint','inverse'),default='all')
    args=parser.parse_args()
    emit(f'Python {platform.python_version()}, SymPy {S.__version__}, optimize={sys.flags.optimize}')
    require(S.__version__=='1.14.0','unsupported SymPy version; install requirements.txt')
    data=load_all()
    check_dependencies(data['dependencies.json'])
    if args.section in ('all','exact'):
        d,e=check_triangle(data['exact.json'])
        check_elimination(data['exact.json'],e)
        check_gauge(data['exact.json'])
    if args.section in ('all','formal'):
        check_formal(data['formal_7.json'],data['exact.json'])
    if args.section in ('all','endpoint'):
        check_endpoint(data['endpoint_7.json'],data['formal_7.json'])
    if args.section in ('all','inverse'):
        check_inverse(data['inverse.json'],data['endpoint_7.json'])
    emit('PASS requested finite exact checks. These checks do not prove analytic estimates or the asymptotic/inverse theorems.')

if __name__=='__main__':
    try:
        main()
    except (VerificationError,OSError) as error:
        print(f'FAIL: {error}',file=sys.stderr,flush=True)
        sys.exit(1)
