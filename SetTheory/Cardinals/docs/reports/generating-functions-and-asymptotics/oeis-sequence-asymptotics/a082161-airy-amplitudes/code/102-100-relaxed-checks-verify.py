#!/usr/bin/env python3
"""Fail-closed finite exact checks; this program does not prove asymptotics."""
import argparse
import ast
from fractions import Fraction as F
import hashlib
import json
from math import factorial
from pathlib import Path
import platform
import re
import sys
import time
import sympy as S
from formal_engine import (VerificationError, require, zero, x, k, t, a, ORDER,
    recurrence_rhs, derivative, construct, integrate_endpoint, direct_ratio, ratio_from_log)

ROOT = Path(__file__).resolve().parent
MAX_N = 30
DATA_NAMES = ('formal_9.json','formal_9_linear_solver.json','endpoint_9.json')
SOURCE_FILES = frozenset({
    'README.md','requirements.txt','verify.py','formal_engine.py','negative_tests.py',
    'data/formal_9.json','data/formal_9_linear_solver.json','data/endpoint_9.json',
    'diagnostics/README.md','diagnostics/exact_dp_3000.json','diagnostics/numerical_analysis.json',
    'provenance/source_hashes.json',
})

def unique_object(pairs):
    obj = {}
    for key,value in pairs:
        require(key not in obj, f'duplicate JSON key: {key}')
        obj[key] = value
    return obj

def read_json(path):
    try:
        return json.loads(path.read_text(encoding='utf-8'),object_pairs_hook=unique_object,
                          parse_constant=lambda value: (_ for _ in ()).throw(VerificationError(f'nonfinite JSON value: {value}')))
    except (OSError,UnicodeError,json.JSONDecodeError) as error:
        raise VerificationError(f'cannot read valid JSON: {path.name}: {error}') from error

def exact_keys(obj,keys,label):
    require(type(obj) is dict and set(obj)==set(keys),f'{label}: expected exactly keys {sorted(keys)}')

def exact_list(obj,size,label):
    require(type(obj) is list and len(obj)==size,f'{label}: expected exactly {size} indexed entries')

def polynomial(text,symbols,label):
    require(type(text) is str and 0<len(text)<=100000,f'{label}: nonempty polynomial string required')
    names = {str(symbol):symbol for symbol in symbols}
    try:
        tree = ast.parse(text,mode='eval')
    except (SyntaxError,ValueError,RecursionError) as error:
        raise VerificationError(f'{label}: invalid expression syntax') from error
    require(sum(1 for _ in ast.walk(tree))<=20000,f'{label}: expression too large')
    def convert(node):
        if isinstance(node,ast.Constant) and type(node.value) is int:
            return S.Integer(node.value)
        if isinstance(node,ast.Name) and node.id in names:
            return names[node.id]
        if isinstance(node,ast.UnaryOp) and isinstance(node.op,(ast.UAdd,ast.USub)):
            val = convert(node.operand)
            return val if isinstance(node.op,ast.UAdd) else -val
        if isinstance(node,ast.BinOp) and isinstance(node.op,(ast.Add,ast.Sub,ast.Mult,ast.Div,ast.Pow)):
            left,right = convert(node.left),convert(node.right)
            if isinstance(node.op,ast.Add): return left+right
            if isinstance(node.op,ast.Sub): return left-right
            if isinstance(node.op,ast.Mult): return left*right
            if isinstance(node.op,ast.Div):
                require(right.is_Rational is True and right!=0,f'{label}: denominator must be a nonzero rational constant')
                return left/right
            require(right.is_Integer is True and 0<=right<=64,f'{label}: exponent must be an integer in 0..64')
            return left**right
        raise VerificationError(f'{label}: unsupported expression syntax')
    try:
        expr = convert(tree.body)
        poly = S.Poly(expr,*symbols,domain=S.QQ)
    except (S.PolynomialError,S.CoercionFailed,TypeError,ValueError,RecursionError) as error:
        raise VerificationError(f'{label}: not an exact rational polynomial') from error
    require(poly.total_degree()<=64,f'{label}: polynomial degree exceeds supported bound')
    return poly.as_expr()

def load_formal(path):
    raw = read_json(path)
    exact_keys(raw,('R','C'),path.name)
    out = {}
    for kind in ('R','C'):
        data = raw[kind]
        exact_keys(data,('f','sigma'),f'{path.name}/{kind}')
        exact_list(data['f'],8,f'{path.name}/{kind}/f')
        exact_list(data['sigma'],10,f'{path.name}/{kind}/sigma')
        profiles=[]
        for j,pair in enumerate(data['f']):
            exact_list(pair,2,f'{path.name}/{kind}/f/{j}')
            parsed=[polynomial(value,(x,k),f'{path.name}/{kind}/f/{j}/{c}') for c,value in enumerate(pair)]
            require(all(S.Poly(value,x).degree()<=2*j+2 for value in parsed),f'{path.name}/{kind}/f/{j}: degree bound')
            profiles.append(parsed)
        sigma=[polynomial(value,(k,),f'{path.name}/{kind}/sigma/{j}') for j,value in enumerate(data['sigma'])]
        require(profiles[0]==[S.S.One,S.S.Zero],f'{path.name}/{kind}: f0 normalization')
        require(sigma[:3]==[S.S(2),S.S.Zero,k],f'{path.name}/{kind}: sigma0..2 normalization')
        out[kind]=(profiles,sigma)
    return out

def load_endpoint(path):
    raw = read_json(path)
    exact_keys(raw,('R','C'),path.name)
    out = {}
    for kind in ('R','C'):
        exact_keys(raw[kind],('log_correction','multiplicative','ratio'),f'{path.name}/{kind}')
        out[kind]={}
        for key,size in (('log_correction',6),('multiplicative',7),('ratio',10)):
            values=raw[kind][key]
            exact_list(values,size,f'{path.name}/{kind}/{key}')
            out[kind][key]=[polynomial(value,(a,),f'{path.name}/{kind}/{key}/{j}') for j,value in enumerate(values)]
        require(out[kind]['multiplicative'][0]==1,f'{path.name}/{kind}: multiplicative constant')
        require(out[kind]['ratio'][:3]==[S.S.One,S.S.Zero,a],f'{path.name}/{kind}: ratio0..2 normalization')
    return out

def check_integrity(root):
    require({p.name for p in root.glob('*.py')}=={'verify.py','formal_engine.py','negative_tests.py'},'executable source inventory mismatch')
    manifest = read_json(root/'manifest.json')
    exact_keys(manifest,('schema','algorithm','files'),'manifest')
    require(type(manifest['schema']) is int and manifest['schema']==1,'unsupported manifest schema')
    require(manifest['algorithm']=='sha256','unsupported manifest algorithm')
    exact_keys(manifest['files'],SOURCE_FILES,'manifest file inventory')
    for relative in sorted(SOURCE_FILES):
        record=manifest['files'][relative]
        exact_keys(record,('bytes','sha256'),f'manifest/{relative}')
        require(type(record['bytes']) is int and record['bytes']>=0,f'manifest/{relative}: byte count')
        require(type(record['sha256']) is str and re.fullmatch('[0-9a-f]{64}',record['sha256']) is not None,f'manifest/{relative}: SHA-256 syntax')
        path=root/relative
        require(path.is_file() and not path.is_symlink(),f'manifest/{relative}: missing or symlinked file')
        require(not any(parent.is_symlink() for parent in path.parents if parent!=root.parent),f'manifest/{relative}: symlinked parent')
        content=path.read_bytes()
        require(len(content)==record['bytes'],f'manifest/{relative}: byte count mismatch')
        require(hashlib.sha256(content).hexdigest()==record['sha256'],f'manifest/{relative}: SHA-256 mismatch')
    print(f'PASS integrity: exact inventory of {len(SOURCE_FILES)} source/data/documentation files; SHA-256 and sizes; manifest SHA-256={hashlib.sha256((root/"manifest.json").read_bytes()).hexdigest()}',flush=True)

def check_schema(root):
    data=root/'data'
    require(data.is_dir(),'missing data directory')
    require({p.name for p in data.iterdir()}==set(DATA_NAMES),'data directory inventory mismatch')
    formal=load_formal(data/'formal_9.json')
    linear=load_formal(data/'formal_9_linear_solver.json')
    endpoint=load_endpoint(data/'endpoint_9.json')
    print('PASS schema: R,C; f indices 0..7, pairs of length 2; sigma 0..9; endpoint log 1..6, multiplicative 0..6, ratio 0..9; exact rational polynomials only',flush=True)
    return formal,linear,endpoint

def check_algebra(max_n):
    require(type(max_n) is int and max_n==MAX_N,'algebra coverage must be exactly n=1..30')
    # All normalized meander states through time 60 require triangle rows through 60.
    R=[[0]*(2*max_n+1) for _ in range(2*max_n+1)]
    C=[[0]*(max_n+1) for _ in range(max_n+1)]
    for n in range(2*max_n+1):
        R[n][0]=1
        for m in range(1,n+1):
            R[n][m]=(m+1)*R[n-1][m]+R[n][m-1]
    for n in range(max_n+1):
        C[n][0]=1
        for m in range(1,n+1):
            C[n][m]=(m+1)*(C[n-1][m] if m<n else 0)+C[n][m-1]-(m-1)*(C[n-2][m-1] if n>=2 and m<n else 0)
    require([R[n][n] for n in range(10)]==[1,1,3,16,127,1363,18628,311250,6173791,142190703],'relaxed initial sequence')
    require([C[n][n] for n in range(10)]==[1,1,3,15,111,1119,14487,230943,4395855,97608831],'compacted initial sequence')
    def one_step(old,time):
        out=[F(0)]*(time+1)
        for h in range(time+1):
            if h and h-1<len(old): out[h]+=F(time-h+2,time+h)*old[h-1]
            if h+1<len(old): out[h]+=old[h+1]
        return out
    def apply_A(old,n):
        require(len(old)==n,'two-step input dimension')
        out=[]
        for j in range(n+1):
            if j==0:
                val=old[0]+(old[1] if n>1 else 0)
            else:
                val=F((n-j+1)**2,(n+j)*(n+j-1))*old[j-1]
                if j<n: val+=F(2*n-2*j+1,n+j)*old[j]
                if j+1<n: val+=old[j+1]
            out.append(val)
        return out
    D=[F(1)];E=[F(1)];Qprev=[F(1)]
    state_count=meander_count=operator_entries=0
    for n in range(1,max_n+1):
        for time_index in (2*n-1,2*n):
            D=one_step(D,time_index)
            for h,value in enumerate(D):
                if (time_index-h)%2:
                    require(value==0,f'meander parity at {time_index},{h}')
                else:
                    row,column=(time_index+h)//2,(time_index-h)//2
                    require(value==F(R[row][column],factorial(row)),f'meander/triangle at {time_index},{h}')
                    meander_count+=1
        current=[D[2*j] for j in range(n+1)]
        require(apply_A(E,n)==current,f'two-step actual vector at n={n}')
        require(current[0]==F(R[n][n],factorial(n)),f'diagonal at n={n}')
        # Equality of operators is tested on every input basis, not just on one orbit.
        for column in range(n):
            basis=[F(0)]*n;basis[column]=F(1)
            embedded=[F(0)]*(2*n-1)
            for j,value in enumerate(basis): embedded[2*j]=value
            product=one_step(one_step(embedded,2*n-1),2*n)
            require(apply_A(basis,n)==[product[2*j] for j in range(n+1)],f'two-step basis at n={n}, column={column}')
            operator_entries+=n+1
        Q=[F(factorial(n)**3*factorial(n-1),factorial(n-j)**2*factorial(n+j-1)*factorial(n+j)) for j in range(n+1)]
        require(Q[0]==1 and all(value>0 for value in Q),f'symmetrizer positivity at {n}')
        for j in range(n+1):
            diagonal=F(1) if j==0 else F(2*n-2*j+1,n+j)
            cdiag2=F(n-j,n+j) if j<n else F(0)
            csub2=F(n-j+1,n+j) if j>0 else F(0)
            require(cdiag2>=0 and csub2>=0,f'factor square sign at {n},{j}')
            require(cdiag2+csub2==diagonal,f'J=CC^T diagonal at {n},{j}')
            if j:
                lower=F((n-j+1)**2,(n+j)*(n+j-1))
                require(lower>0,f'positive Jacobi off-diagonal at {n},{j}')
                require(Q[j]/Q[j-1]==lower,f'symmetrizer edge at {n},{j}')
                require(lower**2*Q[j-1]/Q[j]==Q[j]/Q[j-1],f'conjugate upper/lower squares at {n},{j}')
                require(F(n-j+1,n+j-1)*csub2==lower,f'J=CC^T edge square at {n},{j}')
            # The bidiagonal support implies all more distant Gram entries vanish.
            for other in range(j+2,n+1):
                row_support={c for c in (j-1,j) if 0<=c<n}
                other_support={c for c in (other-1,other) if 0<=c<n}
                require(row_support.isdisjoint(other_support),f'Gram off-band support at {n},{j},{other}')
            R2=Qprev[j]/Q[j] if j<n else F(0)
            if n>=2 and j<n:
                require(R2==F((n-j)**2*(n+j-1)*(n+j),n**3*(n-1)),f'R formula at {n},{j}')
            require(0<=R2<=1,f'R contraction at {n},{j}')
            if j==0: require(R2==1,f'R endpoint at {n}')
            if j==n: require(R2==0,f'R zero extension at {n}')
            state_count+=1
        E,Qprev=current,Q
    require(state_count==495 and meander_count==960 and operator_entries==9920,'incomplete exact algebra coverage')
    print('PASS algebra: n=1..30; 495 state-level Jacobi/symmetrizer/PSD-factor/R checks; 960 normalized meander states at times 1..60; 9920 two-step operator entries checked via all basis vectors',flush=True)
    print('Initial relaxed diagonal r_0..r_10: '+str([R[n][n] for n in range(11)]),flush=True)

def compare_endpoint_certificates(kind,logs,multiplicative,direct,from_log,recorded):
    count=0
    for label,values,size in (('log_correction',logs,6),('multiplicative',multiplicative,7),('ratio',direct,10)):
        exact_list(values,size,f'{kind}: generated endpoint {label}')
        exact_list(recorded[label],size,f'{kind}: recorded endpoint {label}')
        for j in range(size):
            require(zero(values[j]-recorded[label][j]),f'{kind}: endpoint {label} index {j}')
            count+=1
    exact_list(from_log,10,f'{kind}: generated ratio from log')
    for j in range(10):
        require(zero(direct[j]-from_log[j]),f'{kind}: independent ratio-from-log index {j}')
        count+=1
    require(count==33,f'{kind}: incomplete endpoint comparison')
    return count

def check_formal(formal,linear,endpoint,order):
    require(type(order) is int and order==ORDER,'formal coverage must be exactly order 9')
    recurrence_count=solver_count=endpoint_count=0
    for kind in ('R','C'):
        profiles,sigma=formal[kind]
        for j,pair in enumerate(profiles):
            require(zero(pair[1].subs(x,0)),f'{kind}: boundary at f{j}')
            if j:
                require(zero((pair[0]+S.diff(pair[1],x)).subs(x,0)),f'{kind}: derivative gauge at f{j}')
        rhs=recurrence_rhs(profiles,sigma,kind,order)
        for component in range(2):
            for power in range(order+1):
                lhs=sum(sigma[power-j]*profiles[j][component] for j in range(len(profiles)) if 0<=power-j<len(sigma))
                require(zero(rhs[component][power]-lhs),f'{kind}: recurrence residual component={component}, power={power}')
                recurrence_count+=1
        print(f'PASS {kind} recurrence: both polynomial components at every power 0..9; all boundaries and gauges',flush=True)
        generated_profiles,generated_sigma=construct(kind)
        for label,(other_profiles,other_sigma) in (('fresh two-solver reconstruction',(generated_profiles,generated_sigma)),('archived generic solution',linear[kind])):
            for j in range(8):
                for component in range(2):
                    require(zero(profiles[j][component]-other_profiles[j][component]),f'{kind}: {label}, f{j}/{component}')
                    solver_count+=1
            for j in range(10):
                require(zero(sigma[j]-other_sigma[j]),f'{kind}: {label}, sigma{j}')
                solver_count+=1
        print(f'PASS {kind} solvers: fresh triangular and generic exact linear solves at stages 3..9, agreeing with both archived tables',flush=True)
        E,logs,multiplicative=integrate_endpoint(profiles,sigma)
        direct=direct_ratio(E,sigma)
        from_log=ratio_from_log(logs,kind)
        endpoint_count+=compare_endpoint_certificates(kind,logs,multiplicative,direct,from_log,endpoint[kind])
        print(f'PASS {kind} endpoint: log corrections 1..6; multiplicative coefficients 0..6; direct two-step and integrated-log ratios 0..9',flush=True)
    require(recurrence_count==40 and solver_count==104 and endpoint_count==66,'incomplete formal/endpoint coverage')
    print('PASS coverage: 40 recurrence coefficient identities; 104 reconstructed/archive coefficient comparisons; 66 endpoint/ratio coefficient comparisons; 14 fresh triangular/generic stage comparisons',flush=True)

def fixed_n(text):
    if re.fullmatch(r'[0-9]+',text) is None or int(text)!=MAX_N:
        raise argparse.ArgumentTypeError('must be exactly 30; reduced or expanded coverage is not a certificate from this package')
    return MAX_N

def fixed_order(text):
    if re.fullmatch(r'[0-9]+',text) is None or int(text)!=ORDER:
        raise argparse.ArgumentTypeError('must be exactly 9; this package has fixed validated data indices')
    return ORDER

def main(argv=None):
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--mode',choices=('full','integrity','schema','algebra','formal'),default='full',help='partial modes report only their stated scope; default full runs every exact check')
    parser.add_argument('--max-n',type=fixed_n,default=MAX_N)
    parser.add_argument('--formal-order',type=fixed_order,default=ORDER)
    args=parser.parse_args(argv)
    start=time.monotonic()
    print(f'Environment: Python {platform.python_version()}; SymPy {S.__version__}; optimization={sys.flags.optimize}; mode={args.mode}',flush=True)
    check_integrity(ROOT)
    if args.mode!='integrity':
        formal,linear,endpoint=check_schema(ROOT)
        if args.mode in ('full','algebra'): check_algebra(args.max_n)
        if args.mode in ('full','formal'): check_formal(formal,linear,endpoint,args.formal_order)
    print(f'COMPLETE {args.mode}: elapsed {time.monotonic()-start:.3f}s',flush=True)
    print('Scope: finite exact algebra and formal coefficient identities only. No finite test proves amplitude convergence, all-orders asymptotic transfer, numerical amplitude digits, or exponentially small sectors.',flush=True)
    return 0

if __name__=='__main__':
    try:
        sys.exit(main())
    except VerificationError as error:
        print(f'FAIL: {error}',file=sys.stderr,flush=True)
        sys.exit(1)
