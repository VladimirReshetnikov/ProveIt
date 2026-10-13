"""Verify consequences of the separately certified order-15 algebraic point.

The companion check_stieltjes_order15.py establishes the algebraic point.
This checker imports only its safe parsing and normalization helpers. It
independently reconstructs adjacent tails by the Cayley recurrence, proves
the real Jacobian sign with rational intervals, and checks finite logarithmic
coefficient identities. No mathematical check is disabled by python -O.
"""
from pathlib import Path
import argparse
import hashlib
import importlib.util
import json
import platform
import sys
import time
import sympy as s

HERE=Path(__file__).resolve().parent
b,t,X,Y,z=s.symbols('b t X Y z',real=True)

def require(condition,message):
    if not bool(condition):raise ValueError(message)

def normalized_hash(path):
    return hashlib.sha256(path.read_text(encoding='utf-8').replace('\r\n','\n').encode('utf-8')).hexdigest()

def add(U,V):return U[0]+V[0],U[1]+V[1]
def mul(U,V):
    terms=[u*v for u in U for v in V]
    return min(terms),max(terms)
def horner(expr,var,iv):
    v=(s.Rational(0),s.Rational(0))
    for c in s.Poly(expr,var).all_coeffs():v=add(mul(v,iv),(c,c))
    return v

def verify(data,source):
    source.exact_keys(data,source.ROOT_KEYS,'Certificate')
    require(data['schema_version']==1 and data['order']==15 and data['scope']==source.SCOPE,
            'Unexpected certificate schema/order/scope')
    polys={key:source.rational_polynomial(data[key],(Y,) if key in ('P','N','D') else (X,Y))
           for key in source.POLYNOMIAL_KEYS}
    intervals={key:source.read_interval(data[key],key) for key in source.INTERVAL_KEYS}
    source.exact_keys(data['adjacent_tails'],('14','16'),'Adjacent tails')
    adjacent={}
    for k,row in data['adjacent_tails'].items():
        source.exact_keys(row,('R_interval','I_interval'),'Adjacent tail '+k)
        adjacent[k]={key:source.read_interval(iv,'Adjacent '+k+' '+key) for key,iv in row.items()}
    normalized={'schema_version':1,'order':15,'scope':source.SCOPE,
                'polynomials':{key:source.normalized_polynomial(poly) for key,poly in polys.items()},
                'intervals':{key:list(map(str,iv)) for key,iv in intervals.items()},
                'adjacent_tails':{k:{key:list(map(str,iv)) for key,iv in row.items()}
                                  for k,row in adjacent.items()}}
    checks=[]
    def check(name,condition):
        require(condition,name)
        checks.append({'name':name,'pass':True})
    xbox,ybox=intervals['X_enclosure'],intervals['Y_enclosure']
    def evalxy(expr):
        val=(s.Rational(0),s.Rational(0))
        for c in s.Poly(expr,X).all_coeffs():val=add(mul(val,xbox),horner(c,Y,ybox))
        return val
    def even_sub(expr):
        p=s.Poly(s.expand(expr),b,t)
        require(all(i%2==j%2==0 for (i,j),c in p.terms()),'Invalid even polynomial parity')
        return sum(c*X**(i//2)*Y**(j//2) for (i,j),c in p.terms())
    B=s.Integer(1)
    reconstructed={}
    for k in range(17):
        if k in (14,16):
            R,I=even_sub(s.re(B)),even_sub(s.im(B)/(b*t))
            reconstructed[k]=(evalxy(R),evalxy(I))
            for name,iv in zip(('R','I'),reconstructed[k]):
                stored=adjacent[str(k)][name+'_interval']
                check(f'Reconstructed {name}{k} enclosed by certificate bounds',
                      stored[0]<=iv[0]<=iv[1]<=stored[1])
        if k<16:B=s.expand((b+s.I*t/2)*B+s.I*(1+t*t)*s.diff(B,t)/2)
    R14,I14=reconstructed[14]
    R16,I16=reconstructed[16]
    scalar=add(mul(R14,R16),mul(mul(xbox,ybox),mul(I14,I16)))
    J=mul((s.Rational(15,4),s.Rational(15,4)),mul(add((1,1),ybox),scalar))
    check('Real Jacobian is strictly negative',J[1]<0)
    check('Readable rational Jacobian enclosure',-5*10**20<J[0]<J[1]<-4*10**20)

    coefficients=[]
    for q in range(1,16):
        E=s.Poly(s.prod(1+j*z for j in range(1,q+1)),z)
        e=[E.nth(r) for r in range(q+1)]
        H=lambda r:sum(s.Rational(1,n)**r for n in range(1,q+1))
        check(f'Alpha harmonic correction q={q}',
              sum((-1)**(r+1)*e[r]*H(r+1) for r in range(1,q+1))==H(1))
        check(f'Kappa initial finite terms vanish q={q}',
              sum((-1)**r*e[r]*H(r+2) for r in range(q+1))==0)
        # Formal independent extraction from the differentiated gamma quotient.
        # Z_r represents zeta(r), without relying on numerical identities.
        Z={r:s.Symbol(f'Z{r}') for r in range(2,q+3)}
        P=s.Poly(s.prod(1+z/s.Integer(j) for j in range(1,q+1)),z)
        def differentiated_coefficient(order):
            return s.factorial(order)*sum(P.nth(k)*(-1)**(order-k+1)*
                   (Z[order-k+1]-H(order-k+1)) for k in range(min(q,order-1)+1))
        alpha=sum((-1)**(r+1)*e[r]*Z[r+1] for r in range(1,q+1))-H(1)
        kappa=(q+1)*sum((-1)**r*e[r]*Z[r+2] for r in range(q+1))
        check(f'Formal gamma quotient alpha coefficient q={q}',
              s.expand(differentiated_coefficient(q)-alpha)==0)
        check(f'Formal gamma quotient kappa coefficient q={q}',
              s.expand(differentiated_coefficient(q+1)-kappa)==0)
        coefficients.append({'q':q,'kappa_zeta_2_through_q_plus_2':
                             [int((q+1)*(-1)**r*e[r]) for r in range(q+1)]})
    require(len(checks)==66,'Unexpected exact-check count')
    return {'status':'PASS','exact_check_count':len(checks),'checks':checks,
            'normalized_certificate_sha256':source.digest(normalized),
            'Jacobian_interval':[str(c) for c in J],
            'Jacobian_decimal_enclosure':[str(s.N(c,25)) for c in J],
            'coefficient_records':coefficients,
            'upstream_validation_required':'check_stieltjes_order15.py must separately establish the point and A15=0 for this normalized certificate.',
            'scope':'Local real transversality and finite formal coefficient checks; no all-order root classification or consecutive-tail exclusion.'}

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--certificate',type=Path,default=HERE/'stieltjes-order15-certificate.json')
    parser.add_argument('--output',type=Path,default=HERE/'stieltjes-order15-consequences.json')
    args=parser.parse_args()
    started=time.monotonic()
    companion=args.certificate.resolve().parent/'check_stieltjes_order15.py'
    metadata={'schema_version':1,'status':'RUNNING','python':platform.python_version(),
              'sympy':s.__version__,'python_optimization_level':sys.flags.optimize,
              'verifier_sha256_lf':normalized_hash(Path(__file__)),
              'certificate_file':args.certificate.name}
    try:
        require(args.output.resolve() not in (args.certificate.resolve(),Path(__file__).resolve(),companion),
                'Output must differ from input files')
        if args.output.exists():
            require(not any(args.output.samefile(p) for p in (args.certificate,Path(__file__),companion) if p.exists()),
                    'Output must not alias an input file')
    except ValueError as exc:
        print('FAIL:',exc,file=sys.stderr)
        return 1
    def write(value):args.output.write_text(json.dumps(value,indent=2)+'\n',encoding='utf-8')
    try:
        write(metadata)
        metadata['companion_parser_sha256_lf']=normalized_hash(companion)
        metadata['certificate_sha256_lf']=normalized_hash(args.certificate)
        sys.dont_write_bytecode=True
        spec=importlib.util.spec_from_file_location('order15_safe_parsing',companion)
        source=importlib.util.module_from_spec(spec)
        spec.loader.exec_module(source)
        result=verify(source.load_json(args.certificate.read_bytes()),source)
        write({**metadata,**result,'elapsed_seconds':round(time.monotonic()-started,3)})
        print('PASS:',result['exact_check_count'],'exact consequences checks;',
              'J in',result['Jacobian_decimal_enclosure'],flush=True)
        return 0
    except Exception as exc:
        failure={**metadata,'status':'FAIL','error':f'{type(exc).__name__}: {exc}'}
        write(failure)
        print('FAIL:',failure['error'],file=sys.stderr)
        return 1

if __name__=='__main__':sys.exit(main())
