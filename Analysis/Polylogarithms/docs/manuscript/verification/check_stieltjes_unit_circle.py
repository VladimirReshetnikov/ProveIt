"""Verify exact unit-circle colored-tail certificates for orders 1 through 8.

No Groebner computation and no numerical root approximation is used. The
certificate file is parsed as rational polynomial arithmetic, never evaluated
as Python. Run --extra-identities for two additional independent recurrence
families. This verifier makes no statement for higher orders or nonunit colors.
"""
from __future__ import annotations
import argparse
import ast
from copy import deepcopy
import hashlib
import json
from pathlib import Path
import platform
import sys
import sympy as sp

HERE = Path(__file__).resolve().parent
ORDER_BOUND = 8
X, Y, b, t, a, w = sp.symbols('X Y b t a w', real=True)

class VerificationError(ValueError):
    """A malformed certificate or failed exact identity."""

def require(condition, message):
    if not bool(condition):
        raise VerificationError(message)

def rational_polynomial(text, variables):
    require(isinstance(text, str) and len(text) <= 50000, 'Polynomial must be a bounded string')
    names = {str(v): v for v in variables}
    def parse(node):
        if isinstance(node, ast.Constant) and type(node.value) is int:
            return sp.Integer(node.value)
        if isinstance(node, ast.Name) and node.id in names:
            return names[node.id]
        if isinstance(node, ast.UnaryOp) and isinstance(node.op, (ast.UAdd, ast.USub)):
            operand = parse(node.operand)
            return operand if isinstance(node.op, ast.UAdd) else -operand
        if isinstance(node, ast.BinOp):
            left, right = parse(node.left), parse(node.right)
            if isinstance(node.op, ast.Add): return left + right
            if isinstance(node.op, ast.Sub): return left - right
            if isinstance(node.op, ast.Mult): return left * right
            if isinstance(node.op, ast.Div):
                require(right.is_Rational and right != 0, 'Only nonzero rational denominators are allowed')
                return left / right
            if isinstance(node.op, ast.Pow):
                require(right.is_Integer and 0 <= right <= 64, 'Polynomial exponent outside 0..64')
                return left ** int(right)
        raise VerificationError('Unsupported polynomial syntax')
    try:
        expression = parse(ast.parse(text, mode='eval').body)
        return sp.Poly(expression, *variables, domain=sp.QQ).as_expr()
    except VerificationError:
        raise
    except (SyntaxError, TypeError, ValueError, sp.PolynomialError) as exc:
        raise VerificationError(f'Invalid rational polynomial: {exc}') from exc

def exact_keys(record, keys, context):
    require(isinstance(record, dict) and set(record) == set(keys), f'{context}: wrong fields')

def verify_payload(data, extra_identities=False):
    exact_keys(data, ('schema_version', 'max_order', 'scope', 'polynomials', 'certificates'), 'root')
    require(data['schema_version'] == 1 and type(data['schema_version']) is int, 'Unsupported schema')
    require(data['max_order'] == ORDER_BOUND and type(data['max_order']) is int, 'Order bound must be exactly 8')
    require(data['scope'] == '1<=q<=8, a>0, abs(omega)=1, omega!=1; no higher-order claim', 'Unexpected declared scope')
    require(isinstance(data['polynomials'], list) and len(data['polynomials']) == 9, 'Expected exactly nine tail polynomials')
    require(isinstance(data['certificates'], list) and len(data['certificates']) == 8, 'Expected exactly eight order certificates')
    R, I = [], []
    for k, entry in enumerate(data['polynomials']):
        exact_keys(entry, ('k', 'R', 'I'), f'polynomial {k}')
        require(type(entry['k']) is int and entry['k'] == k, 'Tail indices must be exactly 0 through 8 in order')
        R.append(rational_polynomial(entry['R'], (X,Y)))
        I.append(rational_polynomial(entry['I'], (X,Y)))
    checks, extra = [], []
    def check(name, condition, destination=checks):
        require(condition, name)
        destination.append({'name': name, 'exact_residual': '0'})

    # This original-color recurrence is independent of the generator's
    # real Cayley-coordinate recurrence.
    P = [sp.Integer(1)]
    for k in range(ORDER_BOUND):
        P.append(sp.expand(w*(1-w)*sp.diff(P[-1],w)+(a+(k+1-a)*w)*P[-1]))
    B = []
    for k in range(ORDER_BOUND+1):
        poly = sp.Poly(P[k], w)
        normalized = sp.expand(sum(poly.coeff_monomial(w**j).subs(a,b+sp.Rational(1,2))
                     *(sp.I*t-1)**j*(sp.I*t+1)**(k-j) for j in range(k+1))/2**k)
        reconstructed = ((b if k%2 else 1)*R[k]
                         +sp.I*t*(b if k%2==0 else 1)*I[k]).subs({X:b*b,Y:t*t})
        B.append(sp.expand(reconstructed))
        check(f'Original-color normalization and parity k={k}', sp.expand(normalized-reconstructed)==0)

    for expected_q, entry in enumerate(data['certificates'], 1):
        exact_keys(entry, ('q', 'noncentral', 'central', 'alternating'), f'order {expected_q}')
        require(type(entry['q']) is int and entry['q'] == expected_q, 'Certificate orders must be exactly 1 through 8 in order')
        q = expected_q
        for kind, variables, polys, length in [
            ('noncentral',(X,Y),[R[q-1],I[q-1],R[q],I[q]],4),
            ('central',(Y,),[(R[j] if j%2==0 else I[j]).subs(X,0) for j in (q-1,q)],2)]:
            item = entry[kind]
            exact_keys(item, ('multipliers','degree_bound'), f'{kind} q={q}')
            require(isinstance(item['multipliers'],list) and len(item['multipliers'])==length,
                    f'{kind} q={q}: wrong multiplier count')
            require(type(item['degree_bound']) is int and item['degree_bound'] >= 0,
                    f'{kind} q={q}: invalid degree bound')
            multipliers = [rational_polynomial(v, variables) for v in item['multipliers']]
            require(all(sp.Poly(v,*variables).total_degree() <= item['degree_bound'] for v in multipliers),
                    f'{kind} q={q}: multiplier exceeds declared degree')
            check(f'Unit polynomial identity q={q} case={kind}',
                  sp.expand(sum(c*p for c,p in zip(multipliers,polys))-1)==0)
        alt=entry['alternating']
        exact_keys(alt, ('gcd','multipliers'), f'alternating q={q}')
        require(isinstance(alt['multipliers'],list) and len(alt['multipliers'])==2,
                f'alternating q={q}: wrong multiplier count')
        g=rational_polynomial(alt['gcd'],(a,))
        expected_g = a*a-a-1 if q==5 else sp.Integer(1)
        require(sp.expand(g-expected_g)==0, f'alternating q={q}: unexpected claimed gcd')
        m0,m1=[rational_polynomial(v,(a,)) for v in alt['multipliers']]
        e0,e1=sp.euler(q-1,a),sp.euler(q,a)
        check(f'Euler Bezout identity q={q}', sp.expand(m0*e0+m1*e1-g)==0)
        check(f'Euler common divisibility q={q}', sp.rem(e0,g,a)==0 and sp.rem(e1,g,a)==0)
    require(len(checks)==41, 'Unexpected base identity count')

    if extra_identities:
        for q in range(1,ORDER_BOUND+1):
            check(f'Shift derivative d_a A_q=q A_(q-1), q={q}',
                  sp.expand(sp.diff(P[q],a)-q*(1-w)*P[q-1])==0, extra)
        for k in range(ORDER_BOUND):
            check(f'Real parity recurrence k={k}',
                  sp.expand(B[k+1]-(b+sp.I*t/2)*B[k]-sp.I*(1+t*t)*sp.diff(B[k],t)/2)==0, extra)
    return checks, extra

def negative_controls(data):
    controls=[]
    def corrupt(name, mutate):
        candidate=deepcopy(data)
        mutate(candidate)
        try:
            verify_payload(candidate)
        except VerificationError as exc:
            controls.append({'name':name,'rejected':True,'reason':str(exc)})
            return
        raise VerificationError(f'Corrupted certificate was accepted: {name}')
    def add_one(d,q,part,j):
        v=d['certificates'][q-1][part]['multipliers'][j]
        d['certificates'][q-1][part]['multipliers'][j]=f'({v})+1'
    corrupt('Alter a noncentral Bezout multiplier',lambda d:add_one(d,8,'noncentral',0))
    corrupt('Alter a central Bezout multiplier',lambda d:add_one(d,8,'central',0))
    corrupt('Alter the golden Euler Bezout multiplier',lambda d:add_one(d,5,'alternating',0))
    corrupt('Corrupt the odd imaginary parity polynomial',lambda d:d['polynomials'][1].__setitem__('I','-1/2'))
    corrupt('Drop order eight coverage',lambda d:d['certificates'].pop())
    corrupt('Duplicate an order label',lambda d:d['certificates'][7].__setitem__('q',7))
    corrupt('Append a silently ignored multiplier',lambda d:d['certificates'][7]['noncentral']['multipliers'].append('0'))
    corrupt('Replace the golden gcd by one',lambda d:d['certificates'][4]['alternating'].__setitem__('gcd','1'))
    corrupt('Inject a nonpolynomial expression',lambda d:d['polynomials'][1].__setitem__('R','sin(X)'))
    return controls

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--certificates',type=Path,default=HERE/'stieltjes-unit-circle-certificates.json')
    parser.add_argument('--output',type=Path,default=HERE/'stieltjes-unit-circle-verification.json')
    parser.add_argument('--extra-identities',action='store_true')
    args=parser.parse_args()
    require(args.certificates.resolve()!=args.output.resolve(),'Input and output must differ')
    meta={'schema_version':1,'status':'RUNNING','scope':'Only orders 1 through 8 on the unit circle, with a>0 and omega!=1',
          'python':platform.python_version(),'sympy':sp.__version__,
          'certificate_file':args.certificates.name,
          'digest_mode':'lf-normalized',
          'verifier_sha256':hashlib.sha256(Path(__file__).read_bytes().replace(b'\r\n',b'\n')).hexdigest()}
    args.output.write_text(json.dumps(meta,indent=2)+'\n',encoding='utf-8')
    try:
        raw=args.certificates.read_bytes()
        data=json.loads(raw)
        checks,extra=verify_payload(data,args.extra_identities)
        controls=negative_controls(data)
        result={**meta,'status':'PASS','certificate_sha256':hashlib.sha256(raw.replace(b'\r\n',b'\n')).hexdigest(),
                'base_identity_count':len(checks),'extra_identity_count':len(extra),
                'negative_control_count':len(controls),'base_identities':checks,
                'extra_identities':extra,'negative_controls':controls,
                'classification':{'q':5,'omega':'-1','a':'(1+sqrt(5))/2'},
                'limitations':'Exact finite polynomial certificates and the stated case reduction; no theorem for q>8, nonunit colors, or numerical arithmetic independence.'}
        args.output.write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
        print(f"PASS: {len(checks)} base identities, {len(extra)} extra identities, {len(controls)} rejected corruptions")
        return 0
    except Exception as exc:
        args.output.write_text(json.dumps({**meta,'status':'FAIL','error':str(exc)},indent=2)+'\n',encoding='utf-8')
        print(f'FAIL: {exc}',file=sys.stderr)
        return 1

if __name__=='__main__':
    sys.exit(main())
