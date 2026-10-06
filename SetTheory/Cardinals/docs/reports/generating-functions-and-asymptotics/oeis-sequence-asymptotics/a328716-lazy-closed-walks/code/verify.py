#!/usr/bin/env python3
"""Verify Report179 using only the Python standard library (works with -S)."""
import argparse
import ast
from decimal import Decimal as D, localcontext
from fractions import Fraction as F
import hashlib
import json
from math import factorial
from pathlib import Path
import re
import sys
sys.dont_write_bytecode = True
HERE = Path(__file__).absolute().parent
ROOT = HERE.parent
sys.path.insert(0, str(ROOT))
sys.path.insert(0, str(HERE))
import verify_manifest as files
from exact import (P, B, V, J, need, cumulants_riccati, cumulants_raw_ode,
                   corrections_partition, corrections_exponential, integer_rows,
                   zero_counts, count_riccati, positive_rows, joint_counts)

KNOWN = [1,1,5,19,217,1451,26041,249705,6116209,76432627,2373097921,36562658573,1374991573825,25188442156333,1112491608614933,23620069750701091,1198207214200181217,28930659427538020915,1657461085278025906081,44848606508761385855085]
CHECK_N = list(range(42)) + [60,61,80,81,120,121,160,161,200,201]
JOINT_N = [0,1,2,3,20,21,60,61,120,121]
# Immutable pins protect the bundled numerical-reference/provenance objects.
PINS = {'data/walk_checks.json': '26c58eda9dfb99cc934a244248e1c026e0b26d91cfe98e5040d410228d2f9f03', 'data/independent_checks.json': 'c2469ad3ad9cb3eb0ae3ca163255b24b2a3ef6da57f01c180b52870f4437d3eb', 'data/PROVENANCE.json': '6e0e1a5f4389018a153e1a80fae6165af735b316cff911d37058edf20e9447e8'}


def canonical(value):
    return json.dumps(value, sort_keys=True, indent=2, ensure_ascii=True, allow_nan=False)+'\n'


def same(actual, expected, label='certificate'):
    need(canonical(actual) == canonical(expected), label+' differs from exact regeneration')


def read(path):
    path = Path(path).absolute()
    files.check_directory(path.parent)
    return files.read_regular(path)


def load_certificate(path):
    return files.load_json(read(path).decode('utf-8'))


def expression(text):
    """Parse a small arithmetic expression; never eval or execute source text."""
    names = {'b': B, 'v': V, 'j': J}
    def convert(node):
        if isinstance(node, ast.Constant) and type(node.value) is int:
            return P(node.value)
        if isinstance(node, ast.Name) and node.id in names:
            return names[node.id]
        if isinstance(node, ast.UnaryOp) and isinstance(node.op, (ast.USub, ast.UAdd)):
            value = convert(node.operand)
            return -value if isinstance(node.op, ast.USub) else value
        if isinstance(node, ast.BinOp):
            left = convert(node.left)
            if isinstance(node.op, ast.Pow):
                need(isinstance(node.right, ast.Constant) and type(node.right.value) is int
                     and 0 <= node.right.value <= 64, 'unsafe exponent')
                return left**node.right.value
            right = convert(node.right)
            if isinstance(node.op, ast.Add): return left+right
            if isinstance(node.op, ast.Sub): return left-right
            if isinstance(node.op, ast.Mult): return left*right
            if isinstance(node.op, ast.Div): return left/right
        raise ValueError('unsupported expression syntax')
    need(isinstance(text, str) and len(text) < 10000, 'invalid expression')
    return convert(ast.parse(text, mode='eval').body)


def references():
    result = {}
    for name, digest in sorted(PINS.items()):
        raw = read(ROOT/name)
        need(hashlib.sha256(raw).hexdigest() == digest, 'reference SHA-256 mismatch: '+name)
        result[name] = files.load_json(raw.decode('utf-8'))
    return result


def polynomial_value(poly, b, v):
    total = D(0)
    for (eb, ev, ej, ey), coefficient in poly.d.items():
        need(ej == ey == 0, 'unsubstituted variable')
        total += D(coefficient.numerator)/D(coefficient.denominator)*b**eb*v**ev
    return total


def bessel(r):
    x, term, total, derivative, j = r*r, D(1), D(1), D(0), 0
    while True:
        j += 1
        term *= x/D(j*j)
        total += term
        derivative += 2*j*term
        if abs(term) < D('1e-100'):
            return total, derivative/total


def close(actual, expected, tolerance, label):
    need(abs(actual-D(expected)) < D(tolerance), 'numeric diagnostic differs: '+label)


def numeric_checks(rows, coefficients, source):
    """85-digit Decimal diagnostics. These are not interval/error certificates."""
    with localcontext() as ctx:
        ctx.prec = 85
        lo, hi = D('0.8'), D('0.81')
        for _ in range(290):
            r = (lo+hi)/2
            if bessel(r)[1] < 1: lo = r
            else: hi = r
        r = (lo+hi)/2
        f, saddle_mean = bessel(r)
        b, d = 4*r*r-1, f/(D(1).exp()*r)
        q, p = 1/f, 1-1/f
        tau = p*q-q*q/b
        close(saddle_mean, '1', '1e-82', 'saddle equation')
        for name,value in [('r',r),('b',b),('d',d)]:
            close(value,source[name],'1e-65',name)
        close(p,source['used_fraction'],'1e-38','occupation density')
        close(tau,source['used_variance'],'1e-38','variance density')
        C, vv, c = {}, {}, {}
        for parity in (0,1):
            eps = (-1)**parity
            E = r.exp()+eps*(-r).exp()
            C[parity] = E/b.sqrt()
            vv[parity] = r*(r.exp()-eps*(-r).exp())/E
            c[parity] = [polynomial_value(poly,b,vv[parity]) for poly in coefficients]
            close(C[parity],source['C'][str(parity)],'1e-65','C parity '+str(parity))
            for k in range(4):
                close(c[parity][k],source['c_numeric'][str(parity)][k],'1e-43','c'+str(k))
        diagnostics = []
        for record in source['checks']:
            n = record['n']; parity = n%2; eps = (-1)**parity; v = vv[parity]
            zeros = zero_counts(n, rows[n]); total = sum(zeros.values())
            ratio = D(total)/(C[parity]*(d*n)**n)
            errors = [(ratio-sum(c[parity][k]/D(n)**k for k in range(L+1)))*D(n)**(L+1) for L in range(4)]
            close(ratio,record['ratio'],'1e-28','count ratio')
            for actual,expected in zip(errors,record['n_scaled_errors']):
                close(actual,expected,'1e-25','scaled count error')
            def total_dim(dim): return sum(zero_counts(n,rows[dim]).values())
            empty1 = D(n*total_dim(n-1))/total
            empty2 = D(n*(n-1)*total_dim(n-2))/total
            mean, variance = n-empty1, empty2+empty1-empty1*empty1
            offset = -(q/b)*(v+(b-1)/2-1/b)
            close(mean/n,record['used_mean_over_n'],'1e-23','occupation mean')
            close(variance/n,record['used_variance_over_n'],'1e-23','occupation variance')
            close(offset,record['occupation_mean_offset'],'1e-23','occupation offset')
            close(n*(mean-n*p-offset),record['occupation_mean_scaled_remainder'],'1e-23','occupation remainder')
            tv, tv1 = D(0), D(0)
            E = r.exp()+eps*(-r).exp()
            for j in range(parity,n+101,2):
                probability = 2*r**j/(D(factorial(j))*E)
                actual = D(zeros.get(j,0))/total
                first = -(D(j*j)-r*r-v)/(2*b)+(D(j)-v)/(b*b)
                tv += abs(actual-probability)/2
                tv1 += abs(actual-probability*(1+first/n))/2
            close(n*tv,record['n_TV'],'1e-23','zero-step TV')
            close(n*n*tv1,record['n2_TV_first'],'1e-23','corrected TV')
            for pgf in record['pgf']:
                u = D(pgf['u'])
                actual = sum(D(ct)*u**j for j,ct in zeros.items())/total
                limit = ((r*u).exp()+eps*(-r*u).exp())/E
                close(n*(actual-limit),pgf['n_scaled_error'],'1e-23','marked PGF')
            diagnostics.append({'n':n,'scaled_errors':[format(x,'.20E') for x in errors],
                'n_TV':format(n*tv,'.20E'),'n2_TV_first':format(n*n*tv1,'.20E'),
                'occupation_mean_over_n':format(mean/n,'.20E'),
                'occupation_variance_over_n':format(variance/n,'.20E')})
        return {'precision_decimal_digits':85,'interval_certified':False,
                'r':format(r,'.60f'),'b':format(b,'.60f'),'d':format(d,'.60f'),
                'count_and_distribution_diagnostics':diagnostics}


def derive():
    refs = references()
    source = refs['data/walk_checks.json']
    kap = cumulants_riccati(8)
    need(kap == cumulants_raw_ode(8), 'independent cumulants disagree')
    c = corrections_partition(3,kap)
    independent, Q = corrections_exponential(3,cumulants_raw_ode(8))
    need(c == independent,'independent correction algorithms disagree')
    need(c[1] == (9-7*B)/(24*B)-P(F(5,6))/B**3+(2-B)*V/(2*B**2),'closed c1')
    need(c[2] == expression('(193*b**6+312*b**5*v-594*b**5-2856*b**4*v+1245*b**4+4368*b**3*v+1624*b**3+3360*b**2*v-6552*b**2-6720*b*v+6160)/(1152*b**6)'), 'closed c2')
    need(Q[1] == -(J**2-(B+1)/4-V)/(2*B)+(J-V)/B**2,'closed Q1')
    need(len(source['c_symbolic']) == 4 and len(source['cumulants']) == 8, 'reference order')
    for k in range(4): need(c[k] == expression(source['c_symbolic'][k]),'reference correction c'+str(k))
    for k in range(1,9): need(kap[k] == expression(source['cumulants'][k-1]),'reference cumulant '+str(k))
    audit = refs['data/independent_checks.json']
    need(len(audit['probability_Q1_through_Q3']) == 3,'reference probability order')
    for k in range(1,4): need(Q[k] == expression(audit['probability_Q1_through_Q3'][k-1]),'reference Q'+str(k))
    rows = integer_rows(max(CHECK_N))
    counts = []
    for n in CHECK_N:
        total = sum(zero_counts(n,rows[n]).values())
        need(total == count_riccati(n),'independent exact count n='+str(n))
        if n < len(KNOWN): need(total == KNOWN[n],'OEIS term n='+str(n))
        counts.append({'n':n,'count':total})
    positive = positive_rows(max(JOINT_N)//2)
    joints = []
    for n in JOINT_N:
        cells = joint_counts(n,positive)
        zero = {}
        for j,k,count in cells:
            zero[j] = zero.get(j,0)+count
        need(zero == zero_counts(n,rows[n]),'joint zero marginal n='+str(n))
        total = sum(ct for j,k,ct in cells)
        mean = F(sum(k*ct for j,k,ct in cells),total)
        second = F(sum(k*k*ct for j,k,ct in cells),total)
        if n >= 2:
            e1 = F(n*sum(zero_counts(n,rows[n-1]).values()),total)
            e2 = F(n*(n-1)*sum(zero_counts(n,rows[n-2]).values()),total)
            need(mean == n-e1 and second-mean*mean == e2+e1-e1*e1,'dimension-deletion moments')
        joints.append({'n':n,'nonzero_cells':len(cells),'total':total,
                       'occupation_mean':str(mean),'occupation_variance':str(second-mean*mean)})
    return {'schema_version':1,'report':179,'oeis':'A328716',
            'ring_variables':['b','v','j','y'],
            'scope':{'exact_order_checked':3,'cumulants_checked':8,
                     'asymptotic_proof_is_in_manuscript':True,
                     'numerical_remainder_bounds_certified':False},
            'oeis_terms':KNOWN,'count_cases':counts,'joint_cases':joints,
            'cumulants':[poly.serial() for poly in kap[1:]],
            'relative_coefficients':[poly.serial() for poly in c],
            'probability_coefficients':[poly.serial() for poly in Q],
            'reference_sha256':PINS,
            'numerical_diagnostics':numeric_checks(rows,c,source)}


def manuscript_prefix(path):
    text = read(path).decode('utf-8')
    begin, end = '% BEGIN VERIFIED OEIS PREFIX', '% END VERIFIED OEIS PREFIX'
    need(text.count(begin) == text.count(end) == 1, 'prefix marker count')
    need(text.index(begin)<text.index(end),'prefix marker order')
    body = text.split(begin,1)[1].split(end,1)[0].strip()
    need(body.startswith(r'\[') and body.endswith(r'\]'),'prefix display delimiters')
    body = body[2:-2]
    # Only decimal integer tokens, commas, whitespace, alignment markers and
    # the exact gathered environment are allowed. Macros/expressions are rejected.
    body = body.replace(r'\begin{gathered}','').replace(r'\end{gathered}','')
    body = body.replace(r'\\','').replace('&','').strip()
    if body.endswith('.'):
        body = body[:-1]  # optional final sentence punctuation, never a decimal
    need(re.fullmatch(r'\s*[0-9]+(?:\s*,\s*[0-9]+)*\s*,?\s*',body) is not None,
         'nonliteral OEIS prefix')
    actual = [int(s.strip()) for s in body.strip().rstrip(',').split(',')]
    need(actual == KNOWN,'manuscript OEIS prefix differs')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--data',type=Path,default=ROOT/'data/certificates.json')
    parser.add_argument('--manuscript',type=Path,default=ROOT/'Report179.tex')
    args = parser.parse_args()
    stored = load_certificate(args.data)
    manuscript_prefix(args.manuscript)
    computed = derive()
    same(stored,computed)
    print(json.dumps({'status':'PASS','report':179,'all_checks_passed':True,
        'standard_library_only':True,'oeis_terms_checked':20,
        'independent_exact_count_cases':len(CHECK_N),'largest_exact_n':max(CHECK_N),
        'independent_joint_cases':len(JOINT_N),'cumulants_checked':8,
        'relative_and_probability_corrections_checked_through':3,
        'numerical_diagnostic_cases':8,'reference_hashes_checked':len(PINS),
        'numerical_error_bounds_certified':False},sort_keys=True))

if __name__ == '__main__':
    try: main()
    except (ValueError,TypeError,KeyError,IndexError,OSError,SyntaxError) as exc:
        print('VERIFICATION FAILED: '+str(exc),file=sys.stderr)
        sys.exit(1)
