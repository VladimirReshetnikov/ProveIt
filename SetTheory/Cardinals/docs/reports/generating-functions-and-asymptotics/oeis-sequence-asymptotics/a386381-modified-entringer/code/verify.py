#!/usr/bin/env python3
"""Verify Report180 exactly with Python's standard library, including under -O."""
import argparse
import ast
from fractions import Fraction as F
import hashlib
import json
from math import factorial
from pathlib import Path
import re
import sys
sys.dont_write_bytecode=True
HERE=Path(__file__).absolute().parent
ROOT=HERE.parent
sys.path.insert(0,str(ROOT));sys.path.insert(0,str(HERE))
import verify_manifest as files
from exact import (P,LAM,X,need,integer_triangle,marked_triangle,euler_coefficients,
                   euler_by_trigonometry,ode_coefficients,frobenius,falling_corrections,
                   falling_corrections_independent,pgf_multipliers,sturm,rational_tails)

KNOWN=[1,1,1,2,8,56,640,10960,264640,8581760,360331520,19031302400,1235451750400,
       96722377139200,8988790940876800,978442125179648000,123324448870740377600,
       17820979140159760793600,2926936219425738642227200,542215853077506417192140800,
       112527512540808439576566169600]
PINS = {'data/references/checks.json': '8d1b4159d538a94a670e09299dfb47a848697652f53b480499634236df884aad', 'data/references/entringer_connection_certificate.json': '7fcd6cf213aea6ae3f56a89f3af404ecc4c3cb479f237ee28ef6128392cd10a4', 'data/references/entringer_diagnostics.json': 'be6a5ac934d00b9641b22af1f9aafa9375b4a172a5864c9e3a408e74291691bb', 'data/references/exact_checks.json': '6ee6eba5af334d5adda98b2ed09e98f7247679440cdc6b8c3819852b5c31e3df', 'data/references/finite_nonreal_counterexample.json': 'dad58641f7761ad334cd76fd27a1e9c1daeee99760c1803a7ad29dccd0ee97f9', 'data/references/length_diagnostics.json': '2cbf778acf30d2358db7025fc39b9e31291804fbbb33b4057ab5c060a7c71b30', 'data/references/marked_coefficients.json': 'b4c19b65683b34438c1bede73a3d4d8aa608b16e854f6b2e8dfa64b3a10a70b1', 'optional/producer/certify_entringer.py': 'f81fdb88bd32779f3c4e7b9e69c2616e493cce0ed626f7fde39844940b6244b2', 'optional/producer/check_marked_coefficients.py': 'f3aaed9b51d6e066a01185572126b3dae270e2322d2d11a43fe6e932653d6e8e', 'optional/producer/verify_entringer.py': '2e2f8b0f9247f4c2661adf5a6049d74202794b3b6d90046239dd3639c09b9f67', 'optional/audit/check_exact.py': '4a9c56d5cfd3cff8a2da015b79312b139c26d9a60515bbd45c65d469f1cf0f63', 'optional/root/check.py': '98fd88ef3424aaeac58fcc9c5e9aefd7b36968dd5db9db3844b5de9759cf3c1d', 'data/PROVENANCE.json': '939e671fb31cf68e5776ad00a807a199b202ce29b0e44de4a23270a50621494e', 'optional/check_length.py': '6f3d2da49bf43ff62a9dcdf28ed84070068e05e27e80c09bf9732f3924b8ac0d'}


def canonical(value):
    return json.dumps(value,sort_keys=True,indent=2,ensure_ascii=True,allow_nan=False)+'\n'


def same(actual,expected,label='certificate'):
    need(canonical(actual)==canonical(expected),label+' differs from exact regeneration')


def read(path):
    path=Path(path).absolute();files.check_directory(path.parent)
    return files.read_regular(path)


def load_certificate(path):return files.load_json(read(path).decode('utf-8'))


def expression(text):
    """Only integer/rational polynomial expressions; never eval source content."""
    def convert(node):
        if isinstance(node,ast.Constant) and type(node.value) is int:return P(node.value)
        if isinstance(node,ast.Name) and node.id=='lam':return LAM
        if isinstance(node,ast.Name) and node.id=='r':return X
        if isinstance(node,ast.UnaryOp) and isinstance(node.op,(ast.UAdd,ast.USub)):
            v=convert(node.operand);return -v if isinstance(node.op,ast.USub) else v
        if isinstance(node,ast.BinOp):
            if isinstance(node.op,ast.Pow):
                need(isinstance(node.right,ast.Constant) and type(node.right.value) is int
                     and 0<=node.right.value<=64,'unsafe exponent')
                n=node.right.value
                return convert(node.left)**n
            a,b=convert(node.left),convert(node.right)
            if isinstance(node.op,ast.Add):return a+b
            if isinstance(node.op,ast.Sub):return a-b
            if isinstance(node.op,ast.Mult):return a*b
            if isinstance(node.op,ast.Div):return a/b
        raise ValueError('unsupported expression syntax')
    need(isinstance(text,str) and len(text)<50000,'invalid expression')
    result=convert(ast.parse(text,mode='eval').body)
    need(all(b%2==0 for a,b in result.d),'odd rho power is outside Q[lambda,rho²]')
    return P({(a,b//2):v for (a,b),v in result.d.items()})


def references():
    result={}
    need(bool(PINS),'source hash pins are missing')
    for name,digest in sorted(PINS.items()):
        raw=read(ROOT/name)
        need(hashlib.sha256(raw).hexdigest()==digest,'reference SHA-256 mismatch: '+name)
        if name.endswith('.json'):result[name]=files.load_json(raw.decode('utf-8'))
    return result


def interval_endpoints(text):
    need(isinstance(text,str) and re.fullmatch(r'\[-?[0-9]+\.[0-9]+, -?[0-9]+\.[0-9]+\]',text) is not None,
         'unexpected finite interval syntax')
    low,high=[F(x.strip()) for x in text[1:-1].split(',')]
    need(low<high,'invalid interval order')
    return low,high


def derive():
    refs=references()
    provenance=refs['data/PROVENANCE.json']
    need(provenance['report']==180 and provenance['schema_version']==1,'provenance report/schema')
    for record in provenance['references']:
        need(PINS.get(record['file'])==record['sha256'],'provenance reference digest')
    for record in provenance['optional_scripts']:
        need(PINS.get(record['packaged_file'])==record['packaged_sha256'],'provenance optional digest')
    rows=integer_triangle(101);counts=[row[-1] for row in rows]
    need(counts[:len(KNOWN)]==KNOWN,'official 21-term prefix')
    e,a,b=ode_coefficients(100)
    need(e==euler_by_trigonometry(100),'Euler Riccati/trigonometric coefficients differ')
    for n in range(2,102):
        N=n-2;v=factorial(N)**2*b[N]
        need(v.denominator==1 and v.numerator==counts[n],'scalar ODE/triangle n='+str(n))
        need(rows[n][-1]==rows[n][-2],'last two entries differ')
    need(all(counts[n+1]>counts[n] for n in range(2,101)),'checked strict growth')
    marked=marked_triangle(18);me,ma,mb=ode_coefficients(16,marked=True)
    marked_cases=[]
    for n,row in marked.items():
        N=n-2;p=row[-1]
        need(p==factorial(N)**2*mb[N],'marked ODE/triangle n='+str(n))
        need(p.at_lambda(1)==counts[n],'marked specialization n='+str(n))
        need(all(v.denominator==1 and v>0 for v in p.d.values()),'marked positive integer coefficients')
        marked_cases.append({'n':n,'diagonal':p.serial()})
        if n>=3:
            W=[v/factorial(N) for v in row[1:n]]
            prev=[v/factorial(N-1) for v in marked[n-1][1:n-1]]
            need(W[0]==LAM*prev[-1]/N,'marked boundary normalization')
            for j in range(1,N+1):need(W[j]-W[j-1]==prev[N-j],'boustrophedon difference')
    c,h,g,L=frobenius(15)
    s=falling_corrections(L,6)
    need(s==falling_corrections_independent(L,6),'independent falling-factorial expansions')
    scalar=[v.at_lambda(1) for v in s]
    expected=[P(1),-2*LAM,LAM*(2*LAM+1),LAM*(X-(2*LAM+1)**2)/3,
              LAM*(4*LAM**3+4*LAM**2+LAM-7*LAM*X+3*X)/6]
    need(s[:5]==expected,'closed marked coefficients')
    expected_scalar=[P(1),P(-2),P(3),-3+X/3,F(3,2)-2*X/3,
                     F(3,5)-7*X/15+X**2/15,-F(6,5)+13*X/30+19*X**2/45]
    need(scalar==expected_scalar,'closed scalar coefficients')
    Q=pgf_multipliers(s,4)
    need(Q[:4]==[P(1),2*(1-LAM),(LAM-1)*(2*LAM-1),
                         (LAM-1)*(-4*LAM**2+4*LAM+X+3)/3],'closed PGF multipliers')
    mean=[q.derivative_lambda().at_lambda(1) for q in Q]
    need(mean[1:4]==[P(-2),P(1),(X+3)/3],'mean corrections')
    # Independent frozen symbolic calculations are parsed into the exact ring.
    audit=refs['data/references/exact_checks.json']
    need([str(v) for v in counts[2:19]]==audit['original_counts_n2_through18'],'audit original counts')
    for key,values in [('H_coefficients',h),('L_coefficients',L),
                       ('normalized_coefficients',s),('PGF_correction_multipliers',Q)]:
        for index,text in enumerate(audit[key]):need(values[index]==expression(text),'audit '+key+str(index))
    roots=refs['data/references/checks.json']
    for key,values in [('L',[v.at_lambda(1) for v in L]),('b',scalar)]:
        for index,text in enumerate(roots[key]):need(values[index]==expression(text),'root '+key+str(index))
    diagnostic=refs['data/references/entringer_diagnostics.json']
    for index,text in enumerate(diagnostic['L_coefficients']):
        need(L[index].at_lambda(1)==expression(text),'producer scalar L'+str(index))
    p=marked[10][-1];counter=sturm(p.univariate())
    known_coeffs=[55843200,152976000,112276976,33906984,4948521,366404,13230,204,1]
    need(p.univariate()==known_coeffs,'exact n10 polynomial')
    need(counter['degrees']==list(range(8,-1,-1)),'Sturm degrees')
    need(counter['signs_minus_infinity']==[1,-1,1,-1,1,-1,1,1,-1],'Sturm negative signs')
    need(counter['signs_plus_infinity']==[1,1,1,1,1,1,1,-1,-1],'Sturm positive signs')
    need(counter['real_root_count']==6 and counter['squarefree'],'Sturm root count/squarefreeness')
    need(counter['signs_minus_infinity']==list(map(int,audit['n10_sturm_signs_minus_inf'])) and
         counter['signs_plus_infinity']==audit['n10_sturm_signs_plus_inf'],'audit Sturm signs')
    need(p==expression(audit['n10_polynomial']),'audit n10 polynomial')
    finite=refs['data/references/finite_nonreal_counterexample.json']
    need(p==expression(finite['polynomial'].replace('l','lam')),'root counterexample polynomial')
    need(counter['degrees']==finite['degrees'] and
         counter['signs_minus_infinity']==finite['signs_at_negative_infinity'] and
         counter['signs_plus_infinity']==finite['signs_at_positive_infinity'] and
         counter['real_root_count']==finite['real_roots']==finite['negative_roots'] and
         finite['squarefree'] is True,'root counterexample exact evidence')
    counter.update({'n':10,'coefficients_ascending':known_coeffs,'negative_real_roots':6,'nonreal_roots':2})
    tails=rational_tails(420)
    certified=refs['data/references/entringer_connection_certificate.json']
    need(F(certified['analytic_tail_bound'])==F(tails['wronskian_tail_bound']),'interval producer exact tail')
    low,high=interval_endpoints(certified['OEIS_c_interval'])
    published_low='25.5745196289574675215372323127353368945234275278994'
    published_high='25.5745196289574675215372323127353368945234275279353'
    need(F(published_low)<low<high<F(published_high),'published outward decimal rounding')
    interval_endpoints(certified['A0_interval'])
    return {'schema_version':1,'report':180,'oeis':['A386363','A386381'],
            'ring_variables':['lambda','rho_squared'],'oeis_terms':KNOWN,
            'scope':{'scalar_triangle_max_n':101,'marked_triangle_max_n':18,
                     'scalar_inverse_power_order':6,'marked_inverse_power_order':6,
                     'PGF_multiplier_order':4,'frobenius_H_degree':15,
                     'standard_library_only':True,'finite_interval_arithmetic_recomputed':False,
                     'finite_N_asymptotic_remainders_certified':False,
                     'analytic_theorems_proved_in_manuscript':True},
            'count_cases':[{'n':n,'count':value} for n,value in enumerate(counts)],
            'marked_cases':marked_cases,
            'cotangent_coefficients':[v.serial() for v in c],
            'H_coefficients':[v.serial() for v in h],
            'G_coefficients':[v.serial() for v in g],
            'L_coefficients':[v.serial() for v in L],
            'marked_corrections':[v.serial() for v in s],
            'scalar_corrections':[v.serial() for v in scalar],
            'PGF_multipliers':[v.serial() for v in Q],
            'mean_corrections':[v.serial() for v in mean],
            'n10_sturm':counter,'certificate_tails':tails,
            'published_amplitude_enclosure':[published_low,published_high],
            'reference_sha256':PINS}


def manuscript_prefix(path):
    text=read(path).decode('utf-8')
    begin,end='% BEGIN VERIFIED OEIS PREFIX','% END VERIFIED OEIS PREFIX'
    need(text.count(begin)==text.count(end)==1,'prefix marker count')
    need(text.index(begin)<text.index(end),'prefix marker order')
    body=text.split(begin,1)[1].split(end,1)[0].strip()
    need(body.startswith(r'\[') and body.endswith(r'\]'),'prefix display delimiters')
    body=body[2:-2].replace(r'\begin{gathered}','').replace(r'\end{gathered}','')
    body=body.replace(r'\\','').replace('&','').strip()
    if body.endswith('.'):body=body[:-1]
    need(re.fullmatch(r'\s*[0-9]+(?:\s*,\s*[0-9]+)*\s*,?\s*',body) is not None,'nonliteral OEIS prefix')
    actual=[int(s.strip()) for s in body.strip().rstrip(',').split(',')]
    need(actual==KNOWN,'manuscript OEIS prefix differs')


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--data',type=Path,default=ROOT/'data/certificates.json')
    parser.add_argument('--manuscript',type=Path,default=ROOT/'Report180.tex')
    args=parser.parse_args()
    stored=load_certificate(args.data);manuscript_prefix(args.manuscript)
    computed=derive();same(stored,computed)
    print(json.dumps({'status':'PASS','report':180,'all_checks_passed':True,
          'standard_library_only':True,'oeis_terms_checked':21,'largest_exact_n':101,
          'marked_polynomial_cases':17,'scalar_and_marked_corrections_through':6,
          'PGF_multipliers_through':4,'n10_real_roots':6,'n10_nonreal_roots':2,
          'certificate_tail_degree':420,'reference_hashes_checked':len(PINS),
          'finite_interval_arithmetic_recomputed':False,'finite_N_remainders_certified':False},sort_keys=True))

if __name__=='__main__':
    try:main()
    except (ValueError,TypeError,KeyError,IndexError,OSError,SyntaxError) as exc:
        print('VERIFICATION FAILED: '+str(exc),file=sys.stderr);sys.exit(1)
