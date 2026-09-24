#!/usr/bin/env python3
"""Verify an explicit 87-operation primality-certificate circuit against the article.

This is an exact symbolic identity check, not a primality prover or a witness
search. Each subtraction can be checked as an addition: t = a-b is certified
by the one operation t+b and comparison with a. Intermediate integers are
supplied as part of a certificate; equality/domain tests are not arithmetic
operations. Thus the bound does not require a subtraction primitive.

Run from any directory with Python 3.10+ and SymPy installed.
Reads the current source.
It writes jones1976_primality87.json and jones1976_primality87.md next to
itself.
"""
from __future__ import annotations
import json
from pathlib import Path
import sympy as sp
from jones1976_verify_mathematics import source_polynomials, LOCAL

HERE = Path(__file__).resolve().parent
# Every tuple is one binary operation. Inputs a,...,z and constants are free.
BLOCKS = [
    [('hj','+','h','j'), ('wz','*','w','z'), ('rhs1','+','wz','hj')],
    [('gk','*','g','k'), ('gkg','+','gk','g'), ('gkgk','+','gkg','k'),
     ('zprod','*','gkgk','hj'), ('rhs2','+','zprod','h')],
    [('kp1','+','k',1), ('np1','+','n',1), ('fourk','*',4,'k'),
     ('fourkn','*','fourk','np1'), ('fourkn2','*','fourkn','fourkn'),
     ('kkp1','*','k','kp1'), ('fprod','*','kkp1','fourkn2'),
     ('rhs3','+','fprod',1), ('lhs3','*','f','f')],
    [('twon','*',2,'n'), ('pq','+','p','q'), ('pqz','+','pq','z'),
     ('rhs4','+','pqz','twon')],
    [('ap1','+','a',1), ('ep2','+','e',2), ('eap1','*','e','ap1'),
     ('eap12','*','eap1','eap1'), ('eep2','*','e','ep2'),
     ('oprod','*','eep2','eap12'), ('rhs5','+','oprod',1), ('lhs5','*','o','o')],
    [('a2','*','a','a'), ('A','-','a2',1), ('y2','*','y','y'),
     ('xprod','*','A','y2'), ('rhs6','+','xprod',1), ('lhs6','*','x','x')],
    [('ry2','*','r','y2'), ('fourry2','*',4,'ry2'),
     ('fourry22','*','fourry2','fourry2'), ('uprod','*','A','fourry22'),
     ('rhs7','+','uprod',1), ('u2','*','u','u')],
    [('cu','*','c','u'), ('xcu','+','x','cu'), ('lhs8','*','xcu','xcu'),
     ('u2a','-','u2','a'), ('u2u2a','*','u2','u2a'), ('G','+','a','u2u2a'),
     ('G2','*','G','G'), ('G2m1','-','G2',1), ('dy','*','d','y'),
     ('fourdy','*',4,'dy'), ('nfourdy','+','n','fourdy'),
     ('nfourdy2','*','nfourdy','nfourdy'), ('gprod','*','G2m1','nfourdy2'),
     ('rhs8','+','gprod',1)],
    [('l2','*','l','l'), ('mprod','*','A','l2'), ('rhs9','+','mprod',1),
     ('lhs9','*','m','m')],
    [('am1','-','a',1), ('iam1','*','i','am1'), ('rhs10','+','k','iam1')],
    [('nl','+','n','l'), ('rhs11','+','nl','v')],
    [('an','-','a','np1'), ('an2','*','an','an'), ('Dn','-','A','an2'),
     ('bDn','*','b','Dn'), ('lan','*','l','an'), ('pla','+','p','lan'),
     ('rhs12','+','pla','bDn')],
    [('ap','-','a','p'), ('app','-','ap',1), ('app2','*','app','app'),
     ('Dpp','-','A','app2'), ('sDpp','*','s','Dpp'),
     ('yapp','*','y','app'), ('qyapp','+','q','yapp'),
     ('rhs13','+','qyapp','sDpp')],
    [('ap2','*','ap','ap'), ('Dp','-','A','ap2'), ('tDp','*','t','Dp'),
     ('pl','*','p','l'), ('plap','*','pl','ap'), ('zplap','+','z','plap'),
     ('rhs14','+','zplap','tDp'), ('lhs14','*','p','m')],
]
LHS = ['q','z','lhs3','e','lhs5','lhs6','u2','lhs8','lhs9','l','y',
       'm','x','lhs14']


def require(condition: bool, message: str) -> None:
    if not condition:
        raise AssertionError(message)


def verify() -> dict:
    env = dict(LOCAL)
    instructions = []
    hist = {'+': 0, '-': 0, '*': 0}
    for eq, block in enumerate(BLOCKS, 1):
        for target, op, left, right in block:
            require(target not in env, f'Redefined name: {target}')
            lv = sp.Integer(left) if isinstance(left, int) else env[left]
            rv = sp.Integer(right) if isinstance(right, int) else env[right]
            value = {'+': lambda: lv+rv, '-': lambda: lv-rv,
                     '*': lambda: lv*rv}[op]()
            env[target] = value
            hist[op] += 1
            # In strict +,* certificate mode, reverse subtraction as addition.
            checked_left = target if op == '-' else left
            checked_op = '+' if op == '-' else op
            checked_right = right
            compared_to = left if op == '-' else target
            instructions.append(dict(number=len(instructions)+1, block=eq,
                target=target, op=op, left=left, right=right,
                certificate_check={'left':checked_left,'op':checked_op,
                                   'right':checked_right,'equals':compared_to}))
            # Verify the reversed check independently, as a polynomial identity.
            cl = env[checked_left] if isinstance(checked_left,str) else sp.Integer(checked_left)
            cr = env[checked_right] if isinstance(checked_right,str) else sp.Integer(checked_right)
            ct = env[compared_to] if isinstance(compared_to,str) else sp.Integer(compared_to)
            check = cl+cr if checked_op == '+' else cl*cr
            require(sp.expand(check-ct) == 0, f'Certificate check failed at {target}')

    text = (HERE.parent/'1976'/'jones1976_corrected.tex').read_text(encoding='utf-8')
    poly_residuals, theorem_residuals = source_polynomials(text)
    circuit_residuals = [env[f'rhs{j}']-env[lhs]
                         for j,lhs in enumerate(LHS, 1)]
    orientations = []
    for j,(c,t) in enumerate(zip(circuit_residuals,theorem_residuals),1):
        sign = 1 if sp.expand(c-t)==0 else -1
        require(sp.expand(c-sign*t)==0, f'Source equation {j} mismatch')
        orientations.append(sign)
    k = LOCAL['k']
    mapping = []
    for residual in poly_residuals:
        matches = [j for j,c in enumerate(circuit_residuals,1)
                   if sp.expand(residual-c.subs(k,k+1))==0
                   or sp.expand(residual+c.subs(k,k+1))==0]
        require(len(matches)==1,'Ambiguous/missing prime-polynomial match')
        mapping.append(matches[0])
    require(sorted(mapping)==list(range(1,15)), 'Polynomial is not the same system')
    require(sp.expand(env['kp1']-k-1)==0, 'Candidate relation failed')
    require(len(instructions)==87, 'Operation count is not 87')
    require([len(b) for b in BLOCKS]==[3,5,9,4,8,6,6,14,4,3,2,7,8,8],
            'Unexpected block counts')
    return dict(status='PASS', operation_count=87, block_counts=[len(b) for b in BLOCKS],
        straight_line_operations=hist,
        addition_multiplication_certificate_operations={
            'additions':hist['+']+hist['-'], 'multiplications':hist['*']},
        exact_source_equations_verified=14,
        circuit_to_source_residual_signs=orientations,
        prime_polynomial_residual_to_equation=mapping,
        conditions='a,...,z nonnegative; k>=1; candidate N=kp1. '
                   'Intermediate signed integers may be supplied. '
                   'Equality/domain checks and reading the certificate are not arithmetic operations.',
        scope='An independently constructed upper-bound certificate, not an optimality proof, '
              'not a reconstruction of the authors\' undisclosed evaluation order, '
              'and not a bit-complexity bound or witness-finding algorithm.',
        instructions=instructions,
        final_equalities=[{'left':l,'right':f'rhs{j}'} for j,l in enumerate(LHS,1)]
                        + [{'left':'candidate','right':'kp1'}])


def main() -> None:
    report=verify()
    (HERE/'jones1976_primality87.json').write_text(json.dumps(report,indent=2)+'\n',
                                               encoding='utf-8',newline='\n')
    lines=['# An explicit 87-operation primality certificate','',
        'Independent verification of Theorem 5 (1976).', '',
        'All fourteen residuals are checked symbolically against the accompanying TeX; '
        'they also match the degree-25 prime polynomial after the documented shift of k.', '',
        '## Counting convention', '', report['conditions'], '', report['scope'], '',
        'The displayed straight-line schedule has subtractions. In a certificate using '
        'literally only addition and multiplication, supply each intermediate integer and '
        'replace `t = a - b` by the one-addition check `t + b = a`. '
        'All other assignments are checked directly. Hence the same schedule uses exactly '
        f"{report['addition_multiplication_certificate_operations']['additions']} additions and "
        f"{report['addition_multiplication_certificate_operations']['multiplications']} multiplications.", '',
        'Supply k as part of the certificate and verify N=kp1; kp1 was already computed. '
        'Thus converting the tested number N to k does not add a subtraction.', '',
        '| No. | Equation block | Assignment | Addition/multiplication check |',
        '|---:|---:|---|---|']
    for row in report['instructions']:
        c=row['certificate_check']
        lines.append(f"| {row['number']} | {row['block']} | `{row['target']} = {row['left']} {row['op']} {row['right']}` | `{c['left']} {c['op']} {c['right']} = {c['equals']}` |")
    lines.extend(['','## Final comparisons','',
        'These are equality tests, with no additional arithmetic:', '',
        ', '.join(f"`{e['left']} = {e['right']}`" for e in report['final_equalities']), '',
        'Reproduce with `python jones1976_verify_87_operations.py`. The argument from satisfiability '
        'to primality is Theorem 2.12; this script verifies its arithmetic realization, '
        'not the complete number-theoretic proof of that theorem.', ''])
    (HERE/'jones1976_primality87.md').write_text('\n'.join(lines),encoding='utf-8',newline='\n')
    print(json.dumps({k:v for k,v in report.items() if k not in ('instructions','final_equalities')},indent=2))

if __name__=='__main__':
    main()
