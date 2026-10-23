#!/usr/bin/env python3
"""Construct and exactly audit the 42-integer quartic; standard library only.

This is a finite polynomial/source check.  It does not certify the unbounded
Pell/compiler theorem and does not search for a ZFC refutation.
"""
import ast
import hashlib
import json
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parent


def require(condition, message):
    if not condition:
        raise ValueError(message)


def add(p, q, factor=1):
    out = dict(p)
    for m, c in q.items():
        out[m] = out.get(m, 0) + factor*c
        if not out[m]:
            del out[m]
    return out


def mul(p, q):
    out = {}
    for a, x in p.items():
        for b, y in q.items():
            m = tuple(i+j for i, j in zip(a, b))
            out[m] = out.get(m, 0) + x*y
    return {m: c for m, c in out.items() if c}


def polynomial(expression, symbols):
    zero = (0,)*len(symbols)
    index = {v: i for i, v in enumerate(symbols)}

    def rec(node):
        if isinstance(node, ast.Name):
            require(node.id in index, 'Unknown symbol '+node.id)
            mon = list(zero)
            mon[index[node.id]] = 1
            return {tuple(mon): 1}
        if isinstance(node, ast.Constant):
            require(type(node.value) is int, 'Only integer constants allowed')
            return {zero: node.value} if node.value else {}
        if isinstance(node, ast.UnaryOp) and isinstance(node.op, ast.USub):
            return {m: -c for m, c in rec(node.operand).items()}
        require(isinstance(node, ast.BinOp), 'Unsupported expression node')
        if isinstance(node.op, ast.Add):
            return add(rec(node.left), rec(node.right))
        if isinstance(node.op, ast.Sub):
            return add(rec(node.left), rec(node.right), -1)
        if isinstance(node.op, ast.Mult):
            return mul(rec(node.left), rec(node.right))
        if isinstance(node.op, ast.Pow):
            require(isinstance(node.right, ast.Constant)
                    and type(node.right.value) is int
                    and 0 <= node.right.value <= 4, 'Invalid fixed exponent')
            out = {zero: 1}
            b = rec(node.left)
            for _ in range(node.right.value):
                out = mul(out, b)
            return out
        raise ValueError('Unsupported operator')
    return rec(ast.parse(expression, mode='eval').body)


def norm_degree(p, witness_count):
    return max((sum(m[:witness_count]) for m in p), default=-1)


def write(name, data):
    (ROOT/name).write_text(json.dumps(data, indent=2, sort_keys=False)+'\n')


def main():
    parent_path = ROOT/'upstream'/'quartic45.json'
    parent_bytes = parent_path.read_bytes()
    require(hashlib.sha256(parent_bytes).hexdigest()
            == '2b4d3d372fd899042eb3db9ee25e085193204640d28009807fde0778bc9528ac',
            'Pinned source bytes changed')
    parent = json.loads(parent_bytes)
    require(parent['variable_count'] == 45, 'Unexpected parent dimension')
    require(len(parent['variables']) == 45, 'Incorrect parent variable list')
    require(len(parent['residuals']) == 28, 'Unexpected parent equation count')
    require(parent['residuals'][22] == '-u**2 + w', 'Square-scale row changed')
    guard_names = [side+'_pos'+str(i) for side in ('eta', 'zeta')
                   for i in (1, 2, 3)]
    old_variables = set(parent['variables'])
    require(set(guard_names) <= old_variables, 'Missing source guard variables')
    for i, expression in enumerate(parent['residuals']):
        names = {n.id for n in ast.walk(ast.parse(expression, mode='eval'))
                 if isinstance(n, ast.Name)}
        if i not in (23, 24):
            require(not names.intersection(guard_names), 'Private guard variable reused')

    witnesses = [v for v in parent['variables'] if v not in guard_names]
    witnesses += ['EZ_pos1', 'EZ_pos2', 'EZ_pos3']
    residuals = parent['residuals'][:22]
    residuals += ['w-4*u**2']
    residuals += parent['residuals'][25:]
    residuals += ['eta*zeta-EZ_pos1**2-EZ_pos2**2-EZ_pos3*(EZ_pos3+1)-1']
    require(len(witnesses) == 42 and len(set(witnesses)) == 42,
            'Incorrect resulting variables')
    require(len(residuals) == 27, 'Incorrect residual count')

    ports = parent['fixed_numerals']
    symbols = witnesses+ports
    polynomials = [polynomial(e, symbols) for e in residuals]
    degrees = [norm_degree(p, 42) for p in polynomials]
    require(all(d <= 2 for d in degrees), 'Residual is not quadratic')
    used = {symbols[i] for p in polynomials for m in p
            for i, exponent in enumerate(m) if exponent}
    require(used == set(symbols), 'An advertised symbol is unused')
    total = {}
    for p in polynomials:
        total = add(total, mul(p, p))
    degree = norm_degree(total, 42)
    require(degree == 4, 'Unexpected exact degree')
    tau4 = tuple(4 if v == 'tau' else 0 for v in symbols)
    require(total.get(tau4, 0) == 1, 'tau^4 certificate failed')

    # Exact source relation: only the square-scale residual and two guards
    # changed; all arithmetic rows (including transport and exposed quotients)
    # retain their original strings and exact polynomials.
    unchanged = list(range(22))+list(range(25, 28))
    require(len(unchanged) == 25, 'Incorrect unchanged-row count')
    for old_index, new_index in [(i, i) for i in range(22)]+[(i, i-2) for i in range(25, 28)]:
        require(polynomial(parent['residuals'][old_index], symbols)
                == polynomials[new_index], 'Retained arithmetic changed')

    # Human-readable formula transcription, independently expanded into the
    # same polynomial ring.  In particular the actual transport coordinate
    # is shifted: its residual contains z, not z-1.
    readable = [
        'L-q*q+1', 'N-q*(L+1)', 'X-w*q',
        'a-E-(2*v_scale+1)*N', 'E*(X+1)-X*a',
        'c-eta-(a-E)*k', 'P-k-E*(c-eta)',
        'tau*tau-P*(P-k)-1', 'D-X-a*c-gamma*(4*a+3)',
        'Delta-a*a-4*a-3', 'C2-c*c', 'D*D-Delta*C2-1',
        'k-1-h*E-((q-F)*(N-q)-C*L+(MC+q*MF)*J)',
        '(K0+w)*C-F-z*(q-1)', 'F2-f*f', 'V+c-f*o',
        'V-j*c+k-1-h*E', 'g+V*V-y*y', 'I-(2*r+1)*C2',
        'Baux-I*I', 'Baux-Delta*(F2-1)', 'y*y-Baux*g-1',
        'w-4*u*u', 'q-2*q_half_root*q_half_root',
        'F*alpha-1-FA_pos1**2-FA_pos2**2-FA_pos3*(FA_pos3+1)',
        'F*C-1-FC_pos1**2-FC_pos2**2-FC_pos3*(FC_pos3+1)',
        'eta*zeta-1-EZ_pos1**2-EZ_pos2**2-EZ_pos3*(EZ_pos3+1)',
    ]
    for index, expression in enumerate(readable):
        for v, t in [('C', 'q-F-alpha'), ('k', 'eta+zeta'), ('q', 'beta*J+1')]:
            expression = re.sub(r'\b'+v+r'\b', '('+t+')', expression)
        require(polynomial(expression, symbols) == polynomials[index],
                'Readable formula mismatch at row '+str(index+1))

    packet = {
        'name': 'quartic42_common_sign_rank_recovery',
        'domain': 'unrestricted integers',
        'variables': witnesses,
        'variable_count': 42,
        'equation_count': 27,
        'fixed_numerals': ports,
        'coefficient_binding': {
            **parent['coefficient_binding'],
            'manifest': 'dependencies/source34/COEFFICIENT_BINDING.json',
            'compiler_manifest': 'dependencies/source34/coefficients/payloads/COEFFICIENT_BINDING.json',
            'transfer_proof': 'dependencies/source34/coefficients/COEFFICIENT_PROOF.md',
        },
        'coefficient_tuple_note': 'The entire package34 tuple of parent Q45; no port replacement.',
        'residuals': residuals,
        'residual_degrees': degrees,
        'single_polynomial': 'sum of squares of listed residuals',
        'exact_degree': degree,
        'exact_degree_certificate': 'coefficient of tau^4 is 1',
        'parent_sha256': hashlib.sha256(parent_bytes).hexdigest(),
        'source_commit': 'beb0192cb8dc36f78c369c080f2adfbc1887a486',
        'source_repository_path': 'Computability/DiophantineConsistency/con-zfc-diophantine-forms/57-separated-degrees/quartic/quartic45.json',
        'proof': 'PROOF.md',
        'status': 'Ordinary mathematical reduction with stated inherited lemmas; no new kernel certificate.'
    }
    expanded = {
        'symbols': symbols,
        'fixed_coefficient_symbols': ports,
        'terms': [[c, [[symbols[i], exponent] for i, exponent in enumerate(m) if exponent]]
                  for m, c in sorted(total.items())],
        'exact_degree_in_witnesses': degree,
        'term_count_with_ports_symbolic': len(total),
    }

    # Bounded diagnostics of the elementary sign lemma and scale restriction.
    sign_cases = 0
    for e in range(5, 101):
        for R in range(1, (e-1)//4+1):
            if not e > 4*R:
                continue
            for n in range(1, R):
                require((2*n+R+1) % e != 0,
                        'Sign-recovery interval diagnostic failed')
                sign_cases += 1
    pos_cases = 0
    for x in range(-8, 9):
        for y in range(-8, 9):
            for t in range(-8, 9):
                require(1+x*x+y*y+t*(t+1)>0, 'Pos diagnostic failed')
                pos_cases += 1
    audit = {
        'parent_sha256': hashlib.sha256(parent_bytes).hexdigest(),
        'old_variables': 45, 'new_variables': 42,
        'old_equations': 28, 'new_equations': 27,
        'exact_retained_rows': 25,
        'all_residuals_quadratic': True,
        'exact_degree': degree,
        'tau_fourth_coefficient': 1,
        'expanded_term_count_with_ports_symbolic': len(total),
        'positive_guard_diagnostic_cases': pos_cases,
        'negative_sign_exclusion_diagnostic_cases': sign_cases,
        'uses_removable_assertions': False,
        'limits': 'Finite exact algebra/data audit; universal proof is PROOF.md and its inherited dependencies.'
    }
    write('quartic42.json', packet)
    write('quartic42_expanded.json', expanded)
    write('READABLE_FORMULAS.json', {
        'abbreviations': {'q': 'beta*J+1', 'C': 'q-F-alpha', 'k': 'eta+zeta'},
        'residuals': readable,
        'exactly_checked_rows': 27,
        'transport_note': 'The literal source uses shifted z, not z-1.'
    })
    write('AUDIT.json', audit)
    print(json.dumps(audit, indent=2))


if __name__ == '__main__':
    main()
