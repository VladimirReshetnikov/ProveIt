#!/usr/bin/env python3
"""Build the 35-integer sextic and 30-integer octic companions.

Only the Python standard library is required.  Each eliminated equation is
checked to be exactly a nonzero integer multiple of v - f(remaining
variables).  Every final residual and every polynomial restoration identity
is expanded and checked over Z[beta,K0,MC,MF].  These are finite algebraic
checks, separate from the ordinary equivalence proof in PROOF.md.
"""
import hashlib
import importlib.util
import json
import re
from pathlib import Path

HERE = Path(__file__).resolve().parent
PARENT = HERE.parent
spec = importlib.util.spec_from_file_location('q42_algebra', PARENT/'build_verify.py')
alg = importlib.util.module_from_spec(spec)
spec.loader.exec_module(alg)


def require(condition, message):
    if not condition:
        raise ValueError(message)


def write(filename, data):
    (HERE/filename).write_text(json.dumps(data, indent=2)+'\n')


def expand_aliases(expression, aliases):
    for name, formula in aliases:
        expression = re.sub(r'\b'+name+r'\b', '('+formula+')', expression)
    return expression


def substitute(poly, variable_index, value, symbol_count):
    exponent = max((m[variable_index] for m in poly), default=0)
    if exponent == 0:
        return poly
    powers = [{(0,)*symbol_count: 1}, value]
    for _ in range(2, exponent+1):
        powers.append(alg.mul(powers[-1], value))
    result = {}
    for monomial, coefficient in poly.items():
        base = list(monomial)
        power = base[variable_index]
        base[variable_index] = 0
        for factor, scalar in powers[power].items():
            term = tuple(x+y for x, y in zip(base, factor))
            result[term] = result.get(term, 0) + coefficient*scalar
    return {m: c for m, c in result.items() if c}


def render(poly, symbols):
    parts = []
    for monomial, coefficient in sorted(poly.items()):
        term = '*'.join(v+('**'+str(e) if e > 1 else '')
                        for v, e in zip(symbols, monomial) if e)
        if not term:
            part = str(coefficient)
        elif coefficient == 1:
            part = term
        elif coefficient == -1:
            part = '-'+term
        else:
            part = str(coefficient)+'*'+term
        parts.append(part)
    return ' + '.join(parts).replace('+ -', '- ') or '0'


def eliminate(polys, name, formula, symbols):
    index = symbols.index(name)
    value = alg.polynomial(formula, symbols)
    require(all(m[index] == 0 for m in value), 'Self-dependent restoration')
    variable = alg.polynomial(name, symbols)
    expected = alg.add(variable, value, -1)
    removed = None
    unit = None
    for row, residual in enumerate(polys):
        if residual == expected:
            removed, unit = row, 1
            break
        if residual == {m: -c for m, c in expected.items()}:
            removed, unit = row, -1
            break
    require(removed is not None, 'No exact monic defining row for '+name)
    new = [substitute(p, index, value, len(symbols))
           for row, p in enumerate(polys) if row != removed]
    return new, value, {'variable': name, 'row_before_elimination': removed+1,
                        'row_sign': unit, 'restoration': render(value, symbols)}


def main():
    source_bytes = (PARENT/'quartic42.json').read_bytes()
    source_sha = hashlib.sha256(source_bytes).hexdigest()
    require(source_sha == '1e38542f9a7cbcfbad1a24153d0e970d0967ae6d9aef98ea5c4b3bf13cd27bc1',
            'Unexpected Q42 source bytes')
    source = json.loads(source_bytes)
    require(source['variable_count'] == 42 and len(source['residuals']) == 27,
            'Unexpected parent shape')
    variables = ['rho' if v == 'q_half_root' else v for v in source['variables']]
    ports = source['fixed_numerals']
    symbols = variables+ports
    require(source['residuals'][23] == 'beta*J+1-2*q_half_root**2',
            'Unexpected old square guard')
    residuals = list(source['residuals'])
    residuals[23] = 'X-8*rho**2'
    original = [alg.polynomial(p, symbols) for p in residuals]
    binding = dict(source['coefficient_binding'])
    for key in ('manifest', 'compiler_manifest', 'transfer_proof'):
        binding[key] = '../'+binding[key]
    variant = {
        'name': 'quartic42_X_square_variant',
        'domain': 'unrestricted integers',
        'variables': variables, 'variable_count': 42,
        'fixed_numerals': ports, 'coefficient_binding': binding,
        'residuals': residuals, 'equation_count': 27,
        'exact_degree': 4, 'single_polynomial': 'sum of squared residuals',
        'source_sha256': source_sha,
        'change': 'Replace q=2*q_half_root^2 by X=8*rho^2; all other rows unchanged.',
        'proof': 'PROOF.md#relocated-square-guard'
    }
    write('quartic42_x_square.json', variant)
    base_aliases = [('C', 'q-F-alpha'), ('k', 'eta+zeta'),
                    ('s', '2*v_scale+1'), ('q', 'beta*J+1')]
    guard_rows = [
        'F*alpha-1-FA_pos1**2-FA_pos2**2-FA_pos3*(FA_pos3+1)',
        'F*C-1-FC_pos1**2-FC_pos2**2-FC_pos3*(FC_pos3+1)',
        'eta*zeta-1-EZ_pos1**2-EZ_pos2**2-EZ_pos3*(EZ_pos3+1)'
    ]
    sextic_plan = [
        ('P', 'k+E*(c-eta)'), ('F2', 'f*f'), ('g', 'y*y-V*V'),
        ('X', '8*rho*rho'), ('N', 'q*(L+1)'), ('C2', 'c*c'),
        ('w', '4*u*u')
    ]
    sextic_readable = [
        'L-q*q+1', '8*rho*rho-4*u*u*q', 'a-E-s*q*(L+1)',
        'E*(8*rho*rho+1)-8*rho*rho*a', 'c-eta-(a-E)*k',
        'tau*tau+(2*tau-k)*E*(c-eta)-1',
        'D-8*rho*rho-a*c-gamma*(4*a+3)', 'Delta-a*a-4*a-3',
        'D*D-Delta*c*c-1',
        'k-1-h*E-(((q-1)*(q-F)+alpha)*L+(MC+q*MF)*J)',
        '(K0+4*u*u)*C-F-z*(q-1)', 'V+c-f*o',
        'V-j*c+k-1-h*E', 'I-(2*r+1)*c*c', 'Baux-I*I',
        'Baux-Delta*(f*f-1)', 'y*y-Baux*(y*y-V*V)-1'
    ]+guard_rows
    octic_plan = [
        ('N', 'q*(L+1)'), ('C2', 'c*c'), ('F2', 'f*f'),
        ('g', 'y*y-V*V'), ('w', '4*u*u'), ('X', '8*rho*rho'),
        ('zeta', 'P-E*(c-eta)-eta'), ('Baux', 'I*I'),
        ('D', '8*rho*rho+a*c+gamma*(4*a+3)'),
        ('Delta', 'a*a+4*a+3'),
        ('P', '1-V+j*c+h*E+E*(c-eta)'), ('L', 'q*q-1')
    ]
    octic_aliases = [('R', '((q-1)*(q-F)+alpha)*(q*q-1)+(MC+q*MF)*J'),
                     ('B', 'E*(c-eta)'), ('H', '4*a+3'),
                     ('Delta', 'a*a+4*a+3'), ('k', '1-V+j*c+h*E'),
                     ('s', '2*v_scale+1'), ('C', 'q-F-alpha'),
                     ('q', 'beta*J+1')]
    octic_readable = [
        '8*rho*rho-4*u*u*q', 'a-E-s*q*q*q',
        'E*(8*rho*rho+1)-8*rho*rho*a', 'c-eta-(a-E)*k',
        'tau*tau-(k+B)*B-1',
        '(8*rho*rho+a*c+gamma*H)**2-Delta*c*c-1',
        '-V+j*c-R', '(K0+4*u*u)*C-F-z*(q-1)',
        'V+c-f*o', 'I-(2*r+1)*c*c', 'I*I-Delta*(f*f-1)',
        'y*y-I*I*(y*y-V*V)-1',
        guard_rows[0], guard_rows[1],
        'eta*(k-eta)-1-EZ_pos1**2-EZ_pos2**2-EZ_pos3*(EZ_pos3+1)'
    ]
    plans = [
        ('sextic35', sextic_plan, sextic_readable, base_aliases, True, 35, 6,
         {'r': 2, 'c': 4}, 4),
        ('octic30', octic_plan, octic_readable, octic_aliases, False, 30, 8,
         {'a': 4, 'f': 4}, 1)
    ]
    audits = []
    for name, plan, readable, aliases, shear, wanted_vars, wanted_degree, certificate, expected_coefficient in plans:
        polys = list(original)
        restorations = {v: alg.polynomial(v, symbols) for v in variables}
        initial_coordinate = None
        if shear:
            initial_coordinate = 'tau_old=tau_tail+P-eta-zeta'
            tau_value = alg.polynomial('tau+P-eta-zeta', symbols)
            polys = [substitute(p, symbols.index('tau'), tau_value, len(symbols))
                     for p in polys]
            restorations['tau'] = tau_value
        ledger = []
        active = list(variables)
        for variable, formula in plan:
            formula = expand_aliases(formula, base_aliases)
            polys, value, entry = eliminate(polys, variable, formula, symbols)
            ledger.append(entry)
            restorations = {v: substitute(p, symbols.index(variable), value, len(symbols))
                            for v, p in restorations.items()}
            active.remove(variable)
        require(len(active) == wanted_vars, name+': variable count mismatch')
        require(len(polys) == len(readable) == 27-len(plan),
                name+': residual count mismatch')
        for i, expression in enumerate(readable):
            require(alg.polynomial(expand_aliases(expression, aliases), symbols) == polys[i],
                    name+': readable transcription mismatch, row '+str(i+1))
        # Each source residual restores to precisely one final residual or 0.
        # Simultaneously substitute the final-variable restoration for each
        # factor of each original monomial (never recursively into images).
        source_to_child = []
        for residual in original:
            result = {}
            for monomial, coefficient in residual.items():
                product = {(0,)*len(symbols): coefficient}
                for i, exponent in enumerate(monomial):
                    if exponent == 0:
                        continue
                    factor = restorations[symbols[i]] if i < 42 else alg.polynomial(symbols[i], symbols)
                    for _ in range(exponent):
                        product = alg.mul(product, factor)
                result = alg.add(result, product)
            if result:
                matches = [i+1 for i, p in enumerate(polys) if p == result]
                require(len(matches) == 1, name+': parent restoration identity failed')
                source_to_child.append(matches[0])
            else:
                source_to_child.append(0)
        require(sorted(x for x in source_to_child if x) == list(range(1,len(polys)+1)),
                name+': incomplete restoration coverage')
        degrees = [alg.norm_degree(p, 42) for p in polys]
        require(max(degrees) == wanted_degree//2, name+': residual degree mismatch')
        expanded = {}
        for p in polys:
            expanded = alg.add(expanded, alg.mul(p, p))
        require(alg.norm_degree(expanded, 42) == wanted_degree, name+': SOS degree mismatch')
        monomial = tuple(certificate.get(v, 0) for v in symbols)
        require(expanded.get(monomial) == expected_coefficient,
                name+': exact-degree coefficient mismatch')
        used = {symbols[i] for p in polys for m in p for i,e in enumerate(m) if e}
        require(used == set(active+ports), name+': unused or eliminated symbol remains')
        rename = {'tau': 'tau_tail'} if shear else {}
        output_symbols = [rename.get(v, v) for v in symbols]
        output_active = [rename.get(v, v) for v in active]
        coefficient_text = '*'.join(v+'^'+str(e) for v,e in certificate.items())
        packet = {
            'name': name+'_from_quartic42', 'domain': 'unrestricted integers',
            'variables': output_active, 'variable_count': len(active),
            'fixed_numerals': ports, 'coefficient_binding': binding,
            'residuals': [render(p, output_symbols) for p in polys],
            'equation_count': len(polys), 'residual_degrees': degrees,
            'single_polynomial': 'sum of squared residuals',
            'exact_degree': wanted_degree,
            'exact_degree_certificate': {'monomial': certificate, 'coefficient': expected_coefficient},
            'parent': 'quartic42_x_square.json',
            'initial_coordinate_change': initial_coordinate,
            'eliminations': ledger,
            'full_parent_restorations': {v: render(p, output_symbols) for v,p in restorations.items()},
            'parent_residual_maps_to_child_row_or_zero': source_to_child,
            'proof': 'PROOF.md',
            'status': 'Exact polynomial elimination; equivalence to Con(ZFC) inherits the ordinary Q42 proof.'
        }
        write(name+'.json', packet)
        write(name+'_readable.json', {
            'aliases': dict(aliases),
            'residuals': [re.sub(r'\btau\b', 'tau_tail', p) if shear else p for p in readable],
            'checked_rows': len(readable)
        })
        write(name+'_expanded.json', {
            'symbols': output_active+ports,
            'exact_degree_in_witnesses': wanted_degree,
            'terms': [[coefficient, [[output_symbols[i], e] for i,e in enumerate(m) if e]]
                      for m, coefficient in sorted(expanded.items())],
            'term_count_with_ports_symbolic': len(expanded)
        })
        audits.append({
            'name': name, 'variables': len(active), 'residuals': len(polys),
            'maximum_residual_degree': max(degrees), 'exact_SOS_degree': wanted_degree,
            'exact_monic_eliminations': len(ledger),
            'checked_parent_restoration_identities': len(source_to_child),
            'checked_readable_transcriptions': len(readable),
            'exact_degree_certificate': f'coefficient of {coefficient_text} = {expected_coefficient}',
            'residual_terms_with_ports_symbolic': sum(len(p) for p in polys),
            'SOS_terms_with_ports_symbolic': len(expanded),
            'uses_removable_assertions': False
        })
    write('AUDIT.json', {
        'source_quartic42_sha256': source_sha,
        'companions': audits,
        'scope': 'Finite exact algebra and source audit. The square-guard equivalence and inherited arithmetic/compiler proof are ordinary mathematics, not certified here.',
        'minimality': 'No claim of global or search-space minimality.'
    })
    print(json.dumps(audits, indent=2))


if __name__ == '__main__':
    main()
