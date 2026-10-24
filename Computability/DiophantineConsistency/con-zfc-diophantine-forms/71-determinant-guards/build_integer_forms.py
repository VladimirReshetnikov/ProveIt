#!/usr/bin/env python3
"""Build Q38, S32, O27 and exact integer-coordinate restoration certificates."""
from pathlib import Path
import hashlib
import json
from polynomial import Poly, parse, require

ROOT = Path(__file__).resolve().parent
PORTS = ['beta', 'K0', 'MC', 'MF', 'cone_A', 'cone_B']


def write(path, value):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, indent=2, sort_keys=True)+'\n')


def source38():
    parent = json.loads((ROOT/'upstream/quartic41.json').read_text())
    removed = {f'{prefix}_pos{i}' for prefix in ['FA', 'FC'] for i in range(1, 4)}
    variables = [x for x in parent['variables'] if x not in removed]
    variables += ['cone_pos1', 'cone_pos2', 'cone_pos3']
    aliases = {'q': parse('beta*J+1')}
    aliases['C'] = parse('q-F-alpha', aliases)
    aliases['cone_U'] = parse('cone_A*F', aliases)
    aliases['cone_V'] = parse('cone_B*C', aliases)
    aliases['cone_W'] = parse('q-cone_U-cone_V', aliases)
    cone = 'cone_U*cone_V-cone_W**2'
    guard = parse(cone+'-1-cone_pos1**2-cone_pos2**2-cone_pos3*(cone_pos3+1)', aliases)
    rows = [parse(x) for i, x in enumerate(parent['residuals']) if i not in (23, 24)]
    rows.insert(23, guard)
    require(len(variables) == 38 and len(rows) == 25, 'Q38 dimensions')
    return variables, rows


def eliminate(variables, rows, var, rhs, history, restorations):
    rhs = parse(rhs)
    require(var not in rhs.symbols(), 'acyclic elimination: '+var)
    defining = Poly.symbol(var)-rhs
    hits = [i for i, row in enumerate(rows) if row == defining or row == -defining]
    require(len(hits) == 1, 'unique monic defining row: '+var)
    deleted = hits[0]
    new_rows = [row.substitute({var: rhs}) for i, row in enumerate(rows) if i != deleted]
    history.append({'variable': var, 'right_hand_side': rhs.expression(),
                    'deleted_row_at_step': deleted, 'exact_monic_identity': True})
    for old in restorations:
        restorations[old] = restorations[old].substitute({var: rhs})
    variables = [x for x in variables if x != var]
    return variables, new_rows


def packet(name, variables, rows, degree, witness_monomial, coefficient, history=None,
           restorations=None, parent_rows=None):
    require(set().union(*(r.symbols() for r in rows))-set(PORTS) == set(variables),
            name+': all and only listed unknowns are live')
    residual_degrees = [row.degree(variables) for row in rows]
    require(max(residual_degrees)*2 == degree, name+': degree upper bound')
    polynomial = sum((row*row for row in rows), Poly())
    require(polynomial.degree(variables) == degree, name+': exact degree')
    require(polynomial.coefficient(witness_monomial, variables) == coefficient,
            name+': exact leading coefficient')
    if name == 'quartic38':
        require(polynomial.coefficient({'J': 4}, variables) ==
                parse('beta**4*(cone_B-1)**4+beta**4+beta**2*(beta-MF)**2'),
                'Q38 exact pure J^4 coefficient')
    restore_results = []
    if restorations is not None:
        used = []
        for i, row in enumerate(parent_rows):
            restored = row.substitute(restorations)
            if restored == 0:
                restore_results.append({'parent_row': i, 'result': 'identically zero'})
            else:
                matches = [j for j, new in enumerate(rows) if restored == new or restored == -new]
                require(len(matches) == 1, name+': full parent-row restoration '+str(i))
                used.append(matches[0])
                restore_results.append({'parent_row': i, 'result': 'retained residual', 'row': matches[0]})
        require(sorted(used) == list(range(len(rows))), name+': one-to-one retained-row matching')
    out = {'name': name, 'domain': 'all integers', 'variables': variables,
           'variable_count': len(variables), 'fixed_ports': PORTS,
           'residuals': [r.expression() for r in rows], 'residual_count': len(rows),
           'single_equation': 'sum of squares of all listed residuals = 0',
           'exact_degree': degree,
           'coefficient_binding': '../coefficients/NEW_BINDING.json',
           'semantic_scope': 'new reduction proved in report; inherits explicitly named source64 native/Pell/calibration theorems'}
    if restorations is not None:
        out['full_parent_restoration'] = {v: p.expression() for v, p in restorations.items() if v not in variables}
    audit = {'name': name, 'status': 'PASS', 'variables': len(variables),
             'residuals': len(rows), 'residual_degrees': residual_degrees,
             'exact_degree': degree, 'leading_monomial': witness_monomial,
             'leading_coefficient': coefficient, 'symbolic_expanded_terms': len(polynomial.terms),
             'all_variables_live': True, 'elimination_steps': history or [],
             'parent_row_restoration': restore_results}
    write(ROOT/'integer_forms'/f'{name}.json', out)
    write(ROOT/'integer_forms'/f'{name}_expanded.json', polynomial.records())
    write(ROOT/'certificates'/f'{name}_audit.json', audit)
    return audit


def main():
    variables, rows = source38()
    audits = [packet('quartic38', variables, rows, 4, {'tau': 4}, 1)]
    # Centering is an integral triangular coordinate automorphism.
    vs = ['tau_tail' if x == 'tau' else x for x in variables]
    centering = parse('tau_tail+P-eta-zeta')
    rs = [r.substitute({'tau': centering}) for r in rows]
    restoration = {v: (centering if v == 'tau' else Poly.symbol(v)) for v in variables}
    history = [{'triangular_change': 'tau=tau_tail+P-eta-zeta', 'integral_inverse': True}]
    for v, rhs in [
        ('P', 'eta+zeta+E*(c-eta)'), ('F2', 'f**2'), ('g', 'y**2-V**2'),
        ('X', '2*u**2'), ('N', '(beta*J+1)*(L+1)'), ('C2', 'c**2')]:
        vs, rs = eliminate(vs, rs, v, rhs, history, restoration)
    require(len(vs) == 32 and len(rs) == 19, 'S32 dimensions')
    audits.append(packet('sextic32', vs, rs, 6, {'r': 2, 'c': 4}, 4,
                         history, restoration, rows))
    vs, rs = list(variables), list(rows)
    restoration = {v: Poly.symbol(v) for v in variables}
    history = []
    for v, rhs in [
        ('N', '(beta*J+1)*(L+1)'), ('C2', 'c**2'), ('F2', 'f**2'),
        ('g', 'y**2-V**2'), ('X', '2*u**2'),
        ('zeta', 'P-E*(c-eta)-eta'), ('Baux', 'I**2'),
        ('D', '2*u**2+a*c+gamma*(4*a+3)'), ('Delta', 'a**2+4*a+3'),
        ('P', '1-V+j*c+h*E+E*(c-eta)'), ('L', '(beta*J+1)**2-1')]:
        vs, rs = eliminate(vs, rs, v, rhs, history, restoration)
    require(len(vs) == 27 and len(rs) == 14, 'O27 dimensions')
    audits.append(packet('octic27', vs, rs, 8, {'a': 4, 'f': 4}, 1,
                         history, restoration, rows))
    write(ROOT/'certificates'/'INTEGER_AUDIT.json', audits)
    print(json.dumps([{k:a[k] for k in ['name','status','variables','residuals','exact_degree','symbolic_expanded_terms']} for a in audits], indent=2))


if __name__ == '__main__':
    main()
