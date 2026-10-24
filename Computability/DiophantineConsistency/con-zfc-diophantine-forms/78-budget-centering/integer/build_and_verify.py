#!/usr/bin/env python3
"""Exact algebra audit of joint guards and two Pell-root translations.

Python standard library only. The imported polynomial engine is source71.
No bounded consistency search or assertion is used. Mathematical existence
of positivity witnesses and the inherited unbounded compiler/Pell theorem
are proved in PROOF.md and the explicitly identified upstream sources.
"""
from pathlib import Path
import gzip
import hashlib
import importlib.util
import json
import math
from polynomial import Poly, parse, require

ROOT = Path(__file__).resolve().parent
PORTS = ['beta', 'K0', 'MC', 'MF', 'cone_A', 'cone_B']
PRIVATE = [f'{p}{i}' for p in ['cone_pos', 'eta_zeta_pos'] for i in range(1, 4)]
JOINT = ['pair_root', 'guard1', 'guard2', 'guard3']


def write(path, obj):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(obj, indent=2, sort_keys=True)+'\n')


def aliases_common():
    a = {}
    for name, rhs in [
        ('q', 'beta*J+1'), ('k', 'eta+zeta'), ('Y', 'a-E'),
        ('C', 'q-F-alpha'), ('H', '4*a+3'), ('delta', 'a*a+H'),
        ('U', 'cone_A*F'), ('W', 'cone_B*C'),
        ('G', 'U*W-(q-U-W)**2'),
        ('Z', 'eta*zeta'),
        ('R', '((q-1)*(q-F)+alpha)*(q*q-1)+(MC+q*MF)*J'),
        ('new_guard', 'G*Z-(pair_root**2-G-Z+1)**2-1-guard1**2-guard2**2-guard3*(guard3+1)')]:
        a[name] = parse(rhs, a)
    return a


def joint_source():
    packet = json.loads((ROOT/'upstream/quartic38.json').read_text())
    require(packet['variable_count'] == 38 and packet['residual_count'] == 25,
            'literal source dimensions')
    rows = [parse(s) for s in packet['residuals']]
    al = aliases_common()
    for index, what, prefix in [(23, 'G', 'cone_pos'), (24, 'Z', 'eta_zeta_pos')]:
        expected = parse(f'{what}-1-{prefix}1**2-{prefix}2**2-{prefix}3*({prefix}3+1)', al)
        require(rows[index] == expected, 'literal source positivity row '+str(index))
    variables = [v for v in packet['variables'] if v not in PRIVATE]+JOINT
    require(len(variables) == 36, 'joint source variable count')
    rows = rows[:23]+[al['new_guard']]
    return variables, rows


def eliminate(variables, rows, v, rhs, restores, history):
    rhs = parse(rhs)
    require(v not in rhs.symbols(), 'acyclic elimination '+v)
    defining = Poly.symbol(v)-rhs
    hits = [i for i, row in enumerate(rows) if row == defining or row == -defining]
    require(len(hits) == 1, 'unique exact monic definition '+v)
    k = hits[0]
    mapping = {v: rhs}
    new_rows = [row.substitute(mapping) for i, row in enumerate(rows) if i != k]
    for old in restores:
        restores[old] = restores[old].substitute(mapping)
    history.append({'variable': v, 'restoration_at_step': rhs.expression(),
                    'deleted_row_at_step_zero_based': k})
    return [x for x in variables if x != v], new_rows


def audit_restore(source_rows, final_rows, restores):
    results, used = [], []
    for i, row in enumerate(source_rows):
        restored = row.substitute(restores)
        if restored == 0:
            results.append({'joint_source_row': i, 'result': 'zero polynomial'})
        else:
            hits = [j for j, final in enumerate(final_rows) if restored == final or restored == -final]
            require(len(hits) == 1, 'exact source row restoration '+str(i))
            results.append({'joint_source_row': i, 'result': 'final residual', 'index': hits[0]})
            used.append(hits[0])
    require(sorted(used) == list(range(len(final_rows))), 'all final rows restored exactly once')
    return results


def manual_rows(kind):
    a = aliases_common()
    a['X'] = parse('2*u*u')
    if kind == 'degree16_23':
        a['X'] = parse('8*q*q*u*u', a)
        a['w_scale'] = parse('2*q*u*u', a)
    if kind in ('decic24', 'degree16_23'):
        a['c'] = parse('Y*k+eta', a)
        a['V'] = parse('f*o-c', a)
    a['T'] = parse('E*(c-eta)', a)
    a['S'] = parse('X+gamma*H', a)
    expressions = [
        'X-4*q*w_scale',
        'a-E-q**3*(2*v_scale+1)',
        'E-X*Y',
        'c-Y*k-eta',
        'tau**2+(2*tau-k)*T-1',
        '2*a*c*S+S**2-H*c**2-1',
        'k-1-h*E-R',
        '(K0+4*w_scale)*C-(q-1)*z-F',
        'V+c-f*o',
        'V+k-1-c*j-h*E',
        'I-(2*r+1)*c**2',
        'I**2-delta*(f**2-1)',
        'I**2*(V**2-y**2)+y**2-1',
        'new_guard']
    if kind in ('decic24', 'degree16_23'):
        deleted = (3, 8) if kind == 'decic24' else (0, 3, 8)
        expressions = [e for i, e in enumerate(expressions) if i not in deleted]
        expressions[-2] = '(V+y_tail)**2-I**2*y_tail*(2*V+y_tail)-1'
    return [parse(e, a) for e in expressions], expressions, a


def packet(name, variables, rows, degree, coefficient_monomial, coefficient, restores, source, history):
    require(set().union(*(p.symbols() for p in rows))-set(PORTS) == set(variables),
            name+': exactly the declared live coordinates')
    manual, expressions, aliases = manual_rows(name)
    matches = []
    for p in manual:
        hits = [i for i, q in enumerate(rows) if p == q or p == -q]
        require(len(hits) == 1, name+': independently specified formula matches one source residual')
        matches.append(hits[0])
    require(sorted(matches) == list(range(len(rows))), name+': manual formula is complete')
    rows = manual
    polynomial = sum((r*r for r in rows), Poly())
    require(polynomial.degree(variables) == degree, name+': exact symbolic degree')
    require(polynomial.coefficient(coefficient_monomial, variables) == coefficient,
            name+': coefficient independent of every fixed port')
    residual_degrees = [r.degree(variables) for r in rows]
    row_restore = audit_restore(source, rows, restores)
    result = {
        'name': name, 'domain': 'all integers', 'variables': variables,
        'variable_count': len(variables), 'fixed_coefficient_ports': PORTS,
        'fixed_binding': '../coefficients/NEW_BINDING.json',
        'residuals': [r.expression() for r in rows], 'residual_count': len(rows),
        'single_equation': 'sum of squares of all listed residuals = 0',
        'exact_degree': degree,
        'human_residuals': expressions,
        'fully_expanded_aliases': {k:v.expression() for k,v in aliases.items()},
        'source_joint_restoration': {k:v.expression() for k,v in restores.items()},
        'proof_boundary': 'New equivalence to literal source71 Q38 proved here; the Q38-to-Con(ZFC) equivalence imports the named native/compiler/Pell and machine-calibration theorems.'}
    write(ROOT/'generated'/f'{name}.json', result)
    # A fully expanded polynomial over the six fixed numeral ports.
    write(ROOT/'generated'/f'{name}_expanded.json', polynomial.records())
    coefficient_json = coefficient.expression() if isinstance(coefficient, Poly) else coefficient
    audit = {'status':'PASS', 'name':name, 'variables':len(variables), 'residuals':len(rows),
             'exact_degree':degree, 'residual_degrees':residual_degrees,
             'symbolic_port_expansion_terms':len(polynomial.terms),
             'degree_certificate':{'monomial':coefficient_monomial,'coefficient':coefficient_json,
                                   'nonvanishing':'positive at the actual fixed coefficient tuple'},
             'literal_parent_row_restoration':row_restore, 'elimination_steps':history,
             'all_variables_live':True, 'human_formula_agrees_exactly':True}
    write(ROOT/'certificates'/f'{name}_CHECKS.json',audit)
    return audit


def verify_coefficients():
    binding = json.loads((ROOT/'coefficients/NEW_BINDING.json').read_text())
    native = ROOT/'coefficients/recipe/build_coefficients.py'
    spec = importlib.util.spec_from_file_location('source34_recipe',native)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    ports, native_audit = module.construct()
    expected = {'beta':ports['beta'], 'K0':ports['K'], 'MC':ports['MC'],
                'MF':ports['MF_source'], 'cone_A':1<<1113, 'cone_B':1<<666104}
    checks = {}
    for name, record in binding['payloads'].items():
        raw = gzip.decompress((ROOT/'coefficients'/record['path']).read_bytes())
        value = int.from_bytes(raw,'little')
        require(len(raw) == record['raw_bytes'], 'payload length '+name)
        require(hashlib.sha256(raw).hexdigest() == record['raw_sha256'], 'payload digest '+name)
        require(value == expected[name], 'literal coefficient recipe '+name)
        require(value.bit_length() == record['bits'], 'payload bits '+name)
        checks[name] = {'bits':value.bit_length(), 'raw_bytes':len(raw), 'raw_sha256':hashlib.sha256(raw).hexdigest()}
    require(expected['beta'] == (1<<1064921)-1, 'source beta')
    require(0<expected['MC']<expected['beta']<expected['MF']<2*expected['beta'], 'native port bounds')
    result = {'status':'PASS','all_six_actual_payloads_reconstructed':True,
              'raw_bytes':sum(x['raw_bytes'] for x in checks.values()),
              'payloads':checks,'native_basis_checks':native_audit['basis_convolution_checks'],
              'scope':'finite coefficient reconstruction only; not a consistency proof'}
    write(ROOT/'certificates/COEFFICIENT_CHECKS.json',result)
    return result


def finite_diagnostics():
    positives = 0
    for x in range(1,201):
        for y in range(1,201):
            N=x+y-1; m=math.isqrt(N)
            t=m if N-m*m<=m else m+1
            require(x*y-(t*t-x-y+1)**2>0, 'nearest-square completeness diagnostic')
            positives += 1
    signed = 0
    for x in range(-25,26):
        for y in range(-25,26):
            for t in range(-10,11):
                g=x*y-(t*t-x-y+1)**2
                require(g<=0 or (x>0 and y>0), 'joint-guard sign diagnostic')
                signed += 1
    result = {'positive_pairs':positives, 'signed_triples':signed,
              'scope':'diagnostics only; universal statements proved in PROOF.md'}
    write(ROOT/'certificates/FINITE_DIAGNOSTICS.json',result)
    return result


def main():
    pins = json.loads((ROOT/'SOURCE_PINS.json').read_text())
    for item in pins['files']:
        require(hashlib.sha256((ROOT/item['local']).read_bytes()).hexdigest()==item['sha256'],
                'unchanged source '+item['local'])
    variables, source = joint_source()
    rows = list(source)
    shift = parse('tau+E*(c-eta)')
    rows = [p.substitute({'tau':shift}) for p in rows]
    restores = {v:(shift if v=='tau' else Poly.symbol(v)) for v in variables}
    history = [{'triangular_change':'tau_old=tau+E*(c-eta)', 'inverse':'tau=tau_old-E*(c-eta)'}]
    for v,rhs in [
        ('X','2*u**2'), ('C2','c**2'), ('F2','f**2'), ('g','y**2-V**2'),
        ('Baux','I**2'), ('Delta','a**2+4*a+3'),
        ('D','2*u**2+a*c+gamma*(4*a+3)'),
        ('P','eta+zeta+E*(c-eta)'),
        ('N','(beta*J+1)*(L+1)'), ('L','(beta*J+1)**2-1')]:
        variables,rows = eliminate(variables,rows,v,rhs,restores,history)
    require(len(variables)==26 and len(rows)==14, 'octic26 dimensions')
    audit26 = packet('octic26',variables,rows,8,{'pair_root':8},1,restores,source,history)
    tail = parse('V+y_tail')
    variables = ['y_tail' if v=='y' else v for v in variables]
    rows = [p.substitute({'y':tail}) for p in rows]
    restores = {v:p.substitute({'y':tail}) for v,p in restores.items()}
    history = history+[{'triangular_change':'y_old=V+y_tail', 'inverse':'y_tail=y_old-V'}]
    for v,rhs in [('c','(a-E)*(eta+zeta)+eta'), ('V','f*o-(a-E)*(eta+zeta)-eta')]:
        variables,rows = eliminate(variables,rows,v,rhs,restores,history)
    require(len(variables)==24 and len(rows)==12, 'decic24 dimensions')
    audit24 = packet('decic24',variables,rows,10,{'r':2,'a':4,'eta':4},4,restores,source,history)
    dyadic = {'u':parse('2*(beta*J+1)*u'),
              'w_scale':parse('2*(beta*J+1)*u**2')}
    rows23 = [p.substitute(dyadic) for p in rows]
    zeros = [i for i,p in enumerate(rows23) if p==0]
    require(len(zeros)==1, 'one dyadic definition becomes an identity')
    rows23 = [p for p in rows23 if p!=0]
    variables23 = [v for v in variables if v!='w_scale']
    restores23 = {v:p.substitute(dyadic) for v,p in restores.items()}
    history23 = history+[{'canonical_restriction':'u_old=2*q*u; w_scale=2*q*u**2',
                         'scope':'existence equivalence via canonical dyadic witnesses; not a bijection of all old zeros',
                         'deleted_row_at_step_zero_based':zeros[0]}]
    require(len(variables23)==23 and len(rows23)==11, 'degree16_23 dimensions')
    audit23 = packet('degree16_23',variables23,rows23,16,{'J':8,'u':8},parse('4096*beta**8'),
                     restores23,source,history23)
    coefficients = verify_coefficients()
    diagnostics = finite_diagnostics()
    results={'status':'PASS', 'source_snapshot':pins['snapshot'],
             'results':[{k:a[k] for k in ['name','variables','residuals','exact_degree','symbolic_port_expansion_terms','degree_certificate']} for a in [audit26,audit24,audit23]],
             'coefficient_raw_bytes':coefficients['raw_bytes'], 'diagnostics':diagnostics,
             'scope':'Algebra, degrees, restored literal rows, fixed bytes; universal positivity and inherited semantics are separate proof obligations.'}
    write(ROOT/'VERIFICATION.json',results)
    print(json.dumps(results,indent=2))


if __name__=='__main__':
    main()
