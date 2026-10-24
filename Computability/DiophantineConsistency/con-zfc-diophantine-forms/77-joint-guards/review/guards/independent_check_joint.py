#!/usr/bin/env python3
"""Independent joint-positivity audit; imports only this reviewer's own ring."""
from collections import defaultdict
from pathlib import Path
from math import isqrt
import hashlib
import json
from independent_check import (HERE, G, need, parse, mul, add, neg, power, const,
                               substitute, symbols, degree, sos, metric, native_recipe)

J = G.parent/'joint'


def load(path):
    return json.loads(path.read_text())


def main():
    pin = load(J/'SOURCE_PIN.json')
    raw = (J/'upstream/determinant26_octic.json').read_bytes()
    need(hashlib.sha256(raw).hexdigest() == pin['sha256'], 'joint parent pin')
    need(raw == (G/'determinant26_octic.json').read_bytes(), 'joint parent is the independently audited octic')
    parent = json.loads(raw)
    old = list(map(parse, parent['residuals']))
    q = parse('beta*(3*J3+1)+1')
    C = add(q, parse('-F-alpha'))
    U = parse('cone_A*F')
    W = mul(parse('cone_B'), C)
    det = add(mul(U, W), neg(power(add(q, neg(add(U, W))), 2)))
    z0 = parse('1-V+j*c+h*E-eta')
    signed_product = mul(parse('eta'), z0)
    old_pos = parse('1+eta_zeta_pos1**2+eta_zeta_pos2**2+eta_zeta_pos3*(eta_zeta_pos3+1)')
    det_pos = parse('1+cone1**2+cone2**2+cone3*(cone3+1)')
    need(old[-2] == add(signed_product, neg(old_pos)), 'exact old eta-zeta positivity guard')
    need(old[-1] == add(det, neg(det_pos)), 'exact old determinant positivity guard')
    private = {'eta_zeta_pos1','eta_zeta_pos2','eta_zeta_pos3','cone1','cone2','cone3'}
    common = [v for v in parent['variables'] if v not in private]
    need(len(common) == 20, 'twenty inherited arithmetic coordinates')
    added = ['pair_root','pair_pos1','pair_pos2','pair_pos3']
    pos = parse('1+pair_pos1**2+pair_pos2**2+pair_pos3*(pair_pos3+1)')
    metrics = []
    data_by_name = {}
    for name, retained in [('joint25_octic',True), ('joint24_degree12',False)]:
        data = load(J/(name+'.json'))
        data_by_name[name] = data
        need(data['fixed_numerals'] == parent['fixed_numerals'], name+' unchanged complete ports')
        for port, path in data['coefficient_binding']['ports'].items():
            need((J/path).resolve() == (G/parent['coefficient_binding']['ports'][port]).resolve(),
                 name+' exact payload target '+port)
        need((J/data['coefficient_binding']['manifest']).resolve() == (G/'COEFFICIENT_BINDING.json').resolve(),
             name+' full coefficient manifest')
        want_variables = common + (['zeta'] if retained else []) + added
        need(data['variables'] == want_variables, name+' exact declared coordinate order')
        Y = parse('eta*zeta') if retained else signed_product
        expected_guard = add(add(mul(det,Y), neg(power(add(parse('pair_root**2+1'),neg(add(det,Y))),2))),neg(pos))
        expected_rows = old[:-2] + ([add(parse('zeta'),neg(z0))] if retained else []) + [expected_guard]
        actual_rows = list(map(parse,data['residuals']))
        need(actual_rows == expected_rows, name+' every row is exactly the intended composition')
        need(not set().union(*(symbols(r) for r in actual_rows)).intersection(private),name+' deleted guard coordinates absent')
        data['equation_count'] = data['residual_count']
        metrics.append(metric(data))
        if retained:
            need(degree(expected_guard,set(want_variables)) == 4,name+' quartic pair row')
            need(data['zeta_restoration'] and parse(data['zeta_restoration']) == z0,name+' monic zeta restoration')
        else:
            homogeneous6 = {m:c for m,c in expected_guard.items() if sum(v in set(want_variables) for v in m)==6}
            need(homogeneous6 == parse('-eta**2*(E*h+c*j)**2'),name+' exact leading homogeneous pair row')
        mutated = actual_rows[:-1]+[add(actual_rows[-1],const(1))]
        need(mutated != expected_rows,name+' altered guard is rejected')
    rows25 = list(map(parse,data_by_name['joint25_octic']['residuals']))
    rows24 = list(map(parse,data_by_name['joint24_degree12']['residuals']))
    projected = [substitute(row, {'zeta':z0}) for row in rows25]
    need([i for i,row in enumerate(projected) if not row] == [11], 'exactly the zeta definition vanishes')
    need([row for row in projected if row] == rows24, '25-to-24 projection exactly matches all rows')
    # Lower projections use a reversible row operation before monic elimination.
    strong = parse('I**2-(a**2+4*a+3)*(f**2-1)')
    auxiliary = parse('I**2*(V**2-y**2)+y**2-1')
    reduced = parse('(a**2+4*a+3)*(f**2-1)*(V**2-y**2)+y**2-1')
    need(rows24[7] == parse('V+c-f*o') and rows24[8] == parse('I-(2*r+1)*c**2'),
         'exact lower-projection monic definitions')
    need(rows24[9] == strong and rows24[10] == auxiliary, 'exact strong and auxiliary rows')
    need(add(auxiliary,neg(reduced)) == mul(parse('V**2-y**2'),strong),
         'two-sided ideal row operation with the strong row retained')
    lower_receipts = []
    for name, remove_i in [('joint23_degree12',False),('joint22_degree16',True)]:
        data = load(J/(name+'.json'))
        replacements = {'V':parse('f*o-c')}
        original = list(rows24)
        if remove_i:
            replacements['I'] = parse('(2*r+1)*c**2')
            original[10] = reduced
        images = [substitute(row,replacements) for row in original]
        zeros = [i for i,row in enumerate(images) if not row]
        need(zeros == ([7,8] if remove_i else [7]),name+' exactly the monic definition rows vanish')
        need([r for r in images if r] == list(map(parse,data['residuals'])),name+' every projected row exact')
        need(data['variables'] == [v for v in data_by_name['joint24_degree12']['variables'] if v not in replacements],
             name+' exact variable deletion')
        need({k:parse(v) for k,v in data['full_parent_restoration'].items()} == replacements,
             name+' advertised restoration is the actual integer polynomial map')
        need(data['fixed_numerals'] == parent['fixed_numerals'] and
             data['coefficient_binding'] == data_by_name['joint24_degree12']['coefficient_binding'],
             name+' unchanged exact numeral binding')
        data['equation_count'] = data['residual_count']
        data_by_name[name] = data
        metrics.append(metric(data))
        lower_receipts.append({'name':name,'identically_deleted_rows':zeros,
                               'row_operation':'aux_new=aux_old-(V^2-y^2)*strong; strong retained' if remove_i else 'none'})
    # Same count/degree, but retaining V and eliminating I alone is sparser.
    name = 'joint23_degree12_eliminate_I'
    data = load(J/(name+'.json'))
    alternate_rows = list(rows24)
    alternate_rows[10] = reduced
    images = [substitute(row,{'I':parse('(2*r+1)*c**2')}) for row in alternate_rows]
    need([i for i,row in enumerate(images) if not row] == [8],name+' exact monic row deletion')
    need([row for row in images if row] == list(map(parse,data['residuals'])),name+' exact alternate rows')
    need(data['variables'] == [v for v in data_by_name['joint24_degree12']['variables'] if v!='I'],
         name+' exact alternate variables')
    data['equation_count'] = data['residual_count']
    data['residual_degrees'] = [degree(parse(row),set(data['variables'])) for row in data['residuals']]
    need(data['degree_witness']['coefficient_expression']=='1',name+' uniform witness expression')
    data['degree_witness']['coefficient'] = 1
    data_by_name[name] = data
    metrics.append(metric(data))
    _, totals, values = native_recipe()
    modulus = 1000000007
    residues = {p:v%modulus for p,v in values.items()}
    for item in metrics:
        data = data_by_name[item['name']]
        variables = set(data['variables'])
        full = sos(list(map(parse,data['residuals'])))
        groups = defaultdict(int)
        for m,c in full.items():
            unknown = tuple(v for v in m if v in variables)
            term = c%modulus
            for v in m:
                if v not in variables:
                    term = term*residues[v]%modulus
            groups[unknown] = (groups[unknown]+term)%modulus
        need(all(groups.values()),item['name']+' each specialized coefficient has nonzero exact residue')
        item['exact_monomials_after_authentic_numeral_specialization'] = len(groups)
        item['nonzero_coefficient_residue_certificate'] = {'modulus':modulus,'coefficient_count':len(groups)}
    # Diagnostics supplement the full all-integer proof, never replace it.
    sound_cases = 0
    for x in range(-20,21):
        for y in range(-20,21):
            for t in range(-30,31):
                if x*y-(t*t-x-y+1)**2 > 0:
                    need(x>0 and y>0,'signed pair positivity diagnostic')
                    sound_cases += 1
    converse_cases = 0
    for x in range(1,201):
        for y in range(1,201):
            N=x+y-1
            m=isqrt(N)
            t=m if N-m*m<=m else m+1
            need(x*y-(t*t-N)**2>0,'constructive nearest-square diagnostic')
            converse_cases += 1
    # Missing the offset +1 destroys completeness at (x,y)=(1,1).
    need(max(1-(t*t-2)**2 for t in range(-3,4)) == 0, 'pair offset cannot be omitted')
    files = [p for p in J.rglob('*') if p.is_file() and p.suffix in ('.json','.md','.py')]
    report = {'status':'PASS','optimized_python':not __debug__,
              'implementation':'Independent reviewer AST/sparse ring; no construction-builder or construction-checker imports',
              'metrics':metrics,'parent_sha256':pin['sha256'],'coefficient_raw_bytes':totals['determinant'],
              'lower_projection_receipts':lower_receipts,
              'projection':'Only row 11 (zero based) vanishes under zeta=1-V+j*c+h*E-eta; other rows equal joint24_degree12 exactly.',
              'diagnostics':{'signed_positive_cases':sound_cases,'constructive_positive_pairs':converse_cases},
              'negative_control':'Omitting +1 in t^2-x-y+1 loses x=y=1; nearest square to 2 has squared error 1, so xy-error^2=0.',
              'file_sha256':{str(p.relative_to(J)):hashlib.sha256(p.read_bytes()).hexdigest() for p in files},
              'scope':'Finite literal identities and exact coefficient certificates, accompanied by the universal mathematical proof in MATHEMATICAL_REVIEW.md. Not a kernel proof or global minimum.'}
    (HERE/('JOINT_CHECKS_OPTIMIZED.json' if not __debug__ else 'JOINT_CHECKS.json')).write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({'status':'PASS','metrics':metrics,'diagnostics':report['diagnostics']},indent=2))


if __name__ == '__main__':
    main()
