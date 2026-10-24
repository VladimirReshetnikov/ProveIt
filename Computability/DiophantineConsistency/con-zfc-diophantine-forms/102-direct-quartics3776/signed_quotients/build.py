#!/usr/bin/env python3
"""Construct a signed-quotient quartic from the frozen natural parent.

All transformations are on literal quadratic residuals.  No arithmetic
macro is interpreted and no external package is required.
"""
from collections import Counter, defaultdict
from copy import deepcopy
from hashlib import sha256
import json
from pathlib import Path
import argparse

HERE = Path(__file__).resolve().parent
PARENT_SHA256 = "e851ff1d420a39be069e63f6f117557356c38e6d8272a481258fe38cb38dc6ea"
RETAINED_SHA256 = "39b3e264c05180c5d1f9028c48c4a28544d5c7641ce7d6d38fae430414ecf710"


def require(condition, message):
    if not condition:
        raise ValueError(message)


def canonical(terms):
    d = defaultdict(int)
    for coefficient, monomial in terms:
        d[tuple(sorted(monomial))] += coefficient
    return [[c, list(m)] for m, c in sorted(d.items()) if c]


def occurrences(rows):
    out = defaultdict(list)
    for index, row in enumerate(rows):
        for variable in {i for _, m in row['terms'] for i in m}:
            out[variable].append(index)
    return out


def definition(row, variable):
    require([1, [variable]] in row['terms'], 'monic gate output absent')
    rhs = [[-c, m] for c, m in row['terms'] if m != [variable]]
    require(all(variable not in m for _, m in rhs), 'recursive definition')
    return rhs


def substitute(row, variable, rhs):
    out = []
    for c, m in row['terms']:
        if variable not in m:
            out.append([c, m])
        else:
            require(m == [variable], 'only linear wire elimination permitted')
            out.extend([[c*d, n] for d, n in rhs])
    return {'label': row['label'], 'terms': canonical(out)}


def build(retained=False):
    parent_path = HERE/('source/retained/equation.json' if retained else 'source/natural_equation.json')
    parent_hash = RETAINED_SHA256 if retained else PARENT_SHA256
    raw = parent_path.read_bytes()
    require(sha256(raw).hexdigest() == parent_hash, 'frozen parent mismatch')
    parent = json.loads(raw)
    rows = deepcopy(parent['residuals'])
    variables = deepcopy(parent['variables'])
    original_occ = occurrences(rows)
    quotient_pairs = []
    removed_rows, removed_variables = set(), set()
    signed_variables = set()
    wire_eliminations = []

    # Eliminate one-use affine wires that obstruct a direct paired congruence.
    # Their complete definitions are retained in the transformation certificate.
    bridges = set()
    for quotient, metadata in enumerate(variables):
        if '.qp.' not in metadata['name'] and '.qm.' not in metadata['name']:
            continue
        require(len(original_occ[quotient]) == 1, 'nonprivate initial quotient')
        dr = original_occ[quotient][0]
        product_outputs = [m[0] for c, m in rows[dr]['terms'] if c == 1 and len(m) == 1]
        require(rows[dr]['label'] == 'multiplication' and len(product_outputs) == 1,
                'initial quotient multiplication')
        product = product_outputs[0]
        uses = [j for j in original_occ[product] if j != dr]
        require(len(uses) == 1, 'nonprivate initial product')
        row = rows[uses[0]]
        if row['label'] == 'addition':
            outputs = [m[0] for c, m in row['terms'] if c == 1 and len(m) == 1]
            require(len(outputs) == 1, 'bridge output')
            bridges.add(outputs[0])
    require(len(bridges) == (442 if retained else 2), 'bridge count')
    for variable in sorted(bridges):
        uses = original_occ[variable]
        def_rows = [j for j in uses if rows[j]['label'] == 'addition'
                    and [1, [variable]] in rows[j]['terms']]
        require(len(def_rows) == 1 and len(uses) == 2, 'affine bridge shape')
        definition_index = def_rows[0]
        use_index = next(j for j in uses if j != definition_index)
        rhs = definition(rows[definition_index], variable)
        require(all(len(m) <= 1 for _, m in rhs), 'bridge is not affine')
        require(all(c > 0 for c, _ in rhs), 'bridge restoration is not nonnegative')
        rows[use_index] = substitute(rows[use_index], variable, rhs)
        removed_rows.add(definition_index)
        removed_variables.add(variable)
        wire_eliminations.append({'variable': variable, 'definition_row': definition_index,
                                  'use_row': use_index, 'rhs': rhs})

    occ = occurrences([row if j not in removed_rows else {'terms': []}
                       for j, row in enumerate(rows)])
    for plus, metadata in enumerate(variables):
        if '.qp.' not in metadata['name']:
            continue
        minus = plus + 1
        require(variables[minus]['name'] == metadata['name'].replace('.qp.', '.qm.'),
                'quotient pair name mismatch')
        require(len(occ[plus]) == len(occ[minus]) == 1, 'nonprivate quotient')
        definitions, products, factors, final_uses = [], [], [], []
        for quotient in (plus, minus):
            row_index = occ[quotient][0]
            row = rows[row_index]
            require(row['label'] == 'multiplication', 'quotient use is not multiplication')
            outputs = [m[0] for c, m in row['terms'] if c == 1 and len(m) == 1]
            require(len(outputs) == 1, 'quotient product output')
            output = outputs[0]
            rhs = definition(row, output)
            require(all(m.count(quotient) == 1 for _, m in rhs), 'not a multiple of quotient')
            factor = canonical([[c, [i for i in m if i != quotient]] for c, m in rhs])
            require(all(len(m) <= 1 for _, m in factor), 'nonaffine modulus')
            require(all(c > 0 for c, _ in factor), 'modulus is not nonnegative')
            uses = [j for j in occ[output] if j != row_index]
            require(len(uses) == 1, 'nonprivate product output')
            definitions.append(row_index); products.append(output)
            factors.append(factor); final_uses.append(uses[0])
        require(factors[0] == factors[1] and final_uses[0] == final_uses[1],
                'different quotient moduli or use rows')
        use_index = final_uses[0]
        row = rows[use_index]
        p, q = products
        cp = [c for c, m in row['terms'] if m == [p]]
        cm = [c for c, m in row['terms'] if m == [q]]
        require(len(cp) == len(cm) == 1 and cp[0] == -cm[0],
                'quotient products do not occur as opposite linear terms')
        require(all(p not in m or m == [p] for _, m in row['terms'])
                and all(q not in m or m == [q] for _, m in row['terms']), 'nonlinear product use')
        terms = [[c, m] for c, m in row['terms'] if m not in ([p], [q])]
        terms += [[cp[0]*c, sorted(m+[plus])] for c, m in factors[0]]
        rows[use_index] = {'label': row['label'], 'terms': canonical(terms)}
        removed_rows.update(definitions)
        removed_variables.update((minus, p, q))
        signed_variables.add(plus)
        variables[plus] = {'name': metadata['name'].replace('.qp.', '.signed.'),
                           'kind': 'signed_quotient'}
        quotient_pairs.append({'plus': plus, 'minus': minus, 'products': products,
                               'definition_rows': definitions, 'use_row': use_index,
                               'factor': factors[0], 'orientation': cp[0]})

    keep = [i for i in range(len(variables)) if i not in removed_variables]
    renumber = {old: new for new, old in enumerate(keep)}
    core_variables = [variables[i] for i in keep]
    core_rows = []
    for j, row in enumerate(rows):
        if j in removed_rows:
            continue
        require(all(i in renumber for _, m in row['terms'] for i in m),
                'deleted coordinate remains in a row')
        core_rows.append({'label': row['label'],
                          'terms': canonical([[c, [renumber[i] for i in m]] for c, m in row['terms']])})

    # No signed quotient feeds a retained arithmetic gate or a modulus.
    original_quotients = {entry[k] for entry in quotient_pairs for k in ('plus', 'minus')}
    require(all(not (set(m) & original_quotients)
                for entry in quotient_pairs for _, m in entry['factor']), 'signed modulus')
    gate_definitions = set()
    for row in core_rows:
        if row['label'] not in ('addition', 'multiplication'):
            continue
        positives = [(c, m) for c, m in row['terms'] if c > 0]
        require(len(positives) == 1 and positives[0][0] == 1
                and len(positives[0][1]) == 1, 'monic retained gate')
        output = positives[0][1][0]
        require(core_variables[output]['kind'] == 'gate' and output not in gate_definitions,
                'unique retained gate definition')
        for c, m in row['terms']:
            if m == [output]:
                continue
            require(c < 0 and all(i < output and core_variables[i]['kind'] != 'signed_quotient'
                                 for i in m), 'retained gate not naturally restorable')
        gate_definitions.add(output)
    require(gate_definitions == {i for i, v in enumerate(core_variables) if v['kind'] == 'gate'},
            'every retained gate defined')

    # The remaining natural inputs use the universal three-square certificate.
    guarded = [i for i, v in enumerate(core_variables) if v['kind'] in ('outer', 'witness')]
    final_variables, final_rows, guards = deepcopy(core_variables), deepcopy(core_rows), []
    for i in guarded:
        aux = []
        for suffix in 'abc':
            aux.append(len(final_variables))
            final_variables.append({'name': f'nat.{i}.{suffix}', 'kind': 'guard_auxiliary'})
        a, b, c = aux
        final_rows.append({'label': f'nonnegative.{i}', 'terms': canonical([
            [1, [i]], [-1, [a, a]], [-1, [b, b]], [-1, [c, c]], [-1, [c]]])})
        guards.append({'input': i, 'auxiliaries': aux})
    require(len(quotient_pairs) == 221, 'expected 221 pairs')
    require(len(final_variables) == (8759 if retained else 6628)
            and len(final_rows) == (5864 if retained else 3733), 'candidate counts')
    expanded = defaultdict(int)
    for row in final_rows:
        require(all(len(m) <= 2 for _, m in row['terms']), 'nonquadratic residual')
        for a, ma in row['terms']:
            for b, mb in row['terms']:
                expanded[tuple(sorted(ma+mb))] += a*b
    polynomial = [[c, list(m)] for m, c in sorted(expanded.items()) if c]
    used = {i for _, m in polynomial for i in m}
    require(used == set(range(len(final_variables))), 'dead final coordinate')
    metrics = {'variables': len(final_variables), 'quadratic_rows': len(final_rows),
               'exact_degree': max(len(m) for _, m in polynomial),
               'expanded_monomials': len(polynomial),
               'coefficient_height': max(abs(c) for c, _ in polynomial),
               'core_variables': len(core_variables), 'core_rows': len(core_rows),
               'signed_quotients': len(signed_variables), 'natural_inputs_guarded': len(guarded),
               'natural_gate_wires': sum(v['kind'] == 'gate' for v in core_variables),
               'guard_auxiliaries': 3*len(guarded),
               'variable_reduction_from_parent_integer': len(parent['variables'])+3*1670-len(final_variables),
               'row_reduction_from_parent_integer': len(parent['residuals'])+1670-len(final_rows)}
    equation = {'schema': 'finite_quadratic_residuals_v1', 'domain': 'unrestricted integers',
                'polynomial': 'sum(square(row) for row in residuals)',
                'parent_natural_sha256': parent_hash,
                'variables': final_variables, 'residuals': final_rows,
                'natural_input_guards': guards, 'metrics': metrics}
    certificate = {'parent_natural_sha256': parent_hash,
                   'affine_wire_eliminations': wire_eliminations,
                   'signed_quotient_eliminations': quotient_pairs,
                   'retained_old_variables': keep,
                   'retained_old_rows': [j for j in range(len(rows)) if j not in removed_rows],
                   'core_variable_count': len(core_variables), 'core_row_count': len(core_rows)}
    return equation, {'domain': 'unrestricted integers', 'variables': len(final_variables),
                      'terms': polynomial}, certificate, metrics


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--retained', action='store_true', help='keep upstream affine wires')
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    eq, poly, cert, metrics = build(args.retained)
    output = args.output or HERE/('retained_candidate' if args.retained else 'candidate')
    output.mkdir(exist_ok=True)
    hashes = {}
    for name, value in [('equation.json', eq), ('expanded_polynomial.json', poly),
                        ('transformation_certificate.json', cert)]:
        raw = (json.dumps(value, sort_keys=True, separators=(',', ':'))+'\n').encode()
        (output/name).write_bytes(raw)
        hashes[name] = sha256(raw).hexdigest()
    receipt = {'status': 'PASS', 'metrics': metrics, 'sha256': hashes,
               'parent_sha256': eq['parent_natural_sha256'],
               'scope': 'Literal row transformation and exact full quartic expansion; semantic proof supplied separately.'}
    (output/'BUILD.json').write_text(json.dumps(receipt, indent=2, sort_keys=True)+'\n')
    print(json.dumps(receipt, indent=2, sort_keys=True))


if __name__ == '__main__':
    main()
