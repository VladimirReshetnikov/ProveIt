#!/usr/bin/env python3
"""Independent exact checker for the recycled-quotient direct polynomials.

No producer, search routine, or other verifier is imported. The source delta
is replayed from the frozen parent; unit projections and integral shears are
checked exactly. Final DAGs are checked against certified polynomial
restorations and source rows, not merely sampled. Modular certificates prove
exact degree and actual input dependence. The ordinary unbounded arithmetic
and inherited logical calibration remain separate proof obligations.
"""
from collections import Counter
from copy import deepcopy
import argparse
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parent


def need(value, message):
    if not value:
        raise ValueError(message)


def read(path):
    return json.loads(path.read_text())


def poly(terms):
    result = {}
    for c, monomial in terms:
        need(isinstance(c, int) and isinstance(monomial, list), 'Bad sparse row')
        monomial = tuple(sorted(monomial))
        result[monomial] = result.get(monomial, 0) + c
    return {m:c for m,c in result.items() if c}


def plus(a, b):
    out = a.copy()
    for m,c in b.items():
        out[m] = out.get(m,0)+c
    return {m:c for m,c in out.items() if c}


def times(a, b):
    out = {}
    for m,c in a.items():
        for n,d in b.items():
            key = tuple(sorted(m+n))
            out[key] = out.get(key,0)+c*d
    return {m:c for m,c in out.items() if c}


def scale(a, coefficient):
    return {m:coefficient*c for m,c in a.items() if coefficient*c}


def replace(a, variable, expression):
    powers = {0:{():1}}
    out = {}
    for monomial, coefficient in a.items():
        exponent = monomial.count(variable)
        for j in range(1, exponent+1):
            if j not in powers:
                powers[j] = times(powers[j-1], expression)
        tail = tuple(x for x in monomial if x != variable)
        out = plus(out, times({tail:coefficient}, powers[exponent]))
    return out


def pivot(rows, row_number, variable, restoration):
    row = rows[row_number]
    coefficient = row.get((variable,), 0)
    need(coefficient in (-1,1), 'Pivot coefficient is not a unit')
    need(all(variable not in m for m in row if m != (variable,)),
         'Pivot variable occurs nonlinearly')
    expected = {m:-coefficient*c for m,c in row.items() if m != (variable,)}
    need(restoration == expected, 'False integer restoration')
    rows = [replace(r, variable, restoration) for r in rows]
    need(not rows[row_number], 'Projected row did not vanish')
    return rows


def reduce_rows(template, rows, kept_rows, kept_variables):
    need(len(kept_rows) == len(set(kept_rows)), 'Repeated retained row')
    need(len(kept_variables) == len(set(kept_variables)), 'Repeated retained coordinate')
    need(all(not rows[j] for j in set(range(len(rows)))-set(kept_rows)),
         'Discarded nonzero row')
    renumber = {v:i for i,v in enumerate(kept_variables)}
    reduced = []
    for j in kept_rows:
        need(all(v in renumber for m in rows[j] for v in m),
             'Discarded coordinate remains in a retained row')
        reduced.append({'label':template['residuals'][j]['label'],
                        'terms':[[c,[renumber[v] for v in m]]
                                 for m,c in sorted(rows[j].items())]})
    return {'variables':[template['variables'][v] for v in kept_variables],
            'residuals':reduced}


def same_mathematics(a, b):
    return (a['variables'] == b['variables'] and
            len(a['residuals']) == len(b['residuals']) and
            all(x['label'] == y['label'] and poly(x['terms']) == poly(y['terms'])
                for x,y in zip(a['residuals'],b['residuals'])))


def inherited_projection(factored, projection, translations, affine):
    rows = [poly(r['terms']) for r in factored['residuals']]
    for step in projection['steps']:
        rows = pivot(rows, step['row_id'], step['variable'], poly(step['restoration']))
    stage = reduce_rows(factored, rows, projection['retained_original_rows'],
                        projection['retained_original_variables'])
    rows = [poly(r['terms']) for r in stage['residuals']]
    for variable, amount in translations['shifts']:
        rows = [replace(r, variable, {(variable,):1, ():amount}) for r in rows]
    stage['residuals'] = [{'label':r['label'], 'terms':[[c,list(m)] for m,c in sorted(p.items())]}
                          for r,p in zip(stage['residuals'], rows)]
    translated_stage = deepcopy(stage)
    for step in affine['operations']:
        kind = step['type']
        if kind == 'translation':
            variable = step['variable']
            expression = {(variable,):1, ():step['delta']}
            rows = [replace(r, variable, expression) for r in rows]
        elif kind == 'shear':
            variable = step['variable']
            expression = poly(step['restoration'])
            need(expression.get((variable,)) in (-1,1), 'Nonintegral shear inverse')
            need(all(variable not in m for m in expression if m != (variable,)),
                 'Nonlinear self-reference in shear')
            rows = [replace(r, variable, expression) for r in rows]
        elif kind == 'row_add':
            target, source = step['target'], step['source']
            need(target != source, 'Noninvertible self-row operation')
            rows[target] = plus(rows[target], scale(rows[source], step['multiple']))
        elif kind == 'projection':
            rows = pivot(rows, step['row'], step['variable'], poly(step['restoration']))
        else:
            raise ValueError('Unknown affine certificate operation')
    final = reduce_rows(stage, rows, affine['retained_rows'], affine['retained_variables'])
    return translated_stage, final


def source_replay():
    base = ROOT/'parent166'
    provenance = read(ROOT/'PROVENANCE.json')
    mapping = {
        'stages/compressed/raw_source.json':'raw_source.json',
        'stages/compressed/factored_source.json':'factored_source.json',
        'stages/compressed/factorization_certificate.json':'factorization_certificate.json',
        'stages/compressed/projection_certificate.json':'projection_certificate.json',
        'stages/compressed/translation_certificate.json':'translation_certificate.json',
        'stages/compressed/equation.json':'parent_stage.json',
        'equations/compact/certificate.json':'affine_compact_certificate.json',
        'equations/compact/equation.json':'parent_compact229.json'}
    for source_name, local_name in mapping.items():
        digest = hashlib.sha256((base/local_name).read_bytes()).hexdigest()
        need(digest == provenance['parent_hashes'][source_name], 'Changed frozen parent: '+local_name)
    raw = read(base/'raw_source.json')
    factored = read(base/'factored_source.json')
    projection = read(base/'projection_certificate.json')
    translations = read(base/'translation_certificate.json')
    affine = read(base/'affine_compact_certificate.json')
    old_stage, old_final = inherited_projection(factored, projection, translations, affine)
    need(same_mathematics(old_stage, read(base/'parent_stage.json')),
         'Independent replay differs from the inherited intermediate')
    need(same_mathematics(old_final, read(base/'parent_compact229.json')),
         'Independent replay differs from the inherited compact parent')

    # The new arithmetic delta acts on rows unchanged by the inherited
    # factorization and on no coordinate whose interpretation it changes.
    names = [v['name'] for v in factored['variables']]
    index = {name:j for j,name in enumerate(names)}
    W,A,q,z,L,u,v = [index[name] for name in
        ['shared.W','shared.A','pow2.output','shared.Zminus1','frame.L','free_A.u','free_A.v']]
    raw_names = [v['name'] for v in raw['variables']]
    need(names[:len(raw_names)] == raw_names, 'Unexpected factorization renumbering')
    labels = [r['label'] for r in factored['residuals']]
    frow = labels.index('shared.frame_definition')
    crow = labels.index('free_A.cofinal_constructor')
    for label in ('shared.frame_definition','free_A.cofinal_constructor','shared.last_norm'):
        rr = next(r for r in raw['residuals'] if r['label'] == label)
        fr = next(r for r in factored['residuals'] if r['label'] == label)
        need(poly(rr['terms']) == poly(fr['terms']), 'Factorization does not commute with delta')
    old_frame = poly(factored['residuals'][frow]['terms'])
    need(old_frame.get((W,)) == 1, 'Wrong frame definition')
    W0 = {m:-c for m,c in old_frame.items() if m != (W,)}
    need(all(W not in m and A not in m and u not in m and v not in m for m in W0),
         'Recursive or center-dependent magnitude bound')
    squares = set(read(base/'factorization_certificate.json')['square_variables'])
    need(not squares.intersection({i for m in W0 for i in m}),
         'Magnitude uses a coordinate reinterpreted by factorization')
    old_center = poly(factored['residuals'][crow]['terms'])
    need(old_center == {(A,):1,(L,L):-1,(u,u):-1,(v,v):-1}, 'Wrong old center')
    changed = deepcopy(factored)
    changed['residuals'][frow]['terms'] = [[c,list(m)] for m,c in sorted(
        plus({(W,):1}, times({(q,):-1}, W0)).items())]
    changed['residuals'][crow]['terms'] = [[c,list(m)] for m,c in sorted(
        {(A,):1,(L,L):-1,(z,z):-8,(z,):-8,():-2}.items())]
    _, result = inherited_projection(changed, projection, translations, affine)
    dead = {j for j,d in enumerate(result['variables']) if d['name'] in ('free_A.u','free_A.v')}
    need(len(dead) == 2, 'Private center coordinate count changed')
    rows = [poly(r['terms']) for r in result['residuals']]
    need(all(not dead.intersection(m) for r in rows for m in r), 'Removed center still occurs')
    result = reduce_rows(result, rows, list(range(len(rows))),
                         [j for j in range(len(result['variables'])) if j not in dead])
    supplied = read(ROOT/'source227.json')
    need(same_mathematics(result, supplied), 'New 227-coordinate source is not the literal replay')
    need(len(supplied['variables']) == 227 and len(supplied['residuals']) == 175,
         'Unexpected source size')
    return supplied, {'parent_files_authenticated':len(mapping),
                      'parent_projection_replay':'exact', 'new_source_replay':'exact',
                      'source_variables':227, 'source_rows':175,
                      'new_frame':'W=q*W0', 'new_center':'A=L^2+2(2z+1)^2'}


class Canonical:
    """Associative/commutative reflection, without polynomial expansion.

    Only flattening sums/products and exact constant folding are used.
    This is enough to verify a literal polynomial evaluator after its
    restoration subexpressions are shared. No probabilistic identity test.
    """
    def __init__(self):
        self.forms = []
        self.ids = {}

    def intern(self, form):
        if form not in self.ids:
            self.ids[form] = len(self.forms)
            self.forms.append(form)
        return self.ids[form]

    def const(self, value):
        return self.intern(('const', value))

    def input(self, number):
        return self.intern(('input', number))

    def operate(self, op, left, right):
        flattened = Counter()
        constant = 0 if op == 'add' else 1
        for child in (left,right):
            form = self.forms[child]
            children = form[1] if form[0] == op else ((child,1),)
            for item,multiplicity in children:
                f = self.forms[item]
                if f[0] == 'const':
                    constant = (constant+f[1]*multiplicity if op == 'add'
                                else constant*pow(f[1],multiplicity))
                else:
                    flattened[item] += multiplicity
        if op == 'mul' and constant == 0:
            return self.const(0)
        if constant != (0 if op == 'add' else 1) or not flattened:
            flattened[self.const(constant)] += 1
        if len(flattened) == 1:
            item,multiplicity = next(iter(flattened.items()))
            if multiplicity == 1:
                return item
        return self.intern((op,tuple(sorted(flattened.items()))))


def final_check(source, directory, circuit_override=None, projection_override=None):
    circuit = read(directory/'circuit.json') if circuit_override is None else circuit_override
    certificate = read(directory/'projection.json') if projection_override is None else projection_override
    certificates = read(directory/'certificates.json')
    metrics = read(directory/'METRICS.json')
    rows = [poly(r['terms']) for r in source['residuals']]
    size = len(source['variables'])
    definitions, used_rows = {}, set()
    for p in certificate['pivots']:
        row_number, variable = p['row'], p['variable']
        need(0 <= row_number < len(rows) and 0 <= variable < size, 'Invalid pivot index')
        need(row_number not in used_rows and variable not in definitions, 'Repeated pivot')
        row = rows[row_number]
        coefficient = row.get((variable,),0)
        need(coefficient in (-1,1), 'Nonunit selected pivot')
        need(all(variable not in m for m in row if m != (variable,)), 'Nonlinear selected pivot')
        expected = {m:-coefficient*c for m,c in row.items() if m != (variable,)}
        need(poly(p['restoration']) == expected, 'False selected restoration')
        definitions[variable] = expected
        used_rows.add(row_number)
    free = [v for v in range(size) if v not in definitions]
    retained = [r for r in range(len(rows)) if r not in used_rows]
    need(certificate['free'] == free and certificate['retained_rows'] == retained,
         'Incomplete coordinate/row partition')
    active, finished = set(), set()
    def visit(v):
        need(v not in active, 'Cyclic restoration')
        if v in finished or v not in definitions:
            return
        active.add(v)
        for dep in {i for m in definitions[v] for i in m}:
            visit(dep)
        active.remove(v)
        finished.add(v)
    for v in definitions:
        visit(v)
    need(circuit['variables'] == [source['variables'][v]['name'] for v in free],
         'False final coordinate list')
    need(circuit['domain'] == 'unrestricted integers', 'Domain silently altered')
    need(certificate['variables'] == len(free) and certificate['residuals'] == len(retained),
         'Wrong certificate dimension')

    nodes = circuit['nodes']
    canon = Canonical()
    reflected, degrees, heights = [], [], []
    for j,node in enumerate(nodes):
        op = node[0]
        if op == 'input':
            need(len(node) == 2 and 0 <= node[1] < len(free), 'Bad independent input')
            reflected.append(canon.input(node[1])); degrees.append(1); heights.append(1)
        elif op == 'const':
            need(len(node) == 2 and isinstance(node[1],int), 'Noninteger literal')
            reflected.append(canon.const(node[1])); degrees.append(0); heights.append(abs(node[1]))
        else:
            need(op in ('add','mul') and len(node) == 3 and all(0 <= z < j for z in node[1:]),
                 'Bad or nontopological arithmetic node')
            x,y = node[1:]
            reflected.append(canon.operate(op,reflected[x],reflected[y]))
            degrees.append(max(degrees[x],degrees[y]) if op == 'add' else degrees[x]+degrees[y])
            heights.append(heights[x]+heights[y] if op == 'add' else heights[x]*heights[y])
    coords = circuit['source_coordinate_roots']
    need(len(coords) == size and all(0 <= n < len(nodes) for n in coords), 'Wrong restoration roots')
    coord = [reflected[n] for n in coords]
    for i,v in enumerate(free):
        need(coord[v] == canon.input(i), 'Free input was transformed or constrained')
    def reflect_polynomial(p):
        total = canon.const(0)
        for monomial, coefficient in sorted(p.items()):
            term = canon.const(coefficient)
            for v in monomial:
                term = canon.operate('mul',term,coord[v])
            total = canon.operate('add',total,term)
        return total
    for v,expression in definitions.items():
        need(coord[v] == reflect_polynomial(expression), 'DAG has a false restoration')
    residual_roots = circuit['residual_roots']
    need(len(residual_roots) == len(retained), 'Wrong residual count')
    for row_number,root in zip(retained,residual_roots):
        need(reflected[root] == reflect_polynomial(rows[row_number]), 'DAG has a false residual')
    total = canon.const(0)
    for root in residual_roots:
        square = canon.operate('mul',reflected[root],reflected[root])
        total = canon.operate('add',total,square)
    need(reflected[circuit['output']] == total, 'Output is not the sum of residual squares')
    need(2*max(degrees[r] for r in residual_roots) == certificate['degree_bound'],
         'Degree upper bound differs from literal DAG')

    # Nonzero leading coefficient along an integer linear ray certifies one
    # residual has maximal degree. Over Z, its square cannot cancel against
    # the squares of the other real leading homogeneous forms.
    dc = certificates['degree']
    mod = dc['modulus']
    need(mod > 1 and len(dc['ray']) == len(free), 'Invalid degree test ring')
    leading = []
    for j,node in enumerate(nodes):
        op = node[0]
        if op == 'input':
            leading.append(dc['ray'][node[1]] % mod)
        elif op == 'const':
            leading.append(node[1] % mod)
        elif op == 'mul':
            leading.append(leading[node[1]]*leading[node[2]] % mod)
        else:
            x,y = node[1:]
            leading.append(((leading[x] if degrees[x] == degrees[j] else 0)
                           +(leading[y] if degrees[y] == degrees[j] else 0)) % mod)
    dr = dc['residual_node']
    need(dr == residual_roots[dc['residual_number']], 'Wrong designated residual')
    need(degrees[dr] == dc['degree'] == max(degrees[r] for r in residual_roots),
         'Degree witness does not attain upper bound')
    need(leading[dr] == dc['leading_coefficient'] and leading[dr] != 0,
         'Degree coefficient is zero or incorrect')
    exact_degree = 2*dc['degree']

    # Forward dual arithmetic is independent of the producer's reverse AD.
    occurrence = certificates['occurrence']
    mod = occurrence['modulus']; point = occurrence['point']; n = len(free)
    need(mod > 1 and len(point) == n, 'Invalid occurrence certificate')
    values, gradients = [], []
    for node in nodes:
        op = node[0]
        if op == 'input':
            values.append(point[node[1]] % mod)
            g = [0]*n; g[node[1]] = 1; gradients.append(g)
        elif op == 'const':
            values.append(node[1] % mod); gradients.append([0]*n)
        else:
            x,y = node[1:]
            if op == 'add':
                values.append((values[x]+values[y]) % mod)
                gradients.append([(a+b) % mod for a,b in zip(gradients[x],gradients[y])])
            else:
                values.append(values[x]*values[y] % mod)
                gradients.append([(a*values[y]+values[x]*b) % mod
                                  for a,b in zip(gradients[x],gradients[y])])
    gradient = gradients[circuit['output']]
    need(gradient == occurrence['gradient'] and all(gradient), 'False input-dependence certificate')
    live = {circuit['output']}
    for j in range(len(nodes)-1,-1,-1):
        if j in live and nodes[j][0] in ('add','mul'):
            live.update(nodes[j][1:])
    counted = {
        'variables':n, 'residuals':len(retained), 'exact_degree':exact_degree,
        'live_binary_gates':sum(nodes[j][0] in ('add','mul') for j in live),
        'live_nodes':len(live), 'total_nodes_with_restorations':len(nodes),
        'largest_absolute_literal':max(abs(nodes[j][1]) for j in live if nodes[j][0]=='const'),
        'expanded_height_strictly_less_than_power_of_two':heights[circuit['output']].bit_length()}
    height_key = 'expanded_height_strictly_less_than_power_of_two'
    need(all(counted.get(k) == metrics.get(k) for k in set(counted)|set(metrics)
             if k != height_key), 'Literal counts differ from metrics')
    need(counted[height_key] <= metrics[height_key],
         'Advertised coefficient bound is smaller than the checked bound')
    need(certificates['height_exponent'] == metrics[height_key],
         'Wrong coefficient-height certificate')
    if directory.name == 'P83':
        tight = read(directory/'TIGHT_HEIGHT.json')
        need(int(tight['bound_integer']) == heights[circuit['output']],
             'Tight coefficient-majorant integer does not match the actual DAG')
        need(tight['strict_power_of_two_exponent'] == counted[height_key] == 1568,
             'The advertised 1568-bit strict coefficient bound is not certified')
    return {'profile':directory.name, **counted,
            'unit_pivots':len(definitions), 'source_rows_covered':len(rows),
            'acyclic_restoration':'checked', 'literal_polynomial_reflection':'exact',
            'exact_degree_witness':{'residual':dc['residual_number'],
                                    'modulus':dc['modulus'], 'nonzero_coefficient':leading[dr]},
            'actual_input_dependence':'all nonzero partial derivatives checked',
            'advertised_coefficient_height_exponent':metrics[height_key],
            'exact_integer_l1_majorant_hex':hex(heights[circuit['output']]),
            'circuit_sha256':hashlib.sha256((directory/'circuit.json').read_bytes()).hexdigest()}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--profiles', nargs='+', default=['P83'])
    parser.add_argument('--receipt', type=Path, default=ROOT/'INDEPENDENT_CHECK.json')
    args = parser.parse_args()
    source, replay = source_replay()
    results = [final_check(source, ROOT/name) for name in args.profiles]
    rejected = []
    if 'P83' in args.profiles:
        directory = ROOT/'P83'
        changed_pivot = read(directory/'projection.json')
        changed_pivot['pivots'][0]['restoration'][0][0] += 1
        changed_output = read(directory/'circuit.json')
        changed_output['output'] = changed_output['residual_roots'][0]
        changed_gate = read(directory/'circuit.json')
        gate = next(j for j,r in enumerate(changed_gate['nodes']) if r[0] == 'mul')
        changed_gate['nodes'][gate][0] = 'add'
        controls = [('false_unit_restoration',None,changed_pivot),
                    ('wrong_sum_of_squares_output',changed_output,None),
                    ('wrong_multiplication_gate',changed_gate,None)]
        for label,bad_circuit,bad_projection in controls:
            try:
                final_check(source,directory,bad_circuit,bad_projection)
            except (ValueError,KeyError,IndexError):
                rejected.append(label)
            else:
                raise ValueError('Accepted deliberate corruption: '+label)
    receipt = {'source_replay':replay, 'profiles':results,
               'deliberate_corruptions_rejected':rejected,
               'scope':'Exact finite algebra. New arithmetic and inherited logical calibration are ordinary proofs, not newly kernel checked.'}
    args.receipt.write_text(json.dumps(receipt,indent=2,sort_keys=True)+'\n')
    print(json.dumps(receipt,indent=2))


if __name__ == '__main__':
    main()
