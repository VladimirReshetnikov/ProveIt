#!/usr/bin/env python3
"""Independent signed inverses, entire quartic and literal raw1493 source bridge.

No terminal optimizer, builder or coefficient emitter is imported/executed.
Frozen source-bridge functions are reused only after the entire raw parent is
restored, and their exact source bytes and all whole dependencies are pinned.
"""
import argparse
from collections import Counter, defaultdict
from copy import deepcopy
from hashlib import sha256
import importlib.util
import json
from pathlib import Path
import sys
sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
REPO = ROOT.parents[1]
EXPECTED_PARENT = 'c30bee5671a654988f4ffa1eb5e5b43469b000292f4e78a85f5c062c0239494e'
EXPECTED_CENSUS = dict(variables=613,quadratic_rows=375,exact_degree=4,
    expanded_monomials=9661,max_abs_expanded_coefficient=2445790974704,
    max_abs_row_coefficient=1122540)

def need(ok, message):
    if not ok:
        raise ValueError(message)

def digest(data):
    return sha256(data).hexdigest()

def encoded(value):
    return (json.dumps(value,sort_keys=True,separators=(',',':'))+'\n').encode()

def load(path):
    return json.loads(path.read_bytes())

def poly(terms, count):
    result = defaultdict(int)
    for coefficient, monomial in terms:
        need(type(coefficient) is int and all(type(v) is int and 0 <= v < count for v in monomial),
             'integer coefficient and bounded coordinate indices')
        result[tuple(sorted(monomial))] += coefficient
    return {m:c for m,c in result.items() if c}

def multiply(left, right):
    result = defaultdict(int)
    for m,c in left.items():
        for n,d in right.items():
            result[tuple(sorted(m+n))] += c*d
    return {m:c for m,c in result.items() if c}

def substitute(row, v, restoration):
    result = defaultdict(int)
    for monomial, coefficient in row.items():
        term = {():coefficient}
        for coordinate in monomial:
            term = multiply(term, restoration if coordinate == v else {(coordinate,):1})
        for m,c in term.items():
            result[m] += c
    return {m:c for m,c in result.items() if c}

def degree(row):
    return max((len(m) for m in row),default=0)

def terms(row):
    return [[c,list(m)] for m,c in sorted(row.items())]

def compare_literal_output(parent, child, certificate, rows, deleted):
    count = len(parent['variables'])
    ordered = sorted({v for row in rows.values() for m in row for v in m})
    need(certificate['retained_original_variables'] == ordered,
         'every actual retained parent coordinate and exact order')
    need(set(range(count)) == deleted | set(ordered) and not deleted & set(ordered),
         'every parent coordinate uniquely covered, none unconstrained')
    need(certificate['unconstrained_removed'] == [], 'no unconstrained restoration shortcut')
    need(certificate['retained_original_rows'] == sorted(rows), 'whole surviving-row map')
    remap = {v:i for i,v in enumerate(ordered)}
    expected = [dict(label=parent['residuals'][rid]['label'],
        terms=[[c,[remap[v] for v in m]] for m,c in sorted(row.items())])
        for rid,row in sorted(rows.items())]
    need(child['variables'] == [parent['variables'][v] for v in ordered],
         'complete variable metadata preserved without renaming')
    need(child['residuals'] == expected, 'every substituted source and guard row, no dropped condition')
    need(child['domain'] == parent['domain'] == 'unrestricted integers', 'integer domains')
    for key in set(parent) - {'variables','residuals','metrics'}:
        need(child[key] == parent[key], 'inherited equation metadata '+key)
    return expected

def verify_projection(parent, child, certificate, check_hashes=True):
    count = len(parent['variables'])
    if check_hashes:
        need(digest(encoded(parent)) == certificate['input_sha256'], 'entire input hash')
        need(digest(encoded(child)) == certificate['output_sha256'], 'entire child hash')
    need(certificate['schema'] == 'integer_quadratic_elimination_v1', 'integral inverse schema')
    rows = {i:poly(row['terms'],count) for i,row in enumerate(parent['residuals'])}
    need(all(degree(row) <= 2 for row in rows.values()), 'whole parent is quadratic')
    deleted = set()
    by_degree, by_kind = Counter(), Counter()
    for step in certificate['steps']:
        rid, v = step['row_id'], step['variable']
        need(type(rid) is int and rid in rows and type(v) is int and 0 <= v < count
             and v not in deleted, 'fresh actual pivot coordinate and row')
        recipe = poly(step['restoration'],count)
        operands = {i for m in recipe for i in m}
        need(v not in operands and not operands & deleted, 'inverse has only current other coordinates')
        d = degree(recipe)
        need(d <= 2 and d == step['restoration_degree'] and len(recipe) <= 8,
             'exact degree/support of every integral restoration')
        pivot = {(v,):1}
        for monomial, coefficient in recipe.items():
            pivot[monomial] = pivot.get(monomial,0)-coefficient
        pivot = {m:c for m,c in pivot.items() if c}
        need(rows[rid] in (pivot,{m:-c for m,c in pivot.items()}),
             'whole removed row is exactly a monic integral definition')
        if d == 2:
            need(all(v not in m or len(m) == 1 for i,row in rows.items() if i != rid for m in row),
                 'quadratic inverse has no nonlinear use in any other remaining row')
        new_rows = {}
        for i,row in rows.items():
            if i == rid:
                continue
            image = substitute(row,v,recipe)
            need(degree(image) <= 2, 'every complete substituted row remains quadratic')
            if image:
                new_rows[i] = image
        rows = new_rows
        deleted.add(v)
        need(step['name'] == parent['variables'][v]['name']
             and step['kind'] == parent['variables'][v].get('kind'), 'exact source metadata per inverse')
        by_degree[d] += 1
        by_kind[step['kind']] += 1
    compare_literal_output(parent,child,certificate,rows,deleted)
    actual = dict(input_variables=count,output_variables=len(child['variables']),
        input_rows=len(parent['residuals']),output_rows=len(rows),
        eliminated_coordinates=len(deleted),unconstrained_removed=0,
        by_restoration_degree={str(k):v for k,v in by_degree.items()},by_kind=dict(by_kind),
        max_support=8,affine_support=None,quadratic_first=False,
        max_output_row_terms=max(map(len,rows.values()),default=0))
    for k,v in actual.items():
        need(certificate['metrics'][k] == v, 'independently measured projection statistic '+k)
    return dict(status='PASS',unique_integral_restorations=len(deleted),
                complete_source_coordinates=count,complete_parent_rows=len(parent['residuals']),
                remaining_rows=len(rows),all_guard_rows_included=True,
                no_parent_sign_or_semantic_premise=True), rows, deleted

def full_quartic(child, stored):
    count = len(child['variables'])
    result = defaultdict(int)
    largest_row = 0
    for row in child['residuals']:
        q = poly(row['terms'],count)
        need(degree(q) <= 2, 'literal quadratic child residual')
        largest_row = max(largest_row,max(map(abs,q.values()),default=0))
        for monomial, coefficient in multiply(q,q).items():
            result[monomial] += coefficient
    result = {m:c for m,c in result.items() if c}
    need(stored == dict(schema='sparse_integer_polynomial_v1',domain='unrestricted integers',
                       variables=count,terms=terms(result)), 'every coefficient of the entire quartic')
    need({v for m in result for v in m} == set(range(count)), 'all613 actual unknowns are live')
    metrics = dict(variables=count,quadratic_rows=len(child['residuals']),exact_degree=degree(result),
        expanded_monomials=len(result),max_abs_expanded_coefficient=max(map(abs,result.values())),
        max_abs_row_coefficient=largest_row)
    need(metrics == EXPECTED_CENSUS, 'exact nonzero degree/support/height census')
    for k,v in metrics.items():
        need(child['metrics'][k] == v, 'child metric '+k)
    need(child['metrics']['variable_kinds'] == dict(Counter(v.get('kind') for v in child['variables'])),
         'complete variable-kind census')
    return metrics

def module(name,path):
    spec = importlib.util.spec_from_file_location(name,path)
    obj = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(obj)
    return obj

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path)
    args = parser.parse_args()
    if (HERE/'MANIFEST.json').exists():
        inventory = load(HERE/'MANIFEST.json')['files']
        need({str(p.relative_to(HERE)) for p in HERE.rglob('*') if p.is_file() and p.name!='MANIFEST.json'}
             == set(inventory), 'closed whole candidate inventory')
        for name,h in inventory.items():
            need(digest((HERE/name).read_bytes()) == h, 'sealed candidate member '+name)
    pins = load(HERE/'SOURCE_PINS.json')
    for name,h in pins['files'].items():
        need(digest((ROOT/name).read_bytes()) == h, 'whole frozen source dependency '+name)
    need(pins['source_metadata_or_labels_changed'] is False and pins['guard_exchange_applied'] is False,
         'no ordering/metadata rewrite and no guard exchange')
    source_parent = ROOT/pins['parent']
    copies = {'guarded.json':'guarded.json','domain_certificate.json':'domain_certificate.json',
              'BRIDGE901.json':'BRIDGE901.json','LIFT904.json':'LIFT904.json',
              'PROOF.md':'PARENT_PROOF.md','MANIFEST.json':'PARENT_MANIFEST.json',
              'SOURCE_PINS.json':'PARENT_SOURCE_PINS.json'}
    for original, copied in copies.items():
        need((HERE/'source'/copied).read_bytes() == (source_parent/original).read_bytes(),
             'entire copied immutable parent artifact '+original)
    parent_bytes = (HERE/'source/guarded.json').read_bytes()
    need(digest(parent_bytes) == EXPECTED_PARENT == pins['parent_equation_sha256'],
         'the exact frozen1493 source, with unchanged labels and metadata')
    parent, child = json.loads(parent_bytes), load(HERE/'equation.json')
    certificate, polynomial = load(HERE/'elimination_certificate.json'), load(HERE/'expanded_polynomial.json')
    build = load(HERE/'BUILD.json')
    need(build['configuration'] == dict(max_support=8,affine_support=None,quadratic_first=False),
         'default affine support, no hidden optimizer configuration')
    need(digest((ROOT/'tools/build_retained_radius_default_affine.py').read_bytes()) == build['generator_sha256'],
         'complete generator source pin')
    for name,h in build['sha256'].items():
        need(digest((HERE/name).read_bytes()) == h, 'whole generated artifact '+name)
    projected, rows, deleted = verify_projection(parent,child,certificate)
    metrics = full_quartic(child,polynomial)
    # Only after ALL1493 coordinates/all1255 residuals have been restored do
    # we invoke the pinned literal901/904 bridge. These are independent source
    # identity functions, not the terminal optimizer or its verifier.
    frozen = module('frozen_raw1493_source_bridge',source_parent/'check.py')
    base = ROOT/pins['raw_foundation']
    target_dir = ROOT/pins['foundation901']
    frozen.sealed(source_parent)
    frozen.sealed(base)
    frozen.sealed(target_dir)
    raw = load(base/'source/raw_builder.json')
    body = load(base/'source/natural667.json')
    restoration = load(base/'source/raw_restoration.json')
    target, targetcert = load(target_dir/'guarded.json'), load(target_dir/'domain_certificate.json')
    domain = load(HERE/'source/domain_certificate.json')
    bridge = load(HERE/'source/BRIDGE901.json')
    lift = load(HERE/'source/LIFT904.json')
    b = module('frozen_raw_integer_polynomial_definitions',ROOT/'candidates/retained-radius-bounds/check.py')
    mixed = module('frozen_raw592_affine_definitions',ROOT/'candidates/projected-radius-mixed/check.py')
    domain_result = frozen.domain(raw,body,target,targetcert,parent,domain,b)
    bridge_result = frozen.bridge901(raw,body,target,targetcert,parent,domain,restoration,bridge,mixed,b)
    compact_lift = load(target_dir/'BRIDGE904.json')
    old = load(ROOT/'candidates/projected-radius-main-root-signs/guarded.json')
    need(lift['compact_bridge_sha256'] == digest((target_dir/'BRIDGE904.json').read_bytes())
         and lift['downstream_pointwise967_bridge_sha256']
          == digest((ROOT/'candidates/projected-radius-main-root-signs/BRIDGE967.json').read_bytes()),
         'exact inherited nonpointwise904 and downstream967 bridges')
    lift_result = frozen.lift904(raw,body,targetcert,parent,domain,restoration,lift,compact_lift,old,b)
    raw_export = frozen.raw_export(raw,load(base/'source/gate_ledger.json'),body)
    need(not any(Path(getattr(m,'__file__','') or '').name == 'terminal_elimination.py'
                 for m in list(sys.modules.values()) if m is not None), 'NO terminal optimizer imported')
    rejected = []
    def reject(label, action):
        try:
            action()
        except (ValueError,RuntimeError,KeyError,IndexError,TypeError):
            rejected.append(label)
        else:
            raise ValueError('corruption accepted: '+label)
    corrupt = deepcopy(certificate)
    corrupt['steps'][0]['restoration'][0][0] += 1
    reject('changed integral inverse with hash checks bypassed',
           lambda:verify_projection(parent,child,corrupt,check_hashes=False))
    corrupt_child = deepcopy(child)
    guard_row = next(i for i,row in enumerate(corrupt_child['residuals']) if row['label'].startswith('raw_guard.'))
    corrupt_child['residuals'].pop(guard_row)
    reject('dropped nonnegativity guard after pointwise substitution',
           lambda:compare_literal_output(parent,corrupt_child,certificate,rows,deleted))
    corrupt_child = deepcopy(child)
    corrupt_child['residuals'][0]['terms'][0][0] += 1
    reject('changed surviving residual coefficient',
           lambda:compare_literal_output(parent,corrupt_child,certificate,rows,deleted))
    corrupt_poly = deepcopy(polynomial)
    corrupt_poly['terms'][0][0] += 1
    reject('changed whole quartic coefficient',lambda:full_quartic(child,corrupt_poly))
    bad_bridge = deepcopy(bridge)
    bad_bridge['guard_transfers'][0]['target_auxiliary'][0] += 1
    reject('incorrect literal901 guard-witness transfer',
           lambda:frozen.bridge901(raw,body,target,targetcert,parent,domain,restoration,bad_bridge,mixed,b))
    bad_lift = deepcopy(lift)
    bad_lift['original_q4_need_not_be_nonnegative'] = False
    reject('illicit pointwise old-q4 positivity premise',
           lambda:frozen.lift904(raw,body,targetcert,parent,domain,restoration,bad_lift,compact_lift,old,b))
    result = dict(status='PASS',optimized_python=bool(sys.flags.optimize),metrics=metrics,
        exact_parent_literal_sha256=EXPECTED_PARENT,projection=projected,
        whole_quartic_comparison='PASS: all9661 coefficients',
        actual1493_source_binding=domain_result,complete_raw_export=raw_export,
        literal901_integer_bijection=bridge_result,literal904_nonpointwise_extension=lift_result,
        source_labels_and_metadata_unchanged=True,guard_exchange_applied=False,
        optimizer_imported=False,source_builder_or_emitter_executed=False,
        checker_sha256=digest(Path(__file__).read_bytes()),rejected_corruptions=rejected,
        scope='Exact integral inverse of all880 deletions, complete375 residual/9661 coefficient checks, and whole raw1493 source binding. Restore the literal parent first, then inherit its exact901/nonpointwise904/967 ordinary chain. No pointwise natural claim, Lean/internal-ZFC theorem, or guard-exchange improvement.')
    text = json.dumps(result,indent=2,sort_keys=True)+'\n'
    if args.output:
        args.output.write_text(text)
    print(text,end='')

if __name__ == '__main__':
    main()
