#!/usr/bin/env python3
"""Independent source binding and diagnostics for the bootstrap guard exchange.

The unbounded ordinary proof review is in the adjacent Markdown file. This
program does not import the author audit, an emitter, or an optimizer.
"""
import argparse
from collections import Counter
from hashlib import sha256
import importlib.util
import json
from pathlib import Path
import sys
sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[1]
PROOF = 'research/bootstrap-guard-exchange/README.md'
EXPECTED_PROOF = '829b7125dfa1ba9074cc4b93eb247562bebdbc7d7ace0c4edf2b7c1981b8fff3'

def need(value, message):
    if not value:
        raise ValueError(message)

def load(relative):
    return json.loads((ROOT / relative).read_bytes())

def digest(path):
    return sha256(path.read_bytes()).hexdigest()

def pell(base, index):
    x, y = 1, 0
    for _ in range(index):
        x, y = base*x + (base*base-1)*y, x + base*y
    return x, y

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    need(digest(ROOT / PROOF) == EXPECTED_PROOF, 'the reviewed proof bytes')
    for name, value in load('research/bootstrap-guard-exchange/MANIFEST.json')['files'].items():
        need(digest(ROOT / 'research/bootstrap-guard-exchange' / name) == value,
             'the complete frozen research inventory: ' + name)
    for name, value in load('research/bootstrap-guard-exchange/VERIFY.json')['source_pins'].items():
        need(digest(ROOT / name) == value, 'the author receipt binds unchanged source bytes: ' + name)
    for name, value in load('research/main-root-and-modulus-signs/SOURCE_PINS.json')['files'].items():
        need(digest(ROOT / name) == value, 'the inherited whole-source provenance: ' + name)
    helper = ROOT / 'reviews/main-root-modulus-signs-peer.py'
    need(digest(helper) == '2779fc7531543a567270668a668511651979fa447ee72314f1c2d369fc49db21',
         'independent sparse polynomial definitions')
    spec = importlib.util.spec_from_file_location('bootstrap_peer_polynomials', helper)
    p = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(p)
    P, C, V, add, mul = p.P, p.C, p.V, p.plus, p.times
    raw = load('candidates/projected-radius-mixed-bounds/source/raw_builder.json')
    rows = [P(row['terms']) for row in raw['rows']]
    cert = load('research/main-root-and-modulus-signs/CERTIFICATE.json')
    domain = load('candidates/projected-radius-comparison-base/domain_certificate.json')
    old = {g['raw_variable'] for g in domain['guards']}
    new = (old - {694}) | {645}
    need(len(old) == len(new) == 78 and 694 in old and 645 not in old,
         'one exchanged guard, not an omitted hypothesis')
    need(raw['variables'][645] == {'kind': 'witness', 'name': 'shared.Zminus1'},
         'literal replacement coordinate')
    combinations = 0
    def collect(cut, target=None, prefix_only=False):
        nonlocal combinations
        result = {}
        for summand in cut['row_combination']:
            multiplier = P(summand['multiplier'])
            row = rows[summand['row']]
            if prefix_only:
                need(p.vars_(multiplier) | p.vars_(row) <= set(range(643)),
                     'prefix provenance does not refer to either private guard')
            result = add(result, mul(multiplier, row))
        if target is None:
            target = P(cut.get('polynomial', cut.get('expanded_polynomial')))
        need(result == target, 'complete collected original-row identity')
        combinations += 1
        return result
    prefix = cert['prefix_proof']
    lower = {v: 0 for v in prefix['initial_semantic_guard_indices']}
    need(len(lower) == 61 and set(lower) <= new, 'all61 semantic guard premises survive')
    sign_steps = 0
    def positive(poly):
        need(p.vars_(poly) <= set(lower), 'earlier sign dependencies')
        shifted = {}
        for monomial, coefficient in poly.items():
            term = C(coefficient)
            for v in monomial:
                term = mul(term, add(V(v), C(lower[v])))
            shifted = add(shifted, term)
        need(all(c >= 0 for c in shifted.values()) and shifted.get((), 0) > 0,
             'strict positivity from certified earlier lower bounds')
    def sign(step):
        nonlocal sign_steps
        v, c, rhs = step['variable'], step['coefficient'], P(step['rhs'])
        want = add(mul(C(c), V(v)), rhs, -1)
        need(c > 0 and v < 643 and rows[step['row']] in (want, mul(C(-1), want)),
             'actual positive-coefficient prefix pivot')
        if step['kind'] == 'positive_monomials':
            dependencies = {i for m in rhs for i, n in Counter(m).items() if n % 2}
            need(all(c > 0 for c in rhs.values()) and dependencies <= set(lower)
                 and dependencies == set(step['dependencies']), 'all odd powers licensed')
        else:
            need(step['kind'] == 'affine_square'
                 and mul(P(step['square_root']), P(step['square_root'])) == rhs,
                 'domain-independent square identity')
        lower[v] = max(lower.get(v, 0), 0)
        sign_steps += 1
    def bound(step):
        v, L = step['variable'], step['lower']
        factor, rhs = P(step['factor']), P(step['rhs'])
        need(v not in p.vars_(factor) | p.vars_(rhs), 'noncircular lower-bound target')
        collect(step, add(mul(V(v), factor), rhs, -1), True)
        positive(factor)
        positive(add(rhs, mul(C(L-1), factor), -1))
        lower[v] = max(lower.get(v, L), L)
    for step in prefix['preliminary_t_n_bounds']:
        bound(step)
    for stage in prefix['five_stages']:
        for step in stage['preceding_sign_steps']:
            sign(step)
        bound(stage)
    for step in prefix['final_sign_steps']:
        sign(step)
    need(set(lower) == set(range(643)) and lower[4] >= 1 and lower[5] >= 2,
         'whole prefix before either A or modulus orientation')
    pp = cert['positive_prefix']
    collect(pp['canonical_modulus_cut'], prefix_only=True)
    positive(add(P(pp['canonical_modulus_cut']['polynomial']), V(129)))
    strict = {4, 5, 129}
    for step in pp['steps']:
        v, row = step['variable'], rows[step['row']]
        need(row.get((v,)) == 1 and all(v not in m or m == (v,) for m in row),
             'strict constructor unit definition')
        rhs = {m: -c for m, c in row.items() if m != (v,)}
        term = tuple(step['positive_monomial'])
        need(all(c > 0 for c in rhs.values()) and p.vars_(rhs) <= set(lower)
             and rhs.get(term, 0) > 0 and set(term) <= strict,
             'positive constructor has earlier strictly positive summand')
        strict.add(v)
    need(strict == set(pp['known_after'])
         and {s['exponent'][1] for s in raw['seeds']} <= strict,
         'all actual seed exponents strictly positive')
    for name in ('frame_cut', 'bootstrap_norm', 'unit_norm_cut', 'positive_V_product',
                 'comparison_base_constructor', 'comparison_base_congruence'):
        collect(cert[name])
    need(len(cert['frame_arguments']) == 43 and len(set(cert['frame_arguments'])) == 43,
         'all43 distinct actual frame arguments')
    for seed in cert['seeds']:
        need(seed['aliases']['YminusK'] in new, 'all15 index bounds still guarded')
        for cut in seed['cuts'].values():
            collect(cut)
    for entry in cert['moduli']:
        collect(entry['cut'])
    critical = [(0, 5, 4, 6), (1, 92, 86, 93), (2, 103, 4, 104), (9, 531, 122, 560)]
    for call_id, n, k, m in critical:
        actual, entry = raw['powers'][call_id], cert['power_calls'][call_id]
        need([actual[key] for key in ('base', 'exponent', 'output')]
             == [['v', v] for v in (n, k, m)], 'four literal call interfaces')
        need((entry['base'], entry['exponent'], entry['output']) == (n, k, m),
             'four certified interfaces bind the same actual source')
        collect(entry['cut'])
    need(cert['power_calls'][0]['X'] == cert['power_calls'][2]['X'] == 670
         and cert['power_calls'][0]['Y'] == cert['power_calls'][2]['Y'] == 671,
         'the two uses of t share their exact Pell seed')
    sum63 = {}
    for i in (47, 48, 49, 50):
        sum63 = add(sum63, rows[i])
    need(sum63 == P([[1,[63]],[-1,[4]],[-1,[1]],[-1,[2]],[-1,[3]],[-2,[]]]),
         'corrected raw63 constructor')
    gates = {row['gate']: i for i, row in enumerate(raw['rows']) if row.get('gate') is not None}
    for v in range(64, 87):
        need(rows[gates[v]] == add(V(v), mul(V(v-1), V(v-1)), -1),
             'raw86 has23 squarings and no parity premise')
    need(add(rows[86], rows[87]) == P([[1,[103]],[-1,[]],[-1,[5,87]]]),
         'call2 base constructor')
    need(add(rows[88], rows[101]) == P([[1,[122]],[-1,[4]],[-1,[104]],[-2,[]]]),
         'even exponent constructor')
    need(add(add(rows[77], rows[75]), mul(V(87), rows[74]))
         == P([[1,[92]],[-1,[]],[-1,[87,86,86]]]), 'call1 base constructor')
    factorial = prefix['five_stages'][0]
    need(P(factorial['factor']) == add(add(C(1), V(94)), V(95))
         and P(factorial['rhs']) == add(V(93), V(95)), 'early positive factorial inference')
    need(rows[gates[531]] == P([[1,[531]],[-1,[530]],[-1,[]]]) and 530 in strict,
         'contradiction call has base at least2')
    interfaces = load('candidates/projected-radius-mixed/arithmetic_interfaces.json')
    gate_rows = set(interfaces['all_gate_rows'])
    changed, cone = {645}, []
    for v, ri in zip([i for i,x in enumerate(raw['variables'])
                      if x['kind'] in ('gate','square_difference')], interfaces['all_gate_rows']):
        row = rows[ri]
        need(row.get((v,)) in (-1,1) and max(p.vars_(row)) == v
             and all(v not in m or m == (v,) for m in row), 'entire topological gate graph')
        dependencies = p.vars_(row) - {v}
        if dependencies & changed:
            changed.add(v)
            cone.append([v, ri])
    affected = [i for i, row in enumerate(rows) if i not in gate_rows and p.vars_(row) & changed]
    need(cone == [[646,594],[648,596],[649,597],[651,599],[653,601],[654,602]]
         and affected == [603] and not changed & old, 'entire converse dependency cone')
    need([t for t in cert['bootstrap_norm']['row_combination'] if t['row'] not in gate_rows]
         == [{'multiplier': [[1,[]]], 'row': 603}], 'unit recovery of the sole affected constraint')
    fixed_roles = set(range(643)) | {643,644,655,656}
    fixed_roles |= {v[1] for s in raw['indices'] for v in s['pair']}
    fixed_roles |= {v[1] for call in raw['powers'] for v in (call['base'],call['exponent'],call['output'])}
    fixed_roles |= {call[key] for call in cert['power_calls'] for key in ('modulus','quotient')}
    need(not changed & fixed_roles, 'normalization leaves all claimed main/comparison/power roles fixed')
    # Unconditional polynomial identities used by the negative-A argument.
    a, n, x, y = [V(i) for i in range(4)]
    D = add(add(mul(C(2), mul(a,n)), mul(n,n)), C(1))
    delta = add(mul(a,a), C(-1))
    minus, plus = add(x, mul(add(a,n), y), -1), add(x, mul(add(a,n), y))
    norm = add(mul(x,x), mul(delta, mul(y,y)), -1)
    need(mul(minus,plus) == add(norm, mul(D,mul(y,y)), -1), 'negative-A norm product')
    nextx, nexty = add(mul(a,x),mul(delta,y)), add(x,mul(a,y))
    need(add(nextx,mul(add(a,n),nexty),-1)
         == add(mul(mul(C(-1),n),minus),mul(D,y),-1), 'negative-A residue recurrence')
    TminusA = add(add(mul(C(2),mul(a,n)),mul(n,n),-1),add(C(1),a),-1)
    identity = add(mul(add(mul(C(2),n),C(-1)),add(add(a,n,-1),C(-1))),
                   mul(add(n,C(-1)),add(n,C(2))))
    need(TminusA == identity, 'old T0 positivity identity')
    negative_controls = 0
    for W in range(2, 9):
        a0 = W**W + 1
        for n0 in range(1,W):
            D0 = 2*a0*n0+n0*n0+1
            for k in range(1,W):
                chi, psi = pell(a0,k)
                for m in range(W):
                    need(m+n0**k <= W**W and m*n0**k+1 <= W**W < D0,
                         'strict signed residue diagnostic bounds')
                    for sx in (-1,1):
                        valid = (sx*chi+(a0+n0)*psi-m) % D0 == 0
                        allowed = (sx == -1 and k%2 == 1 and m == n0**k)
                        allowed |= (sx == 1 and k%2 == 0 and n0 == m == 1)
                        need(valid == allowed, 'all four signed/parity branches including m0/base1')
                        negative_controls += 1
    bootstrap_controls = 0
    for W in range(2,8):
        for multiple in (1,2):
            a0, y0 = pell(W+1,W*multiple)
            need(y0%W == 0 and a0 > W**W, 'bootstrap height/divisibility diagnostics')
            for sz in (-1,1):
                Z = sz*(y0//W)
                need(abs(Z)-1 >= 0 and a0*a0-1 == W**3*(W+2)*abs(Z)**2,
                     'signed Z normalization diagnostics')
                bootstrap_controls += 1
    source_names = [PROOF, 'research/bootstrap-guard-exchange/MANIFEST.json',
        'research/bootstrap-guard-exchange/audit.py',
        'research/main-root-and-modulus-signs/CERTIFICATE.json',
        'candidates/projected-radius-mixed-bounds/source/raw_builder.json',
        'candidates/projected-radius-mixed/arithmetic_interfaces.json',
        'candidates/projected-radius-comparison-base/domain_certificate.json',
        'reviews/main-root-modulus-signs-peer.py',
        str(Path(__file__).relative_to(ROOT))]
    result = dict(status='PASS', optimized_python=bool(sys.flags.optimize),
        proof_sha256=EXPECTED_PROOF, source_pins={n:digest(ROOT/n) for n in source_names},
        exact_guard_count=78, old_guard=694, replacement_guard=645,
        prefix_values_before_private_signs=len(lower), exact_prefix_sign_steps=sign_steps,
        strict_constructor_steps=len(pp['steps']), collected_original_row_identities=combinations,
        full_source_gates=len(gate_rows), full_source_nongates=len(rows)-len(gate_rows),
        converse_changed_gates=cone, converse_affected_nongates=affected,
        critical_calls=critical, negative_A_branch_diagnostics=negative_controls,
        bootstrap_Z_normalization_diagnostics=bootstrap_controls,
        raw86_formula='(t+x+y+M0+2)^(2^23)', raw86_evenness_assumed=False,
        ordinary_review='PASS: both integer-zero existence maps, signed Pell indices, four-call sign contradiction, and complete source dependency boundary',
        scope='Independent ordinary review and exact finite source bindings; diagnostics are not the unbounded proof. No Lean, internal-ZFC proof, or projected-count improvement is claimed.')
    output = args.output or Path(__file__).with_suffix('.json')
    output.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
    print(json.dumps({k:result[k] for k in ('status','exact_guard_count','collected_original_row_identities','negative_A_branch_diagnostics')},indent=2))

if __name__ == '__main__':
    main()
