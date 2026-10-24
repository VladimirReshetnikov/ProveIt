#!/usr/bin/env python3
"""Independent paired-index source/dependency review; no optimizer/emitter.

The ordinary unbounded review is in paired-index-guards-peer.md. Author
normal/-O audits are replayed into scratch; their module is never imported.
"""
import argparse
from collections import Counter
from copy import deepcopy
from fractions import Fraction
from hashlib import sha256
import importlib.util
import json
from math import comb, factorial
from pathlib import Path
import subprocess
import sys
import tempfile
sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[1]
AUTHOR = ROOT/'research/paired-index-guards'
PINS = {
    'README.md':'7307c64d16a085fff48680ec7a4941b92237c0adc64408f70b7039bc7eb4303e',
    'LOCAL_FACTORIAL.md':'1fbb094d09d8d10e03c745a32f7863ca4a5d4a57765408549d47130a4623580d',
    'local_factorial_audit.py':'1932e42bfed4eef58110226dc45274836166b43270e6e835c2961df5f2077a0e',
    'LOCAL_FACTORIAL_CERTIFICATE.json':'2be4f7d49a5c473f71dae8227a791e415ee085d90d6db6f7b3bd31982d4de34a',
}

def need(ok, message):
    if not ok:
        raise ValueError(message)

def sha(path):
    return sha256(path.read_bytes()).hexdigest()

def load(path):
    return json.loads(path.read_bytes())

def boolean(poly, assignment=None):
    assignment = assignment or {}
    result = {}
    for monomial, coefficient in poly.items():
        if any(assignment.get(v) == 0 for v in monomial):
            continue
        monomial = tuple(sorted({v for v in monomial if assignment.get(v) != 1}))
        result[monomial] = (result.get(monomial,0)+coefficient)%2
    return {m:c for m,c in result.items() if c}

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path)
    args = parser.parse_args()
    for name,h in PINS.items():
        need(sha(AUTHOR/name) == h, 'the exact independently reviewed proof/source '+name)
    for record in load(AUTHOR/'MANIFEST.json')['files']:
        data = (AUTHOR/record['path']).read_bytes()
        need(len(data) == record['bytes'] and sha256(data).hexdigest() == record['sha256'],
             'each declared frozen packet member '+record['path'])
    certificate = load(AUTHOR/'LOCAL_FACTORIAL_CERTIFICATE.json')
    for name,h in certificate['source_pins'].items():
        need(sha(ROOT/name) == h, 'full inherited source binding '+name)
    helper = ROOT/'reviews/main-root-modulus-signs-peer.py'
    need(sha(helper) == '2779fc7531543a567270668a668511651979fa447ee72314f1c2d369fc49db21',
         'pinned independent polynomial primitives')
    spec = importlib.util.spec_from_file_location('paired_peer_sparse_definitions',helper)
    p = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(p)
    P,C,V,add,mul,product = p.P,p.C,p.V,p.plus,p.times,p.product
    raw = load(ROOT/'candidates/projected-radius-mixed-bounds/source/raw_builder.json')
    prior = load(ROOT/'research/main-root-and-modulus-signs/CERTIFICATE.json')
    old = load(ROOT/'candidates/projected-radius-comparison-base/domain_certificate.json')
    rows = [P(row['terms']) for row in raw['rows']]
    original = {g['raw_variable'] for g in old['guards']}
    removed = {674,861,1214}
    kept = original-removed
    need(certificate['removed_scalar_guards'] == sorted(removed)
         and certificate['retained_scalar_guards'] == sorted(kept)
         and len(kept) == 75 and {694,711,779} <= kept,
         'exact removed predicates and retained bootstrap/local-pair guard premises')
    need(certificate['new_predicates'] == [dict(kind='value_at_least',raw_variable=656,lower=1),
         dict(kind='nonnegative_product',raw_variables=[674,861])], 'strict carrier and actual product')
    prefix = prior['prefix_proof']
    known = {v:0 for v in prefix['initial_semantic_guard_indices']}
    need(len(known) == 61 and set(known) <= kept, 'every scalar-prefix premise is still guarded')
    combinations = 0
    def collect(cut, target=None, prefix_only=False):
        nonlocal combinations
        out = {}
        for term in cut['row_combination']:
            m, row = P(term['multiplier']), rows[term['row']]
            if prefix_only:
                need(p.vars_(m) | p.vars_(row) <= set(range(643)),
                     'no missing private slack or downstream power semantics in prefix')
            out = add(out,mul(m,row))
        if target is None:
            target = P(cut.get('polynomial',cut.get('expanded_polynomial')))
        need(out == target, 'complete coefficientwise original-row identity')
        combinations += 1
        return out
    def positive(poly):
        need(p.vars_(poly) <= set(known), 'lower bounds from earlier known coordinates only')
        shifted = {}
        for monomial,c in poly.items():
            shifted = add(shifted,product([C(c)]+[add(V(v),C(known[v])) for v in monomial]))
        need(all(c >= 0 for c in shifted.values()) and shifted.get((),0) > 0,
             'universal strict shifted polynomial bound')
    sign_steps = 0
    def sign(step):
        nonlocal sign_steps
        v,c,rhs = step['variable'],step['coefficient'],P(step['rhs'])
        pivot = add(mul(C(c),V(v)),rhs,-1)
        need(v < 643 and c > 0 and rows[step['row']] in (pivot,mul(C(-1),pivot))
             and p.vars_(rows[step['row']]) <= set(range(643)), 'exact early sign pivot')
        if step['kind'] == 'positive_monomials':
            odd = {v for m in rhs for v,n in Counter(m).items() if n%2}
            need(all(c > 0 for c in rhs.values()) and odd == set(step['dependencies'])
                 and odd <= set(known), 'earlier signs for every odd power')
        else:
            need(step['kind'] == 'affine_square'
                 and mul(P(step['square_root']),P(step['square_root'])) == rhs,
                 'domain-independent square inference')
        known[v] = max(known.get(v,0),0)
        sign_steps += 1
    def bound(step):
        v,L,f,g = step['variable'],step['lower'],P(step['factor']),P(step['rhs'])
        need(v not in p.vars_(f) | p.vars_(g), 'no circular target lower bound')
        collect(step,add(mul(V(v),f),g,-1),True)
        positive(f)
        positive(add(g,mul(C(L-1),f),-1))
        known[v] = max(known.get(v,L),L)
    for step in prefix['preliminary_t_n_bounds']:
        bound(step)
    for step in prefix['five_stages']:
        for item in step['preceding_sign_steps']:
            sign(item)
        bound(step)
    for step in prefix['final_sign_steps']:
        sign(step)
    need(set(known) == set(range(643)) and known[4] >= 1 and known[5] >= 2,
         'all643 prefix signs with only retained guards')
    # Also replay all positive exponent constructors. This explicitly licenses
    # V>=1 in the reverse map from an old zero, without any power meanings.
    pp = prior['positive_prefix']
    collect(pp['canonical_modulus_cut'],prefix_only=True)
    positive(add(P(pp['canonical_modulus_cut']['polynomial']),V(129)))
    strict = {4,5,129}
    for step in pp['steps']:
        v, row = step['variable'],rows[step['row']]
        need(row.get((v,)) == 1 and all(v not in m or m == (v,) for m in row),
             'exact positive constructor definition')
        rhs = {m:-c for m,c in row.items() if m != (v,)}
        m = tuple(step['positive_monomial'])
        need(all(c > 0 for c in rhs.values()) and p.vars_(rhs) <= set(known)
             and rhs.get(m,0) > 0 and set(m) <= strict, 'earlier positive monomial')
        strict.add(v)
    need(strict == set(pp['known_after']) and {s['exponent'][1] for s in raw['seeds']} <= strict,
         'all15 actual seed indices positive, including the converse')
    need(len(prior['seeds']) == len(raw['seeds']) == 15, 'all15 old converse seed roles')
    for seed,actual in zip(prior['seeds'],raw['seeds']):
        aliases = seed['aliases']
        need((aliases['X'],aliases['Y'],aliases['k'])
             == (actual['pair'][0][1],actual['pair'][1][1],actual['exponent'][1])
             and aliases['YminusK'] in original, 'each old ordinate/index/guard binds its actual seed')
        collect(seed['cuts']['index_at_most_Y'],P([[1,[aliases['Y']]],
            [-1,[aliases['k']]],[-1,[aliases['YminusK']]]]))
    expected = {
        'radius':[[1,[89]],[-1,[87,86,86]]],
        'shift':[[1,[90]],[-1,[86]],[-1,[89]]],
        'pow1_base':[[1,[92]],[-1,[89]],[-1,[]]],
        'radix':[[1,[530]],[-1,[129]],[-1,[129,93]],[-1,[129,113]]],
        'radix_plus_one':[[1,[531]],[-1,[530]],[-1,[]]],
        'digit':[[1,[532]],[-1,[533,91]],[-1,[533,530,534]],[-1,[535]]],
        'remainder_bound':[[1,[533]],[-1,[535]],[-1,[536]],[-1,[]]],
        'digit_bound':[[1,[530]],[-1,[91]],[-1,[537]],[-1,[]]],
        'factorial_ceiling':[[1,[87,91]],[-1,[93]],[-1,[95]]],
        'factorial_remainder_bound':[[1,[91]],[-1,[94]],[-1,[95]],[-1,[]]],
        'odd_base103':[[1,[103]],[-1,[]],[-1,[5,87]]],
        'opposite_index_parity':[[1,[122]],[-1,[4]],[-1,[104]],[-2,[]]],
        'K_input':[[1,[63]],[-1,[4]],[-1,[1]],[-1,[2]],[-1,[3]],[-2,[]]],
    }
    need(set(certificate['cuts']) == set(expected), 'all required exact local cuts, none omitted')
    for name,target in expected.items():
        collect(certificate['cuts'][name],P(target))
    collect(certificate['M_constructor'],P([[1,[]],[1,[87]],[1,[87,59]],[-1,[129]]]))
    ordinates = [s['pair'][1][1] for s in raw['seeds']]
    collect(certificate['whole_V_product'],add(V(656),product([add(V(1214),C(1))]
        +[mul(V(y),V(y)) for y in ordinates]),-1))
    need({94,95,113,59,534,535,536,537} <= kept, 'actual factorial/digit/radix signs retained')
    gates = {row['gate']:P(row['terms']) for row in raw['rows'] if row.get('gate') is not None}
    need(certificate['K_square_chain'] == list(range(64,87)), 'correct23-square constructor')
    for v in range(64,87):
        need(gates[v] == add(V(v),mul(V(v-1),V(v-1)),-1), 'each exact K squaring row')
    wanted_calls = [(1,92,86,93,707,708),(5,531,90,532,775,776),(6,530,86,533,707,708)]
    need(certificate['local_interpreted_calls'] == [1,5,6]
         and certificate['kept_local_seed_slacks'] == [711,779]
         and certificate['parity_only_call'] == 2
         and certificate['conditional_even_orientation_calls'] == [0,9], 'explicit acyclic power-use boundary')
    for stored, (i,n,k,m,x,y) in zip(certificate['actual_calls'],wanted_calls):
        call = prior['power_calls'][i]
        need(stored == call and [raw['powers'][i][key] for key in ('base','exponent','output')]
             == [['v',v] for v in (n,k,m)] and (call['X'],call['Y']) == (x,y),
             'complete local call and retained seed binding')
        collect(call['cut'],P([[1,[x]],[-1,[644,y]],[1,[n,y]],[-1,[m]],
                              [-1,[call['modulus'],call['quotient']]]]))
        collect(next(item['cut'] for item in prior['moduli'] if item['base'] == n))
    for i in (1,2):
        seed = prior['seeds'][i]
        need(seed['aliases']['YminusK'] in kept, 'local index theorem uses a retained short interval')
        for cut in seed['cuts'].values():
            collect(cut)
    for call,seed,ci,si,slack in zip(certificate['conditional_calls'],certificate['missing_seeds'],
                                    (0,9),(0,4),(674,861)):
        need(call == prior['power_calls'][ci] and seed == prior['seeds'][si]
             and seed['aliases']['YminusK'] == slack
             and [call['X'],call['Y']] == [seed['aliases']['X'],seed['aliases']['Y']],
             'later even-index orientation refers to its actual missing slack')
        for cut in seed['cuts'].values():
            collect(cut)
        collect(call['cut'])
        collect(next(item['cut'] for item in prior['moduli'] if item['base'] == call['base']))
    for name in ('frame_cut','bootstrap_norm','unit_norm_cut',
                 'comparison_base_constructor','comparison_base_congruence'):
        collect(prior[name])
    need(certificate['parity_call'] == prior['power_calls'][2], 'parity-only exact call2')
    call = collect(certificate['parity_call']['cut'])
    norm = collect(certificate['main_t_norm'],P([[1,[670,670]],[-1,[644,644,671,671]],
                                              [1,[671,671]],[-1,[]]]))
    need(boolean(add(call,norm),{103:1,742:0}) == {():1,(104,):1},
         'odd output follows from norm and even modulus, not a t-power theorem')
    need(boolean(P(expected['odd_base103']),{87:0}) == {():1,(103,):1}, 'even factorial implies odd base')
    modulus = next(item for item in prior['moduli'] if item['base'] == 103)
    need(boolean(P(modulus['cut']['polynomial']),{103:1}) == {(742,):1}, 'actual even call2 modulus')
    need(boolean(P(expected['opposite_index_parity']),{104:1}) == {():1,(4,):1,(122,):1},
         'actual t and k122 have opposite parity')
    collect(certificate['t_slack'],P([[1,[671]],[-1,[4]],[-1,[674]]]))
    collect(certificate['k122_slack'],P([[1,[858]],[-1,[122]],[-1,[861]]]))
    # Exact supplemental checks of the strict factorial product, including
    # f=1 and the boundary K=2. These do not replace the reviewed inequality.
    product_controls = 0
    for K in range(2,9):
        m = factorial(K)
        for f in sorted({1,max(1,m//2),m-1,m,m+1}):
            d = f*K*K
            ratio = Fraction((d+1)**K,comb(K+d,K))
            fraction_product = Fraction(m)
            for j in range(1,K+1):
                fraction_product *= Fraction(d+1,d+j)
            need(ratio == fraction_product and Fraction(m*(2*f-1),2*f) < ratio <= m,
                 'exact strict rational-product boundary')
            need(((ratio.numerator+ratio.denominator-1)//ratio.denominator == f) == (f == m),
                 'ceiling fixed-point diagnostic')
            product_controls += 1
    need(Fraction(25,15) > 1, 'K2/f1 strict boundary')
    author_replays = {}
    with tempfile.TemporaryDirectory(prefix='paired-index-independent-peer-') as tmp:
        for optimized in (False,True):
            output = Path(tmp)/('optimized.json' if optimized else 'normal.json')
            command = [sys.executable,'-B']+(['-O'] if optimized else [])
            command += [str(AUTHOR/'local_factorial_audit.py'),'--output',str(output)]
            proc = subprocess.run(command,capture_output=True,text=True)
            need(proc.returncode == 0, 'author scratch replay: '+proc.stderr)
            report = load(output)
            need(report['status'] == 'PASS' and report['optimized_python'] == optimized,
                 'explicit author replay mode and PASS')
            author_replays['optimized' if optimized else 'normal'] = report
    a,b = deepcopy(author_replays['normal']),deepcopy(author_replays['optimized'])
    a.pop('optimized_python');b.pop('optimized_python')
    need(a == b, 'normal and optimized author receipts match except interpreter mode')
    names = [str((AUTHOR/name).relative_to(ROOT)) for name in PINS]
    names += ['research/paired-index-guards/MANIFEST.json','reviews/main-root-modulus-signs-peer.py',
              str(Path(__file__).relative_to(ROOT))]+list(certificate['source_pins'])
    result = dict(status='PASS',optimized_python=bool(sys.flags.optimize),
        source_pins={name:sha(ROOT/name) for name in sorted(set(names))},
        accepted_claims=['local factorial0 equals K! using only calls1/5/6',
            'strict V guard pointwise recovers raw1214 and all nonzero ordinates',
            'call2 parity only gives opposite parity of t/k122 before their power meanings',
            'one even index recovers a strictly positive actual slack',
            'product guard recovers the other slack, hence both original guards',
            'both integer-zero existence maps at the unchanged source body'],
        projected_metrics_or_new_equation_claimed=False,
        independent_exact_prefix_sign_steps=sign_steps,independent_positive_constructor_steps=len(pp['steps']),
        independent_collected_original_row_identities=combinations,
        complete_prefix_coordinates=len(known),local_power_calls=[1,5,6],
        parity_only_call=2,conditional_even_orientation_calls=[0,9],
        boolean_parity_identities=4,strict_product_diagnostics=product_controls,
        author_normal_and_optimized_replays=author_replays,
        author_packet_modified=False,optimizer_or_emitter_imported=False,
        scope='Ordinary unbounded review plus exact source/dependency checks. No full21-power assumption, projected metric, native recalibration, Lean or internal-ZFC theorem.')
    output = args.output or Path(__file__).with_suffix('.json')
    output.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
    print(json.dumps({key:result[key] for key in ('status','independent_exact_prefix_sign_steps',
        'independent_positive_constructor_steps','independent_collected_original_row_identities',
        'projected_metrics_or_new_equation_claimed')},indent=2))

if __name__ == '__main__':
    main()
