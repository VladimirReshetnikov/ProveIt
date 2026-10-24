#!/usr/bin/env python3
"""Independent source and dependency review of the ordinary74-predicate proof.

The sparse integer polynomial implementation is local to this file. No author
module, optimizer, source builder, historical emitter or Lean tool is imported.
Author checker subprocesses run in scratch in both interpreter modes only.
The unbounded mathematical review is in encoded-index-sign-peer.md.
"""
import argparse
from collections import Counter
from copy import deepcopy
from fractions import Fraction
from hashlib import sha256
import json
from math import comb, factorial, prod
from pathlib import Path
import subprocess
import sys
import tempfile

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[1]
AUTHOR = ROOT / 'research/encoded-index-sign'
# Populated with fixed SHA256 values when this independent review was written.
PINS = {
    "candidates/projected-radius-comparison-base/domain_certificate.json": "dc59fc01c077806a8e74f4f6dc455631ee0901843aa4d711aa2a3af9e79f13d5",
    "candidates/projected-radius-mixed-bounds/source/raw_builder.json": "2dc3a2acaeb95d09b22501ee4e978327c03c2cd50a1a0817eadda257651a0a75",
    "research/comparison-base-sign/README.md": "c60a20bb5bf7e41f90fbe51df4953bbbe01106225fa1d0b301fd9ea874ba367c",
    "research/encoded-index-sign/CERTIFICATE.json": "4eb33b0f5b155105750aa55a1ef3e5a0b5b7eaee19ba314531ac15b4b5016573",
    "research/encoded-index-sign/MANIFEST.json": "fade0833980dde2b0e390340046c172b329cb1c21b7469982b3db657e463ed10",
    "research/encoded-index-sign/PROOF.md": "87116c016a93fcb17b7bd0d6505172dfe94960b34b391ae18a1b2c9b2d41d572",
    "research/encoded-index-sign/README.md": "89f5f37495cf637270aed63b6aaf548544cce2118d8a607834383020df777bbd",
    "research/encoded-index-sign/SOURCE_PINS.json": "399614ee8445285dd4b1032b77a5e28f60ff2ae62063baa209261ef698578ddb",
    "research/encoded-index-sign/VERIFICATION.json": "0d5d50edfa40eb0a011ef5efd2c027ef29ed5ed890b4b90230438afe45ead1a8",
    "research/encoded-index-sign/VERIFICATION_OPTIMIZED.json": "d64e50de89b126da1074640bd09c22ba733c13d2a4de5e55474197bf1e126392",
    "research/encoded-index-sign/check.py": "de81ba244f19fe3a0d6c9128a54f8f969ae35102c5e64aad80309452a431ba2a",
    "research/factorial-radius-guard/MANIFEST.json": "0ea24533f7459155070dee3e18b67d4b8ae68500a85481778f6151cd6213557a",
    "research/factorial-radius-guard/PROOF.md": "5d9b65a4841151e200be6537373c403deea76b3943698097992176ee4c233e37",
    "research/factorial-radius-guard/README.md": "67eafdc8a8c7b95f089ddcad086548d954d448c7325a505b206b9eb000535b31",
    "research/factorial-radius-guard/SOURCE_PINS.json": "b1df3de2d214af35729f3c044c3aa0b7eedc56fbd67ecd3d7f8f991a2784d82f",
    "research/factorial-radius-guard/VERIFICATION.json": "9316922a282475b96c46e58f034bd436f36fd412cfd489ff92a451350a46f944",
    "research/factorial-radius-guard/VERIFICATION_OPTIMIZED.json": "1f00677f674e8a404bccf543a94320c7168610c70eeb8715444695f5e653772d",
    "research/factorial-radius-guard/check.py": "96e08e4224081064778c35d770457df1d2521482f8a947586542fa872e20ca28",
    "research/factorial-radius-output-sign/CERTIFICATE.json": "d3cb63c408ae29c47eb848a29809319f660b0a54574a5693c81edef6810f06cf",
    "research/factorial-radius-output-sign/MANIFEST.json": "bb0d2107df65dbce6cbbd8d441028083202e10c4cc8df4d70e40192a7fedd592",
    "research/factorial-radius-output-sign/PROOF.md": "9179ecaa5da1eee21bcae20ceeceb15eaa42b1d0cabf715548054cf323f4558a",
    "research/factorial-radius-output-sign/README.md": "f8377c63a21a26997f1634bbcc14fbf4a5d80e8f756ba6a7efadb42ea5f55abc",
    "research/factorial-radius-output-sign/SOURCE_PINS.json": "1410c5e1708e9bad88b9ef03803b403c1d6eaef99a6d195cfbb9a4c638c2c028",
    "research/factorial-radius-output-sign/VERIFICATION.json": "0d92d190a26d3405a89aa75821004a5924c26cf53653dfe7b2a2ee6c0db44bfc",
    "research/factorial-radius-output-sign/VERIFICATION_OPTIMIZED.json": "488c2a8bb66cbe8cda64ab821face947c6a18cf90828b959238c33f54bbe3de9",
    "research/factorial-radius-output-sign/check.py": "4ba358a3654fe57150b1abd1a6ad19b5db88af9ac3e32c08269c71eeba6517f7",
    "research/main-root-and-modulus-signs/CERTIFICATE.json": "96097a2984ab34468413c32898af70ee01c96d35470aaacc773654aca1140970",
    "research/main-root-and-modulus-signs/README.md": "fb7cc8744422d59ad3552b06370cfeea6fbd5e9c869ffe2d6dba97c1f41be446",
    "research/main-root-and-modulus-signs/SIGNED_INDEX_THEOREM_SOURCE.md": "55c6a0588a86d5a600da42bc77b12ce61faa4d7e383435cb46c35868d10f2f8a",
    "research/paired-index-guards/LOCAL_FACTORIAL.md": "1fbb094d09d8d10e03c745a32f7863ca4a5d4a57765408549d47130a4623580d",
    "research/paired-index-guards/LOCAL_FACTORIAL_CERTIFICATE.json": "2be4f7d49a5c473f71dae8227a791e415ee085d90d6db6f7b3bd31982d4de34a",
    "research/paired-index-guards/MANIFEST.json": "e4d5d0fa887c888f91539d8f912440405f8402c18ddca10773178b34805f4a18",
    "research/paired-index-guards/README.md": "7307c64d16a085fff48680ec7a4941b92237c0adc64408f70b7039bc7eb4303e",
    "reviews/factorial-radius-guard-peer.json": "1a46af23a3920e31f8cf2f3c5d33e8903cef0c3c917ad9bcc2dadbbf290de4a7",
    "reviews/factorial-radius-guard-peer.md": "670b7e4c6befcaa0ea6aea57e56c5e758d09c0bb2c37bcb3b1257eeb30355b8c",
    "reviews/factorial-radius-guard-peer.py": "5dea2fdb113df5425b3c79f63240e2e1a0c5d21e18bc8008011cb56a0a550af7",
    "reviews/factorial-radius-guard-peer_OPTIMIZED.json": "c3bb0e4f33e867ea5da6363e4cb79b6f27f047eb879378b3260968a56a9c6129",
    "reviews/main-root-modulus-signs-peer.py": "2779fc7531543a567270668a668511651979fa447ee72314f1c2d369fc49db21"
}


def need(condition, message):
    if not condition:
        raise ValueError(message)


def sha(path):
    return sha256(path.read_bytes()).hexdigest()


def load(path):
    return json.loads(path.read_bytes())


def poly(terms):
    result = {}
    for coefficient, monomial in terms:
        need(type(coefficient) is int and all(type(v) is int for v in monomial),
             'literal integer coefficients and coordinate indices')
        key = tuple(sorted(monomial))
        result[key] = result.get(key, 0) + coefficient
    return {m: c for m, c in result.items() if c}


def const(value):
    return {(): value} if value else {}


def var(index):
    return {(index,): 1}


def add(*summands):
    return poly([(c, m) for q in summands for m, c in q.items()])


def scale(q, coefficient):
    return {m: c * coefficient for m, c in q.items() if c * coefficient}


def mul(*factors):
    out = const(1)
    for q in factors:
        out = poly([(a * b, m + n) for m, a in out.items() for n, b in q.items()])
    return out


def variables(q):
    return {v for m in q for v in m}


def shifted(q, lower):
    out = {}
    for m, c in q.items():
        out = add(out, mul(const(c), *[add(var(v), const(lower[v])) for v in m]))
    return out


def boolean(q, assignments=None):
    assignments = assignments or {}
    out = {}
    for m, c in q.items():
        if any(assignments.get(v) == 0 for v in m):
            continue
        key = tuple(sorted({v for v in m if assignments.get(v) != 1}))
        out[key] = (out.get(key, 0) + c) % 2
    return {m: c for m, c in out.items() if c}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    need(bool(PINS), 'review has fixed complete source pins')
    for name, expected in PINS.items():
        need(sha(ROOT / name) == expected, 'complete independently pinned file ' + name)
    manifest = load(AUTHOR / 'MANIFEST.json')['files']
    need({str(p.relative_to(AUTHOR)) for p in AUTHOR.rglob('*')
          if p.is_file() and p.name != 'MANIFEST.json'} == set(manifest),
         'closed author inventory')
    for name, expected in manifest.items():
        need(sha(AUTHOR / name) == expected, 'sealed author member ' + name)
    pins = load(AUTHOR / 'SOURCE_PINS.json')
    need(set(pins['files']) <= set(PINS), 'all source dependencies independently pinned')
    for name, expected in pins['files'].items():
        need(PINS[name] == expected, 'source pin agrees with independently fixed hash ' + name)

    data = load(AUTHOR / 'CERTIFICATE.json')
    raw = load(ROOT / 'candidates/projected-radius-mixed-bounds/source/raw_builder.json')
    old = load(ROOT / 'candidates/projected-radius-comparison-base/domain_certificate.json')
    prior = load(ROOT / 'research/main-root-and-modulus-signs/CERTIFICATE.json')
    local = load(ROOT / 'research/paired-index-guards/LOCAL_FACTORIAL_CERTIFICATE.json')
    rows = [poly(row['terms']) for row in raw['rows']]
    original = {g['raw_variable'] for g in old['guards']}
    omitted = {59, 93, 674, 711, 779, 861, 1214}
    kept = original - omitted
    replacements = [dict(kind='at_least', lower=1, raw_variable=656),
                    dict(kind='nonnegative_product', raw_variables=[674, 861]),
                    dict(kind='at_least', lower=2, raw_variable=87)]
    need(len(rows) == 1177 and len(original) == 78 and len(kept) == 71,
         'unchanged1177 source rows and exact71 retained original scalar predicates')
    need(data['omitted_original_predicates'] == pins['removed_original_predicates'] == sorted(omitted)
         and data['inherited_replacement_predicates'] == pins['new_predicates'] == replacements,
         'literal74-predicate domain')
    need({94, 95, 113, 537, 694, 825} <= kept,
         'early signs, original bootstrap, retained shifted-t bound')
    need([i for i, row in enumerate(rows) if 59 in variables(row)]
         == data['source_occurrences_of_59'] == [114], 'ALL source uses of raw59')
    count = 0

    def collect(cut, target=None, prefix_only=False):
        nonlocal count
        result = {}
        for term in cut['row_combination']:
            index = term['row']
            need(type(index) is int and 0 <= index < len(rows), 'actual original row index')
            multiplier = poly(term['multiplier'])
            if prefix_only:
                need(variables(multiplier) | variables(rows[index]) <= set(range(643)),
                     'prefix uses no private guard or downstream power premise')
            result = add(result, mul(multiplier, rows[index]))
        expected = target if target is not None else poly(cut.get('polynomial', cut.get('expanded_polynomial')))
        need(result == expected, 'every coefficient of complete original-row combination')
        if 'polynomial' in cut or 'expanded_polynomial' in cut:
            need(poly(cut.get('polynomial',cut.get('expanded_polynomial'))) == expected,
                 'declared certificate polynomial agrees with independently selected target')
        count += 1
        return result

    targets = {
        'E_definition': [[1,[137]],[-1,[59]],[-1,[]]],
        'M_from_E': [[1,[]],[1,[87,137]],[-1,[129]]],
        'N_early': [[1,[93]],[-1,[87,94]],[-1,[87,95]],[1,[95]],[-1,[87]]],
        'local0_factorial_remainder_bound': [[1,[91]],[-1,[94]],[-1,[95]],[-1,[]]],
        'local0_digit_bound': [[1,[530]],[-1,[91]],[-1,[537]],[-1,[]]],
        'local0_radix': [[1,[530]],[-1,[129]],[-1,[129,93]],[-1,[129,113]]],
        'local0_K_input': [[1,[63]],[-1,[4]],[-1,[1]],[-1,[2]],[-1,[3]],[-2,[]]],
        'local0_radius': [[1,[89]],[-1,[87,86,86]]],
        'local0_shift': [[1,[90]],[-1,[86]],[-1,[89]]],
        'local0_pow1_base': [[1,[92]],[-1,[89]],[-1,[]]],
        'local0_factorial_ceiling': [[1,[87,91]],[-1,[93]],[-1,[95]]],
        'local0_odd_base103': [[1,[103]],[-1,[]],[-1,[5,87]]],
        'local0_opposite_index_parity': [[1,[122]],[-1,[4]],[-1,[104]],[-2,[]]],
        'd1_radius': [[1,[109]],[-1,[107,4,4]]],
        't_shift': [[1,[110]],[-1,[4]],[-1,[109]]],
        't_base': [[1,[112]],[-1,[]],[-1,[109]]],
        'factorial1_remainder': [[1,[111]],[-1,[114]],[-1,[115]],[-1,[]]],
        'factorial1_ceiling': [[1,[107,111]],[-1,[113]],[-1,[115]]],
        'choose1_digit': [[1,[546]],[-1,[547,111]],[-1,[547,530,548]],[-1,[549]]],
        'choose1_remainder': [[1,[547]],[-1,[549]],[-1,[550]],[-1,[]]],
        'choose1_digit_bound': [[1,[530]],[-1,[111]],[-1,[551]],[-1,[]]],
        'choose2_digit': [[1,[560]],[-1,[547,123]],[-1,[547,530,561]],[-1,[562]]],
        'choose2_remainder': [[1,[547]],[-1,[562]],[-1,[563]],[-1,[]]],
        'choose2_digit_bound': [[1,[530]],[-1,[123]],[-1,[564]],[-1,[]]],
        'B_plus_two': [[1,[105]],[-1,[104]],[-2,[]]],
        'product_modulus': [[1,[126]],[1,[]],[-1,[87,104]],[-2,[87]]],
        'product_division': [[1,[106,107,123]],[-1,[129]],[-1,[126,130]]],
        'product_remainder': [[1,[126]],[-1,[129]],[-1,[131]],[-1,[]]],
    }
    ys = [seed['pair'][1][1] for seed in raw['seeds']]
    targets['V_product'] = [(c,m) for m,c in add(var(656), scale(mul(
        add(var(1214),const(1)), *[mul(var(y),var(y)) for y in ys]),-1)).items()]
    need(set(targets) == set(data['exact_source_cuts']), 'every new arithmetic interface')
    for name, target in targets.items():
        collect(data['exact_source_cuts'][name], poly(target))
    for name, target in {
        'radix_plus_one': [[1,[531]],[-1,[530]],[-1,[]]],
        'digit': [[1,[532]],[-1,[533,91]],[-1,[533,530,534]],[-1,[535]]],
        'remainder_bound': [[1,[533]],[-1,[535]],[-1,[536]],[-1,[]]],
    }.items():
        collect(local['cuts'][name], poly(target))
    # A free-polynomial lower-bound identity: F=f-2, r,s>=0 imply N>=2.
    F,r,s = [var(i) for i in range(3)]
    early = add(mul(add(F,const(2)),r), mul(add(F,const(1)),s), F)
    need(early == add(mul(F,add(r,s,const(1))),scale(r,2),s),
         'unbounded early N-2 positive coefficient identity')
    need(all(c > 0 for c in early.values()), 'no semantic premise in the early output bound')

    prefix = prior['prefix_proof']
    initial = set(prefix['initial_semantic_guard_indices'])
    need(len(initial) == 61 and initial - kept == {59,93}, 'exact missing initial prefix signs')
    need(data['early_derived_bounds'] == {'87':2,'93':2,'129':1,'137':0},
         'only weak M>=1 and E>=0 seeded before prefix')
    known = {v:0 for v in initial - {59,93}}
    known.update({87:2,93:2,129:1,137:0})
    canonical = prior['positive_prefix']['canonical_modulus_cut']
    canonical_poly = collect(canonical,poly([[1,[]],[1,[87]],[1,[87,59]],[-1,[129]]]),True)
    rewrites = {entry['variable']:entry for entry in data['rewritten_prefix_bounds']}
    need(set(rewrites) == {130,517}, 'exact two rewritten lower bounds')
    signs = skipped = 0

    def positive(q):
        need(variables(q) <= set(known), 'all lower-bound dependencies already available')
        out = shifted(q,known)
        need(all(c >= 0 for c in out.values()) and out.get((),0) > 0,
             'unbounded positive polynomial after shifting by proved lower bounds')

    def bound(step):
        v,L = step['variable'],step['lower']
        f,g = poly(step['factor']),poly(step['rhs'])
        original_target = collect(step,add(mul(var(v),f),scale(g,-1)),True)
        if v in rewrites:
            replacement = rewrites[v]
            f,g = poly(replacement['factor']),poly(replacement['rhs'])
            if v == 130:
                need(f == add(var(129),const(1),var(131)) and g == add(
                    mul(var(106),var(107),var(123)),scale(var(129),-1)), 'exact130 weakM rewrite')
                coefficient = scale(add(var(130),const(1)),-1)
            else:
                need(f == var(129) and g == var(516), 'exact517 weakM rewrite')
                coefficient = scale(var(517),-1)
            target = add(mul(var(v),f),scale(g,-1))
            need(replacement['lower'] == L and add(original_target,mul(coefficient,canonical_poly))
                 == target, 'complete canonicalM polynomial rewrite')
            collect(replacement,target,True)
        need(v not in variables(f) | variables(g), 'no lower-bound target used as premise')
        positive(f)
        positive(add(g,scale(f,1-L)))
        known[v] = max(known.get(v,L),L)

    def sign(step):
        nonlocal signs, skipped
        v,c,rhs = step['variable'],step['coefficient'],poly(step['rhs'])
        if v == 137:
            need(step['row'] == 114 and data['skip_prefix_sign'] == dict(variable=137,row=114)
                 and known[137] == 0, 'replace only E sign inference by early direct proof')
            skipped += 1
            return
        pivot = add(scale(var(v),c),scale(rhs,-1))
        need(c > 0 and v < 643 and 59 not in variables(rows[step['row']])
             and rows[step['row']] in (pivot,scale(pivot,-1)), 'entire literal ordered source sign row')
        if step['kind'] == 'positive_monomials':
            dependencies = {v for m in rhs for v,n in Counter(m).items() if n % 2}
            need(dependencies == set(step['dependencies']) and dependencies <= set(known)
                 and all(c > 0 for c in rhs.values()), 'every earlier odd-power sign')
        else:
            need(step['kind'] == 'affine_square' and mul(poly(step['square_root']),poly(
                step['square_root'])) == rhs, 'integer-square inference without sign premise')
        known[v] = max(known.get(v,0),0)
        signs += 1

    for step in prefix['preliminary_t_n_bounds']:
        bound(step)
    for step in prefix['five_stages']:
        for entry in step['preceding_sign_steps']:
            sign(entry)
        bound(step)
    for step in prefix['final_sign_steps']:
        sign(step)
    need(set(known) == set(range(643)) - {59} and signs == 574 and skipped == 1,
         'complete modified642-coordinate ordered prefix')
    need(data['expected_prefix'] == dict(excluded_coordinate=59,nonnegative_count=642,
         sign_steps=574,strict_steps=430) and data['raw_coordinate_omitted'] == 59
         and data['successor_coordinate'] == 137, 'entire advertised prefix and encoded coordinate census')
    strict = {4,5,87,93,129}
    constructors = 0
    for step in prior['positive_prefix']['steps']:
        v = step['variable']
        if v == 137:
            need(data['skip_strict_constructor'] == 137, 'no early E>0 assumption')
            continue
        row = rows[step['row']]
        need(row.get((v,)) == 1 and all(v not in m or m == (v,) for m in row),
             'literal unit constructor row')
        rhs = {m:-c for m,c in row.items() if m != (v,)}
        monomial = tuple(step['positive_monomial'])
        need(all(c > 0 for c in rhs.values()) and variables(rhs) <= set(known)
             and rhs.get(monomial,0) > 0 and set(monomial) <= strict,
             'strict constructor uses earlier positive monomial and available nonnegative terms')
        strict.add(v)
        constructors += 1
    arguments = {call[key][1] for call in raw['powers'] for key in ('base','exponent','output')}
    need(len(arguments) == 43 and 59 not in arguments and arguments <= set(known)
         and sorted(arguments) == data['frame_arguments'] == prior['frame_arguments'],
         'actual43-argument frame; raw59 is not an argument or output')
    need(constructors == 430 and all(call['base'][1] in strict and call['exponent'][1] in strict
         for call in raw['powers']) and all(seed['exponent'][1] in strict for seed in raw['seeds']),
         'all actual bases, powers and15 seed indices positive without E>0')
    collect(data['frame_cut'],poly([[1,[643]],[-2,[]]]+[[-1,[v]] for v in sorted(arguments)]))
    gates = {row['gate']:poly(row['terms']) for row in raw['rows'] if row.get('gate') is not None}
    need(data['K_square_chain'] == list(range(64,87)), 'actual23-square K chain')
    for v in range(64,87):
        need(gates[v] == add(var(v),scale(mul(var(v-1),var(v-1)),-1)), 'literal K square')
    # Early carrier bound and common signed-index interfaces are recollected,
    # rather than importing a later natural/power theorem at a weakened domain.
    common_targets = {
        'bootstrap_norm': [[1,[644,644]],[-1,[]],[-1,[643,643,643,643,646,646]],
                           [-2,[643,643,643,646,646]]],
        'unit_norm_cut': [[1,[655,655]],[-1,[644,644,656,656]],[1,[656,656]],[-1,[]]],
        'comparison_base_constructor': [[1,[667]],[-1,[]],[-4,[656]],[-4,[656,657]]],
        'comparison_base_congruence': [[1,[667]],[-1,[644]],[-1,[655,658]]],
    }
    for name,target in common_targets.items():
        collect(prior[name],poly(target))
    collect(prior['initial_A_D_bounds'][0],poly([[2,[644,5]],[-1,[694]],[-1,[5,5]],[-1,[]]]))
    need(data['actual_calls'] == prior['power_calls'][:10] and data['seeds'] == prior['seeds'][:5],
         'exact first-ten powers and first-five seeds')
    for i,call in enumerate(data['actual_calls']):
        need([raw['powers'][i][key] for key in ('base','exponent','output')]
             == [['v',call[key]] for key in ('base','exponent','output')], 'actual call arguments')
        collect(call['cut'],poly([[1,[call['X']]],[-1,[644,call['Y']]],[1,[call['base'],call['Y']]],
            [-1,[call['output']]],[-1,[call['modulus'],call['quotient']]]]))
        modulus = next(item for item in prior['moduli'] if item['base'] == call['base'])
        collect(modulus['cut'],poly([[2,[644,call['base']]],[-1,[call['base'],call['base']]],
            [-1,[]],[-1,[call['modulus']]]]))
    for seed,actual in zip(data['seeds'],raw['seeds']):
        a = seed['aliases']
        need([['v',a['X']],['v',a['Y']]] == actual['pair'] and ['v',a['k']] == actual['exponent'],
             'each literal main pair matches its index')
        seed_targets = {
            'index_at_most_Y': [[1,[a['Y']]],[-1,[a['k']]],[-1,[a['YminusK']]]],
            'norm1': [[1,[a['X'],a['X']]],[-1,[644,644,a['Y'],a['Y']]],
                      [1,[a['Y'],a['Y']]],[-1,[]]],
            'norm3': [[1,[a['S'],a['S']]],[-1,[667,667,a['R'],a['R']]],
                      [1,[a['R'],a['R']]],[-1,[]]],
            'S_mod_U': [[1,[a['S']]],[-1,[a['X']]],[-1,[655,a['Squotient']]]],
            'R_mod_4Y': [[1,[a['R']]],[-1,[a['k']]],[-4,[a['Y'],a['Rquotient']]]],
        }
        need(set(seed_targets) == set(seed['cuts']), 'all five precise signed-index interfaces')
        for name,target in seed_targets.items():
            collect(seed['cuts'][name],poly(target))
    need(data['seeds'][3]['aliases']['YminusK'] == 825 and 825 in kept and
         {data['seeds'][i]['aliases']['YminusK'] for i in (0,1,2,4)} == {674,711,779,861},
         'exact retained and locally recovered index slacks')
    norm = collect(data['parity_t_norm'],poly([[1,[670,670]],[-1,[644,644,671,671]],
                                           [1,[671,671]],[-1,[]]]))
    need(boolean(add(poly(data['actual_calls'][2]['cut']['polynomial']),norm),{103:1,742:0})
         == {():1,(104,):1}, 'call2 parity follows from norm and even modulus before power semantics')
    need(boolean(poly(targets['local0_odd_base103']),{87:0}) == {():1,(103,):1},
         'even f implies odd actual base103')
    need(boolean(poly(next(item['cut']['polynomial'] for item in prior['moduli']
         if item['base'] == 103)),{103:1}) == {(742,):1}, 'actual modulus742 is even')
    need(boolean(poly(targets['local0_opposite_index_parity']),{104:1})
         == {():1,(4,):1,(122,):1}, 'opposite actual t/k122 parity')

    # Independent unbounded polynomial certificates behind the weak-radix
    # carry branch: with b>=d+2 and d=fK², shift-b<=K-2 and
    # N-f*(K-2)=f*(K²-K+2)+1>0 for f>=2,K>=3.
    f,K = var(0),var(1)
    gap = add(mul(f,add(mul(K,K),scale(K,-1),const(2))),const(1))
    need(gap == add(mul(f,mul(K,K)),const(1),scale(mul(f,add(K,const(-2))),-1)),
         'complete collapsedK carry contradiction polynomial')
    carry_positive = shifted(gap,{0:2,1:3})
    need(all(c > 0 for c in carry_positive.values()) and carry_positive.get((),0) == 17,
         'strict unbounded carry contradiction at f>=2,K>=3')
    # The first K square dominates t(t+1) at every integer t>=1.
    t = var(0)
    need(add(mul(add(t,const(2)),add(t,const(2))),scale(mul(t,add(t,const(1))),-1))
         == add(scale(t,3),const(4)), 'unbounded K majorant from literal first square')
    carry_cases = 0
    branches = set()
    for k0 in range(3,13):
        for f0 in range(2,11):
            d = f0*k0*k0
            for b in range(d+2,d+2+2*k0):
                shift = d+k0
                need(shift < 2*b, 'weak-radix shifted index below2b')
                u = pow(b+1,shift,b)
                digit = (pow(b+1,shift,b*b)-u)//b
                need(u == 1 and digit == shift % b, 'first coefficient with real carry')
                if shift < b:
                    branches.add('below')
                    need((d+1+digit-1)//digit == 1, 'no-carry branch forces ceiling1')
                elif shift == b:
                    branches.add('equal')
                    need(digit == 0, 'boundary gives forbidden zero digit')
                else:
                    branches.add('above')
                    need(0 < digit <= k0-2 and f0*digit < d+1, 'carry contradicts literal ceiling')
                carry_cases += 1
    need(branches == {'below','equal','above'}, 'all three weak-radix branches exercised')
    factorial_cases = 0
    for k0 in range(2,10):
        m = factorial(k0)
        for f0 in sorted({1,max(1,m//2),m-1,m,m+1}):
            d = f0*k0*k0
            ratio = Fraction((d+1)**k0,comb(k0+d,k0))
            need(Fraction(m*(2*f0-1),2*f0) < ratio <= m,
                 'strict factorial fixed-point bound, including k2/f1')
            need(((ratio.numerator+ratio.denominator-1)//ratio.denominator == f0) == (f0 == m),
                 'local factorial fixed-point control')
            factorial_cases += 1
    for g in range(1,12):
        need(comb(1+g,1) == g+1 and (g+1+comb(1+g,1)-1)//comb(1+g,1) == 1,
             'factorial1 t=1 has exact ceiling1 without fixed-point lemma')
    product_cases = 0
    for t0 in range(1,8):
        k0 = (t0+2)**2
        for f0 in (2,3,7):
            D = 1+f0*k0*k0
            N = D**k0
            B = (1+(t0+1)*f0)**t0
            coefficient = comb(t0+B+2,t0)
            need(coefficient <= (B+3)**t0 <= D**(t0*(t0+1)) <= N,
                 'complete choose2 coefficient majorant without factorial-sized f')
            need(all(comb(t0+B+2,j) <= coefficient for j in range(t0+1)),
                 'every lower coefficient is a valid digit')
            Q = f0*(B+2)-1
            dividend = f0**t0*factorial(t0)*coefficient
            J = prod(1+f0*j for j in range(1,t0+1))
            need(dividend == prod(f0*(B+2+j) for j in range(1,t0+1))
                 and 1 < J < B < Q and dividend % Q == J,
                 'actual product congruence and unique strict remainder including t1')
            product_cases += 1

    corruptions = []
    def reject(name, action):
        try:
            action()
        except (ValueError,KeyError,IndexError,TypeError):
            corruptions.append(name)
        else:
            raise ValueError('corruption accepted: ' + name)
    bad = deepcopy(data['exact_source_cuts']['product_division'])
    bad['row_combination'][0]['multiplier'][0][0] += 1
    reject('changed original product ideal multiplier',lambda:collect(bad))
    reject('raw59 smuggled into actual frame',lambda:collect(data['frame_cut'],poly(
        [[1,[643]],[-2,[]]]+[[-1,[v]] for v in sorted(arguments | {59})])))
    reject('old raw59-dependent quotient factor before sign restoration',lambda:positive(poly(
        next(step['factor'] for step in prefix['five_stages'] if step['variable'] == 130))))
    reject('drop encoded-index successor offset',lambda:collect(data['exact_source_cuts']['M_from_E'],
        poly([[1,[]],[1,[87,59]],[-1,[129]]])))
    first = data['actual_calls'][0]
    reject('substitute encoded raw59 for actual pow0 output',lambda:collect(first['cut'],poly(
        [[1,[first['X']]],[-1,[644,first['Y']]],[1,[first['base'],first['Y']]],[-1,[59]],
         [-1,[first['modulus'],first['quotient']]]])))
    reject('assume E strictly positive during modified prefix',lambda:need(137 in strict,
        'E remains only nonnegative until final product proof'))
    # Execution of the focused author checker is isolated and never provides
    # the independent sparse operations or the dependency proof above.
    reports = {}
    with tempfile.TemporaryDirectory(prefix='encoded-index74-independent-peer-') as tmp:
        for optimized in (False,True):
            output = Path(tmp)/('optimized.json' if optimized else 'normal.json')
            command = [sys.executable,'-B']+(['-O'] if optimized else [])
            proc = subprocess.run(command+[str(AUTHOR/'check.py'),'--output',str(output)],
                                  capture_output=True,text=True)
            need(proc.returncode == 0, 'author scratch replay: '+proc.stderr)
            report = load(output)
            need(report['status'] == 'PASS' and report['optimized_python'] == optimized,
                 'explicit author PASS and interpreter mode')
            reports['optimized' if optimized else 'normal'] = report
    a,b = deepcopy(reports['normal']),deepcopy(reports['optimized'])
    a.pop('optimized_python'); b.pop('optimized_python')
    need(a == b, 'normal and optimized author semantic receipts agree exactly')
    result = dict(status='PASS',optimized_python=bool(sys.flags.optimize),source_predicates=74,
        ordinary_mathematical_review='PASS: early signs; modified prefix/frame; local dichotomy with weak-radix carry; factorial/parity guards; first-ten powers; choose1/2 digits; strict moduli-product remainder; unchanged-body existence maps',
        source_pins={**PINS,str(Path(__file__).relative_to(ROOT)):sha(Path(__file__)),
                     str(Path(__file__).with_suffix('.md').relative_to(ROOT)):sha(Path(__file__).with_suffix('.md'))},
        independent_polynomial_implementation=True,independent_original_row_identities=count,
        independent_ordered_sign_steps=signs,independent_strict_constructor_steps=constructors,
        nonnegative_prefix_coordinates=len(known),omitted_prefix_coordinate=59,
        actual_frame_argument_count=len(arguments),frame_contains_raw59=False,
        interpreted_local_calls_before_index_guards=[1,5,6],parity_only_call_before_index_guards=2,
        interpreted_calls_after_index_guards=list(range(10)),
        independent_boolean_parity_identities=4,
        weak_radix_controls=carry_cases,weak_radix_branches=sorted(branches),
        strict_factorial_controls=factorial_cases,factorial1_t1_controls=11,
        product_majorant_and_remainder_controls=product_cases,
        unbounded_carry_gap_shifted_coefficients=[[c,list(m)] for m,c in sorted(carry_positive.items())],
        rejected_corruptions=corruptions,author_normal_and_optimized_replays=reports,
        author_packet_modified=False,source_builder_optimizer_or_emitter_executed=False,
        author_module_imported=False,projected_equation_or_metrics_claimed=False,lean_run=False,
        scope='Ordinary unbounded integer-source equivalence of74 and75 predicates, with exact source/dependency audit and supplementary finite controls. No new full quartic, projected metric, Lean or internal-ZFC theorem.')
    output = args.output or Path(__file__).with_suffix('.json')
    output.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
    print(json.dumps({k:result[k] for k in ('status','source_predicates','independent_original_row_identities',
        'independent_ordered_sign_steps','independent_strict_constructor_steps','projected_equation_or_metrics_claimed')},indent=2))


if __name__ == '__main__':
    main()
