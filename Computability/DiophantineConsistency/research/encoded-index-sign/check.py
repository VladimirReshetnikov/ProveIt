#!/usr/bin/env python3
"""Actual source/prefix/frame audit for the corrected encoded-index sign proof.

No optimizer, historical emitter or source builder is imported or executed.
The unbounded arithmetic is in PROOF.md; finite controls supplement complete
original-row identities and the ordered modified prefix certificate.
"""
import argparse
from collections import Counter
from copy import deepcopy
from hashlib import sha256
import importlib.util
import json
from math import comb, factorial, prod
from pathlib import Path
import sys
sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]

def need(ok,message):
    if not ok:
        raise ValueError(message)

def load(path):
    return json.loads(path.read_bytes())

def digest(path):
    return sha256(path.read_bytes()).hexdigest()

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path,required=True)
    args = parser.parse_args()
    pins = load(HERE/'SOURCE_PINS.json')
    for name,h in pins['files'].items():
        need(digest(ROOT/name)==h,'whole frozen source dependency '+name)
    if (HERE/'MANIFEST.json').exists():
        inventory = load(HERE/'MANIFEST.json')['files']
        need({str(p.relative_to(HERE)) for p in HERE.rglob('*') if p.is_file() and p.name!='MANIFEST.json'}==set(inventory), 'closed research inventory')
        for name,h in inventory.items():
            need(digest(HERE/name)==h,'sealed member '+name)
    spec = importlib.util.spec_from_file_location('encoded_sign_independent_poly',ROOT/'reviews/main-root-modulus-signs-peer.py')
    p = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(p)
    P,C,V,add,mul,product = p.P,p.C,p.V,p.plus,p.times,p.product
    data = load(HERE/'CERTIFICATE.json')
    raw = load(ROOT/'candidates/projected-radius-mixed-bounds/source/raw_builder.json')
    prior = load(ROOT/'research/main-root-and-modulus-signs/CERTIFICATE.json')
    local = load(ROOT/'research/paired-index-guards/LOCAL_FACTORIAL_CERTIFICATE.json')
    parent75 = load(ROOT/'research/factorial-radius-output-sign/SOURCE_PINS.json')
    old = load(ROOT/'candidates/projected-radius-comparison-base/domain_certificate.json')
    oldguards = {g['raw_variable'] for g in old['guards']}
    removed = {59,93,674,711,779,861,1214}
    kept = oldguards-removed
    need(len(kept)==71 and pins['removed_original_predicates']==data['omitted_original_predicates']==sorted(removed)
         and set(parent75['removed_original_predicates'])==removed-{59},'exact74-domain boundary')
    need(pins['new_predicates']==data['inherited_replacement_predicates']==parent75['new_predicates']
         and len(pins['new_predicates'])==3,'same strictV/product/f>=2 predicates')
    need({94,95,113,537,694}<=kept,'all direct early-sign/bootstrap premises retained')
    rows = [P(row['terms']) for row in raw['rows']]
    occurrences = [i for i,row in enumerate(rows) if 59 in p.vars_(row)]
    need(occurrences==data['source_occurrences_of_59']==[114],'ALL original source occurrences of59')
    cut_count = 0
    def collect(cut,target=None):
        nonlocal cut_count
        value = {}
        for item in cut['row_combination']:
            need(type(item['row']) is int and 0<=item['row']<len(rows),'literal source row index')
            value = add(value,mul(P(item['multiplier']),rows[item['row']]))
        if target is None:
            target = P(cut.get('polynomial',cut.get('expanded_polynomial')))
        need(value==target,'every coefficient of complete original-row ideal')
        cut_count += 1
        return value
    expected = {
      'E_definition':[[1,[137]],[-1,[59]],[-1,[]]],
      'M_from_E':[[1,[]],[1,[87,137]],[-1,[129]]],
      'N_early':[[1,[93]],[-1,[87,94]],[-1,[87,95]],[1,[95]],[-1,[87]]],
      'local0_factorial_remainder_bound':[[1,[91]],[-1,[94]],[-1,[95]],[-1,[]]],
      'local0_digit_bound':[[1,[530]],[-1,[91]],[-1,[537]],[-1,[]]],
      'local0_radix':[[1,[530]],[-1,[129]],[-1,[129,93]],[-1,[129,113]]],
      'local0_K_input':[[1,[63]],[-1,[4]],[-1,[1]],[-1,[2]],[-1,[3]],[-2,[]]],
      'local0_radius':[[1,[89]],[-1,[87,86,86]]],
      'local0_shift':[[1,[90]],[-1,[86]],[-1,[89]]],
      'local0_pow1_base':[[1,[92]],[-1,[89]],[-1,[]]],
      'local0_factorial_ceiling':[[1,[87,91]],[-1,[93]],[-1,[95]]],
      'local0_odd_base103':[[1,[103]],[-1,[]],[-1,[5,87]]],
      'local0_opposite_index_parity':[[1,[122]],[-1,[4]],[-1,[104]],[-2,[]]],
      'd1_radius':[[1,[109]],[-1,[107,4,4]]],
      't_shift':[[1,[110]],[-1,[4]],[-1,[109]]],
      't_base':[[1,[112]],[-1,[]],[-1,[109]]],
      'factorial1_remainder':[[1,[111]],[-1,[114]],[-1,[115]],[-1,[]]],
      'factorial1_ceiling':[[1,[107,111]],[-1,[113]],[-1,[115]]],
      'choose1_digit':[[1,[546]],[-1,[547,111]],[-1,[547,530,548]],[-1,[549]]],
      'choose1_remainder':[[1,[547]],[-1,[549]],[-1,[550]],[-1,[]]],
      'choose1_digit_bound':[[1,[530]],[-1,[111]],[-1,[551]],[-1,[]]],
      'choose2_digit':[[1,[560]],[-1,[547,123]],[-1,[547,530,561]],[-1,[562]]],
      'choose2_remainder':[[1,[547]],[-1,[562]],[-1,[563]],[-1,[]]],
      'choose2_digit_bound':[[1,[530]],[-1,[123]],[-1,[564]],[-1,[]]],
      'B_plus_two':[[1,[105]],[-1,[104]],[-2,[]]],
      'product_modulus':[[1,[126]],[1,[]],[-1,[87,104]],[-2,[87]]],
      'product_division':[[1,[106,107,123]],[-1,[129]],[-1,[126,130]]],
      'product_remainder':[[1,[126]],[-1,[129]],[-1,[131]],[-1,[]]],
    }
    ordinates = [seed['pair'][1][1] for seed in raw['seeds']]
    expected['V_product'] = [[c,list(m)] for m,c in sorted(add(V(656),product([add(V(1214),C(1))]
          +[mul(V(y),V(y)) for y in ordinates]),-1).items())]
    need(set(expected)==set(data['exact_source_cuts']),'every required new/local source interface present')
    for name,target in expected.items():
        collect(data['exact_source_cuts'][name],P(target))
    need(data['exact_source_cuts']['N_early']==load(ROOT/'research/factorial-radius-output-sign/CERTIFICATE.json')['combined'], 'unchanged early75 output-sign identity')
    prefix = prior['prefix_proof']
    initial = set(prefix['initial_semantic_guard_indices'])
    need(len(initial)==61 and initial-kept=={59,93},'exact two omitted initial direct signs')
    need(data['early_derived_bounds']=={'87':2,'93':2,'129':1,'137':0},'early bounds are exactly those derived in proof, no strongM premise')
    known = {v:0 for v in initial-{59,93}}
    known.update({int(v):L for v,L in data['early_derived_bounds'].items()})
    canonical = prior['positive_prefix']['canonical_modulus_cut']
    collect(canonical,P([[1,[]],[1,[59,87]],[1,[87]],[-1,[129]]]))
    rewrites = {step['variable']:step for step in data['rewritten_prefix_bounds']}
    need(set(rewrites)=={130,517},'only the two actual59-dependent bounds rewritten')
    def positive(q):
        need(p.vars_(q)<=set(known),'every odd-sign/lower-bound dependency available')
        shifted = {}
        for m,c in q.items():
            shifted = add(shifted,product([C(c)]+[add(V(v),C(known[v])) for v in m]))
        need(all(c>=0 for c in shifted.values()) and shifted.get((),0)>0,'unbounded shifted positivity certificate')
    sign_count = 0
    skipped = []
    def sign(step):
        nonlocal sign_count
        v,c,R = step['variable'],step['coefficient'],P(step['rhs'])
        if v==137:
            need(data['skip_prefix_sign']==dict(variable=137,row=114) and step['row']==114 and known[137]>=0,'only E sign inference replaced by early proof')
            skipped.append(114)
            return
        need(59 not in p.vars_(rows[step['row']]) and v<643 and c>0,'no unknown59 sign in other actual rows')
        pivot = add(mul(C(c),V(v)),R,-1)
        need(rows[step['row']] in (pivot,mul(C(-1),pivot)),'entire original ordered sign row')
        if step['kind']=='positive_monomials':
            deps = {v for m in R for v,n in Counter(m).items() if n%2}
            need(deps==set(step['dependencies']) and deps<=set(known) and all(c>0 for c in R.values()),'all earlier odd-power signs')
        else:
            need(step['kind']=='affine_square' and mul(P(step['square_root']),P(step['square_root']))==R,'domain-independent square')
        known[v] = max(known.get(v,0),0)
        sign_count += 1
    def bound(original):
        v,L = original['variable'],original['lower']
        F,G = P(original['factor']),P(original['rhs'])
        old_target = collect(original,add(mul(V(v),F),G,-1))
        if v in rewrites:
            new = rewrites[v]
            F,G = P(new['factor']),P(new['rhs'])
            if v==130:
                need(F==P([[1,[129]],[1,[]],[1,[131]]]) and G==P([[1,[106,107,123]],[-1,[129]]]), 'exact weakM quotient130 factors')
                multiplier = P([[-1,[130]],[-1,[]]])
            else:
                need(F==V(129) and G==V(516),'exact weakM quotient517 factors')
                multiplier = P([[-1,[517]]])
            target = add(mul(V(v),F),G,-1)
            need(new['lower']==L and add(old_target,mul(multiplier,P(canonical['polynomial'])))==target,'complete canonicalM rewrite algebra')
            collect(new,target)
        need(v not in p.vars_(F)|p.vars_(G),'no target used as premise in its own lower bound')
        positive(F)
        positive(add(G,mul(C(L-1),F),-1))
        known[v] = max(known.get(v,L),L)
    for step in prefix['preliminary_t_n_bounds']:
        bound(step)
    for step in prefix['five_stages']:
        for item in step['preceding_sign_steps']:
            sign(item)
        bound(step)
    for step in prefix['final_sign_steps']:
        sign(step)
    need(set(known)==set(range(643))-{59} and sign_count==574 and skipped==[114], 'complete modified642-coordinate prefix, not an assumed full closure')
    strict = {4,5,129,87,93}
    strict_count = 0
    for step in prior['positive_prefix']['steps']:
        v = step['variable']
        if v==137:
            need(data['skip_strict_constructor']==137,'E can still be zero')
            continue
        row = rows[step['row']]
        need(row.get((v,))==1 and all(v not in m or m==(v,) for m in row),'actual strict constructor definition')
        R = {m:-c for m,c in row.items() if m!=(v,)}
        monomial = tuple(step['positive_monomial'])
        need(p.vars_(R)<=set(known) and all(c>0 for c in R.values()) and R.get(monomial,0)>0 and set(monomial)<=strict,'strict construction without137 positivity')
        strict.add(v)
        strict_count += 1
    arguments = {v[1] for call in raw['powers'] for v in (call['base'],call['exponent'],call['output'])}
    need(data['frame_arguments']==prior['frame_arguments'] and arguments==set(data['frame_arguments'])
         and len(arguments)==43 and 59 not in arguments and arguments<=set(known),'the ACTUAL frame excludes59 and bounds every actual argument')
    need({call['base'][1] for call in raw['powers']}<=strict and {call['exponent'][1] for call in raw['powers']}<=strict and strict_count==430,'all actual base/index positivity, despite E possibly zero')
    need(data['expected_prefix']==dict(nonnegative_count=642,excluded_coordinate=59,sign_steps=574,strict_steps=430),'exact advertised prefix census')
    collect(data['frame_cut'],P([[1,[643]],[-2,[]]]+[[-1,[v]] for v in sorted(arguments)]))
    gates = {row['gate']:P(row['terms']) for row in raw['rows'] if row.get('gate') is not None}
    need(data['K_square_chain']==list(range(64,87)),'the actual23-square K constructor')
    for v in range(64,87):
        need(gates[v]==add(V(v),mul(V(v-1),V(v-1)),-1),'each exact K square')
    need(data['actual_calls']==prior['power_calls'][:10] and data['seeds']==prior['seeds'][:5], 'exact first-ten/five-seed source binding')
    for i,call in enumerate(data['actual_calls']):
        need([raw['powers'][i][key] for key in ('base','exponent','output')]==[['v',call[key]] for key in ('base','exponent','output')], 'no encoded-index59 output substituted for an actual call')
        collect(call['cut'],P([[1,[call['X']]],[-1,[644,call['Y']]],[1,[call['base'],call['Y']]],[-1,[call['output']]],[-1,[call['modulus'],call['quotient']]]]))
        collect(next(item['cut'] for item in prior['moduli'] if item['base']==call['base']))
    for seed in data['seeds']:
        for cut in seed['cuts'].values():
            collect(cut)
    need(data['seeds'][3]['aliases']['YminusK'] in kept and {data['seeds'][j]['aliases']['YminusK'] for j in (0,1,2,4)}=={674,711,779,861},'retained shifted-t bound and exactly four recovered bounds')
    for name in ('bootstrap_norm','unit_norm_cut','comparison_base_constructor','comparison_base_congruence'):
        collect(prior[name])
    collect(data['parity_t_norm'])
    # Supplementary arithmetic controls: the carry branch b<=s must actually
    # occur, rather than silently reverting to the old strong-radix proof.
    carry_cases = 0
    carry_branch_seen = False
    for K in range(3,8):
        for f in range(2,7):
            d = f*K*K
            N = d+1
            shift = d+K
            for offset in range(K+2):
                b = d+2+offset
                Cdigit = shift%b
                need(shift<2*b,'weak-radix s<2b diagnostic')
                if shift<b:
                    need(Cdigit==shift and (N+Cdigit-1)//Cdigit==1,'no-carry collapsedK forces f1')
                elif shift==b:
                    need(Cdigit==0,'zero digit violates C>=1')
                else:
                    need(0<Cdigit<=K-2 and f*Cdigit<N,'carry collapsedK contradicts the actual ceiling')
                    carry_branch_seen = True
                carry_cases += 1
    need(carry_branch_seen,'the formerly omitted first-digit carry is covered')
    product_cases = 0
    for t in range(1,7):
        K = (t+2)**2
        f = factorial(K)
        D = 1+f*K*K
        N = D**K
        B = (1+(t+1)*f)**t
        C2 = comb(t+B+2,t)
        need(K>t*(t+1) and C2<=(B+3)**t<=D**(t*(t+1))<=N,'full coefficient majorant including t1')
        need(all(comb(t+B+2,j)<=C2 for j in range(t+1)),'all lower coefficients, not just target')
        Q = f*(B+2)-1
        dividend = f**t*factorial(t)*C2
        J = prod(1+f*j for j in range(1,t+1))
        need(1<J<B<Q and dividend%Q==J,'actual moduli-product congruence and strict range')
        product_cases += 1
    rejected = []
    def reject(label,action):
        try:
            action()
        except (ValueError,KeyError,IndexError,TypeError):
            rejected.append(label)
        else:
            raise ValueError('corruption accepted '+label)
    badcut = deepcopy(data['exact_source_cuts']['choose2_remainder'])
    badcut['row_combination'][0]['multiplier'][0][0] += 1
    reject('changed complete choose2 remainder ideal',lambda:collect(badcut))
    reject('old59-dependent factor used before recovering59',
           lambda:positive(P(next(step['factor'] for step in prefix['five_stages'] if step['variable']==130))))
    reject('incorrect frame includes encoded59 as a power argument',
           lambda:collect(data['frame_cut'],P([[1,[643]],[-2,[]]]+[[-1,[v]] for v in sorted(arguments|{59})])))
    reject('drop successor offset from the encoded-index modulus',
           lambda:collect(data['exact_source_cuts']['M_from_E'],P([[1,[]],[1,[87,59]],[-1,[129]]])))
    first = data['actual_calls'][0]
    reject('misbind encoded59 as the first t-power output',
           lambda:collect(first['cut'],P([[1,[first['X']]],[-1,[644,first['Y']]],[1,[first['base'],first['Y']]],[-1,[59]],[-1,[first['modulus'],first['quotient']]]])))
    result = dict(status='PASS',optimized_python=bool(sys.flags.optimize),source_predicates=74,
        retained_original_scalar_predicates=71,replacement_predicates=3,
        nonnegative_prefix_coordinates=len(known),ordered_sign_steps=sign_count,strict_constructor_steps=strict_count,
        skipped_source_sign_rows=skipped,rewritten_bounds=[130,517],actual_frame_arguments=43,frame_contains59=False,
        complete_original_row_identities=cut_count,first_actual_calls=list(range(10)),
        collapsedK_weak_radix_controls=carry_cases,first_digit_carry_branch_seen=True,
        moduli_product_and_majorant_controls=product_cases,t1_case_included=True,rejected_corruptions=rejected,
        source_pins={str((HERE/name).relative_to(ROOT)):digest(HERE/name) for name in ['PROOF.md','SOURCE_PINS.json','CERTIFICATE.json','check.py']},
        source_builder_optimizer_or_emitter_executed=False,projected_equation_or_metrics_claimed=False,
        scope='Complete original-row identities and modified642-coordinate prefix/frame for the ordinary74-predicate corrected proof. Arithmetic controls supplement its unbounded argument. No projected metrics, Lean or internal-ZFC theorem.')
    text = json.dumps(result,indent=2,sort_keys=True)+'\n'
    args.output.write_text(text)
    print(text,end='')

if __name__ == '__main__':
    main()
