#!/usr/bin/env python3
"""Independent actual-source audit for the72-predicate shifted-t index proof.

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
    need(data['raw_coordinate_omitted']==data['omitted_predicate']==pins['newly_removed_raw_guard']==825 and
         data['parent73_omitted_predicate']==104 and data['parent74_omitted_predicate']==59 and
         data['pow2_stage_omitted_coordinate']==data['B_alias']==pins['signed_actual_frame_argument']==104 and
         data['successor_coordinate']==data['B_successor_alias']==105 and data['Q_alias']==126,
         'actual B/positive-successor/product-modulus coordinate aliases')
    raw = load(ROOT/'candidates/projected-radius-mixed-bounds/source/raw_builder.json')
    prior = load(ROOT/'research/main-root-and-modulus-signs/CERTIFICATE.json')
    parent74 = load(ROOT/'research/encoded-index-sign/SOURCE_PINS.json')
    old = load(ROOT/'candidates/projected-radius-comparison-base/domain_certificate.json')
    oldguards = {g['raw_variable'] for g in old['guards']}
    removed = {59,93,104,674,711,779,825,861,1214}
    kept = oldguards-removed
    need(len(kept)==69 and pins['removed_original_predicates']==data['omitted_original_predicates']==sorted(removed)
         and set(parent74['removed_original_predicates'])==removed-{104,825},'exact72-domain boundary')
    need(pins['new_predicates']==data['inherited_replacement_predicates']==parent74['new_predicates']
         and len(pins['new_predicates'])==3,'same strictV/product/f>=2 predicates')
    need({6,94,95,113,131,537,694}<=kept,'all direct early-sign/bootstrap/support premises retained')
    rows = [P(row['terms']) for row in raw['rows']]
    occurrences = [i for i,row in enumerate(rows) if 59 in p.vars_(row)]
    need(occurrences==data['source_occurrences_of_59']==[114],'ALL original source occurrences of59')
    occurrences104 = [i for i,row in enumerate(rows) if 104 in p.vars_(row)]
    need(occurrences104==data['source_occurrences_of_104']==[88,693,1151],
         'ALL original source occurrences of104, with only row88 in prefix')
    occurrences825 = [i for i,row in enumerate(rows) if 825 in p.vars_(row)]
    need(occurrences825==data['source_occurrences_of_825']==[762]
         and raw['variables'][825]==dict(kind='witness',name='index3.YminusK'),
         'newly omitted coordinate is the actual private shifted-t slack')
    need(len(raw['rows'])==pins['raw_source_rows']==1177 and
         len(raw['variables'])==pins['raw_source_coordinates']==1259,
         'entire unchanged raw source, no projected dimension claim')
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
      'positive_B_successor':[[1,[87,105]],[-1,[129]],[-1,[131]],[-2,[]]],
      'positive_k122_constructor':[[1,[122]],[-1,[4]],[-1,[105]]],
    }
    ordinates = [seed['pair'][1][1] for seed in raw['seeds']]
    expected['V_product'] = [[c,list(m)] for m,c in sorted(add(V(656),product([add(V(1214),C(1))]
          +[mul(V(y),V(y)) for y in ordinates]),-1).items())]
    need(set(expected)==set(data['exact_source_cuts']),'every required new/local source interface present')
    for name,target in expected.items():
        collect(data['exact_source_cuts'][name],P(target))
    combined_t1 = collect(data['t1_combined_source_cut'],P([
        [1,[107,111]],[-1,[113]],[-1,[115]],[1,[112]],[-1,[]],[-1,[107,4,4]]]))
    need(data['exact_source_cuts']['N_early']==load(ROOT/'research/factorial-radius-output-sign/CERTIFICATE.json')['combined'], 'unchanged early75 output-sign identity')
    prefix = prior['prefix_proof']
    initial = set(prefix['initial_semantic_guard_indices'])
    need(len(initial)==61 and initial-kept=={59,93,104},'exact three omitted initial direct signs')
    need(data['early_derived_bounds']=={'87':2,'93':2,'105':1,'129':1,'137':0},'early bounds include only actual positive successor, no B sign')
    known = {v:0 for v in initial-{59,93,104}}
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
        if v in {105,137}:
            expected_row = {105:88,137:114}[v]
            need(dict(variable=v,row=expected_row) in data['skip_prefix_sign'] and
                 step['row']==expected_row and known[v]>= (1 if v==105 else 0),
                 'only successor sign inferences replaced by exact early proofs')
            skipped.append(expected_row)
            return
        need(not ({59,104}&p.vars_(rows[step['row']])) and v<643 and c>0,'no unknown59/104 sign in other actual prefix rows')
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
    need(set(known)==set(range(643))-{59,104} and sign_count==573 and skipped==[88,114], 'complete modified641-coordinate prefix, not an assumed full closure')
    strict = {4,5,129,87,93,105}
    strict_count = 0
    for step in prior['positive_prefix']['steps']:
        v = step['variable']
        if v in {105,137}:
            need(data['skip_strict_constructors']==[105,137], '105 positive by early proof; E can still be zero')
            continue
        row = rows[step['row']]
        need(row.get((v,))==1 and all(v not in m or m==(v,) for m in row),'actual strict constructor definition')
        R = {m:-c for m,c in row.items() if m!=(v,)}
        monomial = tuple(step['positive_monomial'])
        need(p.vars_(R)<=set(known) and all(c>0 for c in R.values()) and R.get(monomial,0)>0 and set(monomial)<=strict,'strict construction without59/104 signs or137 positivity')
        strict.add(v)
        strict_count += 1
    arguments = {v[1] for call in raw['powers'] for v in (call['base'],call['exponent'],call['output'])}
    need(data['frame_arguments']==prior['frame_arguments'] and arguments==set(data['frame_arguments'])
         and len(arguments)==43 and {59,825}.isdisjoint(arguments) and 104 in arguments and arguments-{104}<=set(known),
         'ACTUAL43-argument frame, with sole possibly negative argument104')
    need(data['weak_frame_nonnegative_arguments']==sorted(arguments-{104}) and {4,86,103}<=arguments-{104},
         'all actual other42 arguments, including t/K/base103, in weak positive frame')
    need({call['base'][1] for call in raw['powers']}<=strict and {call['exponent'][1] for call in raw['powers']}<=strict and strict_count==429,'all actual base/index positivity from actual positive105 constructor')
    need(data['expected_prefix']==dict(nonnegative_count=641,excluded_coordinates=[59,104],sign_steps=573,strict_steps=429),'exact advertised prefix census')
    collect(data['frame_cut'],P([[1,[643]],[-2,[]]]+[[-1,[v]] for v in sorted(arguments)]))
    collect(data['weak_frame_cut'],P([[1,[643]],[-1,[105]]]+[[-1,[v]] for v in sorted(arguments-{104})]))
    gates = {row['gate']:P(row['terms']) for row in raw['rows'] if row.get('gate') is not None}
    need(data['K_square_chain']==list(range(64,87)),'the actual23-square K constructor')
    for v in range(64,87):
        need(gates[v]==add(V(v),mul(V(v-1),V(v-1)),-1),'each exact K square')
    need(data['actual_calls']==prior['power_calls'][:10] and
         data['seeds']==prior['seeds'][:5], 'exact first-ten-call/five-seed literal binding; chronology checked separately')
    for call in data['actual_calls']:
        i = call['index']
        need([raw['powers'][i][key] for key in ('base','exponent','output')]==[['v',call[key]] for key in ('base','exponent','output')], 'no encoded-index59 output substituted for an actual call')
        collect(call['cut'],P([[1,[call['X']]],[-1,[644,call['Y']]],[1,[call['base'],call['Y']]],[-1,[call['output']]],[-1,[call['modulus'],call['quotient']]]]))
        collect(next(item['cut'] for item in prior['moduli'] if item['base']==call['base']))
    for seed in data['seeds']:
        for cut in seed['cuts'].values():
            collect(cut)
    need({data['seeds'][i]['aliases']['YminusK'] for i in [0,4]}=={674,861} and not ({674,861}&kept),
         'exact two missing t/k122 slacks, covered only by retained product predicate')
    for name in ('bootstrap_norm','unit_norm_cut','comparison_base_constructor','comparison_base_congruence'):
        collect(prior[name])
    collect(data['parity_t_norm'])
    need(data['calls_used_before_B_recovery']==[0,2,9] and
         data['support_calls_for_t_k122']==[0,9], 'only sign-safe support calls0/9 and final actual call2 needed')
    need(data['negative_branch']==dict(B=-1,D=1,k122_minus_t=1,seed_recovery_is_conditional=True),
         'seed recovery only under sole negative branch with consecutive positive indices')
    calls = {call['index']:call for call in data['actual_calls']}
    def support_ports(selected):
        need(selected[0]['output']==6 and 6 in kept and selected[9]['output']==560 and 560 in known and
             selected[0]['base']==5 and selected[9]['base']==531 and {5,531}<=strict,
             'paired strict seed orientation uses actual nonnegative outputs6/560, not104')
    support_ports(calls)
    need([calls[2][k] for k in ['base','exponent','output','X','Y']]==[103,4,104,670,671],
         'final call2 is actual B output at t seed; no other power meaning needed')
    # Bind the NEW chronology independently of the producer's stage labels.
    chronology = data['chronology']
    expected_chronology = dict(
        early_B_recovery_calls=[0,2,9],local_factorial0_calls=[1,5,6],
        local_factorial0_support_seeds=[1,2],paired_t_k122_support_calls=[0,9],
        interpreted_calls_before_825=[0,1,2,3,4,5,6,8,9],calls_not_interpreted_before_825=[7],
        known_slacks_after_factorial0_and_pairing=[674,711,779,861],
        shifted_t_seed=3,shifted_t_slack=825,shifted_t_index=110,shifted_t_X=821,shifted_t_Y=822,
        collapsed_seed3_support_call=7,collapsed_seed3_base=531,collapsed_seed3_output=546,
        choose1_denominator_call=8,choose1_denominator=547,choose1_digit=111,
        t1_numerator_call=4,t1_numerator=113,t1_factorial_candidate=107,
        t1_branch_needs_factorial1_semantics=False,late_guard_identity='raw825=raw822-raw110',
        whole_parent73_theorem_used_only_after825_recovered=True)
    def schedule(candidate):
        need(candidate==expected_chronology,'exact partial-parent schedule, with call7 excluded before825')
    schedule(chronology)
    need(825 not in kept and 825 not in initial and 825 not in known and 825 not in strict,
         'missing825 is never silently installed as an early sign')
    need(set(chronology['known_slacks_after_factorial0_and_pairing'])==
         {data['seeds'][i]['aliases']['YminusK'] for i in [0,1,2,4]},
         'early recovery covers exactly t/K/shiftedK/k122, not shifted-t')
    early_seed_pairs={(seed['aliases']['X'],seed['aliases']['Y']) for i,seed in enumerate(data['seeds']) if i!=3}
    need(all((calls[i]['X'],calls[i]['Y']) in early_seed_pairs for i in chronology['interpreted_calls_before_825'])
         and all(calls[i]['exponent']!=110 for i in chronology['interpreted_calls_before_825']),
         'every pre825 interpreted call uses one of the four recovered pairs')
    def shifted_ports(selected):
        need([selected[7][k] for k in ['base','exponent','output','X','Y','modulus']]==[531,110,546,821,822,798]
             and [selected[8][k] for k in ['base','exponent','output']]==[530,4,547]
             and [selected[4][k] for k in ['base','exponent','output']]==[112,4,113],
             'actual call7 conditional support, call8 denominator, call4 t1 numerator')
    shifted_ports(calls)
    need({107,111,113,114,115,546,547,548,549}<=set(known) and {530,531,110}<=strict,
         'all shifted-t digit and t1 ceiling sign premises are prefix facts without825')
    need(data['seeds'][3]['aliases']==dict(X=821,Y=822,YminusK=825,k=110,S=823,R=824,Squotient=838,Rquotient=839),
         'actual shifted-t pair and private original slack aliases')
    collect(data['seeds'][3]['cuts']['index_at_most_Y'],P([[1,[822]],[-1,[110]],[-1,[825]]]))
    # At t=1, add only the already interpreted call4 relation113=112.
    # No g=t! or choose1-binomial semantics appears in this identity.
    def substitute_constant(poly,variable,value):
        answer={}
        for monomial,coefficient in poly.items():
            degree=monomial.count(variable)
            rest=tuple(v for v in monomial if v!=variable)
            answer=add(answer,{rest:coefficient*value**degree})
        return answer
    branch_ceiling = add(substitute_constant(combined_t1,4,1),add(V(113),V(112),-1))
    expected_t1 = P([[1,[107,111]],[-1,[107]],[-1,[]],[-1,[115]]])
    need(branch_ceiling==expected_t1,'complete t1 ideal gives g*(C111-1)=1+raw115')
    weak_frame_cases = 0
    for t in range(1,7):
        for f in range(2,9):
            B=-1; successor=B+2; n=1+(t+1)*f; K=(t+2)**2
            W=successor+t+n+K+7
            A=W**W+1
            T=2*A*n-n*n-1
            need(successor>=1 and abs(B)<W and max(t,n,K)<W and 0<n**t+1<A<=T,
                 'weak frame and forbidden negative-output residue diagnostic')
            need((t+B+2)>0 and (t+B+2-t)%2==1, 'opposite positive indices even when B=-1')
            weak_frame_cases+=1
    collapsed_large_t_cases=0
    for t in range(2,9):
        for b in range(2,21):
            for digit in range(1,5):
                need(b**t*digit>b+1,'t>=2 digit lower bound excludes collapsed numerator')
                collapsed_large_t_cases+=1
    t1_ceiling_cases=0
    for g in range(7):
        for digit in range(1,9):
            for slack in range(7):
                if g*digit==1+g+slack:
                    need(g>=1 and digit>=2,'t1 ceiling forces g positive and digit at least2')
                    for b in range(2,11):
                        need(b*digit>b+1,'t1 choose1 lower bound excludes collapsed numerator')
                    t1_ceiling_cases+=1
    need(t1_ceiling_cases>0,'t1 controls contain nonvacuous valid ceiling assignments')
    small_ordinate_cases=0
    for W in range(7,13):
        A=W**W+1
        for base in range(3,W):
            T=2*A*base-base*base-1
            for output in range(W):
                admissible=[]
                for X,Y in [(A,1),(-A,1),(A,-1),(-A,-1)]:
                    if (X-(A-base)*Y-output)%T==0:
                        admissible.append((X,Y))
                need(admissible==([(A,1)] if output==base else []),
                     'small-ordinate residues force actual positive pair and output=base')
                small_ordinate_cases+=1
    rejected = []
    def reject(label,action):
        try:
            action()
        except (ValueError,KeyError,IndexError,TypeError):
            rejected.append(label)
        else:
            raise ValueError('corruption accepted '+label)
    badcut = deepcopy(data['exact_source_cuts']['B_plus_two'])
    badcut['row_combination'][0]['multiplier'][0][0] += 1
    reject('changed complete B successor ideal',lambda:collect(badcut))
    reject('old59-dependent factor used before recovering59',
           lambda:positive(P(next(step['factor'] for step in prefix['five_stages'] if step['variable']==130))))
    reject('incorrect frame includes encoded59 as a power argument',
           lambda:collect(data['frame_cut'],P([[1,[643]],[-2,[]]]+[[-1,[v]] for v in sorted(arguments|{59})])))
    reject('drop successor offset from the encoded-index modulus',
           lambda:collect(data['exact_source_cuts']['M_from_E'],P([[1,[]],[1,[87,59]],[-1,[129]]])))
    first = data['actual_calls'][0]
    reject('misbind encoded59 as the first t-power output',
           lambda:collect(first['cut'],P([[1,[first['X']]],[-1,[644,first['Y']]],[1,[first['base'],first['Y']]],[-1,[59]],[-1,[first['modulus'],first['quotient']]]])))
    reject('assume old nonnegative full43-argument frame',lambda:need(arguments<=set(known),'104 remains unknown'))
    badcut = deepcopy(data['exact_source_cuts']['positive_B_successor'])
    badcut['row_combination'][0]['multiplier'][0][0] += 1
    reject('changed actual positive-successor identity',lambda:collect(badcut))
    reject('wrong weak frame omits positive successor',lambda:collect(data['weak_frame_cut'],
           P([[1,[643]]]+[[-1,[v]] for v in sorted(arguments-{104})])))
    badcalls = deepcopy(calls)
    badcalls[0]['output'] = 104
    reject('orient paired t seed using unknown104 output',lambda:support_ports(badcalls))
    bad_schedule=deepcopy(chronology)
    bad_schedule['interpreted_calls_before_825'].append(7)
    reject('interpret shifted-t call7 before restoring825',lambda:schedule(bad_schedule))
    bad_schedule=deepcopy(chronology)
    bad_schedule['t1_branch_needs_factorial1_semantics']=True
    reject('assume g=t! in the collapsed shifted-t branch',lambda:schedule(bad_schedule))
    badcut=deepcopy(data['exact_source_cuts']['choose1_digit'])
    badcut['row_combination'][0]['multiplier'][0][0]+=1
    reject('alter actual choose1 digit ideal',lambda:collect(badcut,P(expected['choose1_digit'])))
    reject('drop the positive constant from the t1 ceiling relation',
           lambda:need(branch_ceiling==P([[1,[107,111]],[-1,[107]],[-1,[115]]]),'t1 positive constant required'))
    badcalls=deepcopy(calls)
    badcalls[7]['base']=530
    reject('replace actual collapsed call7 base b+1 by b',lambda:shifted_ports(badcalls))
    reject('replace825 by the distinct paired122 slack861',lambda:collect(
        data['seeds'][3]['cuts']['index_at_most_Y'],P([[1,[822]],[-1,[110]],[-1,[861]]])))
    reject('silently add omitted825 to the early prefix',lambda:need(825 in known,'825 is not an early premise'))
    result = dict(status='PASS',optimized_python=bool(sys.flags.optimize),source_predicates=72,
        retained_original_scalar_predicates=69,replacement_predicates=3,
        nonnegative_prefix_coordinates=len(known),ordered_sign_steps=sign_count,strict_constructor_steps=strict_count,
        skipped_source_sign_rows=skipped,rewritten_bounds=[130,517],actual_frame_arguments=43,frame_contains59=False,
        sole_possible_negative_actual_argument=104,positive_successor=105,source_occurrences_of104=occurrences104,
        complete_original_row_identities=cut_count,actual_call_interfaces=list(range(10)),
        actual_calls_used_before_B_recovery=data['calls_used_before_B_recovery'],
        actual_calls_interpreted_before825=chronology['interpreted_calls_before_825'],
        source_occurrences_of825=occurrences825,frame_contains825=False,
        collapsed_large_t_controls=collapsed_large_t_cases,t1_ceiling_controls=t1_ceiling_cases,
        small_ordinate_residue_controls=small_ordinate_cases,factorial1_semantics_used=False,
        nonnegative_support_call_outputs=[6,560],
        weak_frame_and_negative_output_controls=weak_frame_cases,rejected_corruptions=rejected,
        source_pins={str((HERE/name).relative_to(ROOT)):digest(HERE/name) for name in ['PROOF.md','SOURCE_PINS.json','CERTIFICATE.json','check.py']},
        source_builder_optimizer_or_emitter_executed=False,projected_equation_or_metrics_claimed=False,
        scope='Complete original-row identities and641-coordinate prefix/weak frame for ordinary72-predicate shifted-t recovery. Only calls0..6,8,9 interpreted before825; call7 is used conditionally for small-ordinate residues, then interpreted after collapse exclusion. No factorial1 semantics, projected metrics, Lean or internal-ZFC theorem.')
    text = json.dumps(result,indent=2,sort_keys=True)+'\n'
    args.output.write_text(text)
    print(text,end='')

if __name__ == '__main__':
    main()
