#!/usr/bin/env python3
"""Exact early output-sign restoration for the75-predicate source extension.

No optimizer, emitter or source builder is imported. Polynomial identities
are checked against the complete original rows. The parent76 source checks
are replayed into scratch only after the early-sign dependency is verified.
"""
import argparse
from collections import defaultdict
from copy import deepcopy
from hashlib import sha256
import json
from pathlib import Path
import subprocess
import sys
import tempfile
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

def poly(terms):
    result = defaultdict(int)
    for coefficient,monomial in terms:
        need(type(coefficient) is int and all(type(v) is int and v>=0 for v in monomial),
             'integral sparse polynomial')
        result[tuple(sorted(monomial))] += coefficient
    return {m:c for m,c in result.items() if c}

def add(left,right,scale=1):
    result = dict(left)
    for m,c in right.items():
        result[m] = result.get(m,0)+scale*c
    return {m:c for m,c in result.items() if c}

def mul(left,right):
    result = defaultdict(int)
    for m,c in left.items():
        for n,d in right.items():
            result[tuple(sorted(m+n))] += c*d
    return {m:c for m,c in result.items() if c}

def terms(q):
    return [[c,list(m)] for m,c in sorted(q.items()) if c]

def verify(data,pins,raw,local,old,parent76,prior):
    oldguards = {g['raw_variable'] for g in old['guards']}
    removed = {93,674,711,779,861,1214}
    kept = oldguards-removed
    need(len(oldguards)==78 and len(kept)==72 and {94,95,694}<=kept,
         'exact72 old scalar predicates retained, including both direct remainder signs and T0')
    need(pins['removed_original_predicates']==sorted(removed)
         and pins['new_predicates']==parent76['new_predicates']
         and len(pins['new_predicates'])==3
         and dict(kind='at_least',raw_variable=87,lower=2) in pins['new_predicates'],
         'same three parent predicates, with the direct f>=2 premise')
    need(set(parent76['removed_original_predicates'])==removed-{93}
         and pins['restored_guard']==93 and pins['retained_direct_signs']==[94,95]
         and pins['new_predicate_used_before_prefix']==dict(raw_variable=87,lower=2),
         'the only parent76 predicate omitted is raw93')
    initial = set(prior['prefix_proof']['initial_semantic_guard_indices'])
    need(len(initial)==61 and initial-kept=={93} and initial<=kept|{93},
         'exactly one original early sign premise needs recovery')
    need(data['variables']==dict(f=87,N=93,r=94,s=95,C=91), 'actual source-coordinate roles')
    remainder = local['cuts']['factorial_remainder_bound']
    ceiling = local['cuts']['factorial_ceiling']
    need(data['original_source_cuts']==dict(factorial_remainder_bound=remainder,factorial_ceiling=ceiling),
         'both complete copied original-row source cuts')
    rows = [poly(row['terms']) for row in raw['rows']]
    def collect(cut,target=None):
        value = {}
        for item in cut['row_combination']:
            need(type(item['row']) is int and 0<=item['row']<len(rows), 'original row index')
            value = add(value,mul(poly(item['multiplier']),rows[item['row']]))
        if target is None:
            target = poly(cut.get('polynomial',cut.get('expanded_polynomial')))
        need(value==target,
             'every coefficient of the full original-row combination')
        return value
    R = collect(remainder,poly([[1,[91]],[-1,[94]],[-1,[95]],[-1,[]]]))
    E = collect(ceiling,poly([[1,[87,91]],[-1,[93]],[-1,[95]]]))
    need(R==poly([[1,[91]],[-1,[94]],[-1,[95]],[-1,[]]])
         and E==poly([[1,[87,91]],[-1,[93]],[-1,[95]]]), 'actual ceiling and remainder-bound equations')
    weights = {}
    for sign,cut in [(1,remainder),(-1,ceiling)]:
        for item in cut['row_combination']:
            multiplier = poly(item['multiplier'])
            multiplier = mul({(87,):1},multiplier) if sign==1 else {m:-c for m,c in multiplier.items()}
            weights[item['row']] = add(weights.get(item['row'],{}),multiplier)
    expected_combination = [dict(row=i,multiplier=terms(q)) for i,q in sorted(weights.items()) if q]
    need(data['combination_rule']=='f*factorial_remainder_bound-factorial_ceiling'
         and data['combined']['row_combination']==expected_combination,
         'entire combined ideal equals f times bound minus ceiling')
    combined = collect(data['combined'])
    target = poly([[1,[93]],[-1,[87,94]],[-1,[87,95]],[1,[95]],[-1,[87]]])
    need(combined==target==add(mul({(87,):1},R),E,-1), 'complete unconditional early-N identity')
    need(data['lower_bound_symbols']==dict(F=0,r=1,s=2)
         and data['lower_bound_substitution']==dict(f='F+2',F_nonnegative=True,r_nonnegative=True,s_nonnegative=True),
         'lower-bound premises use only the three retained direct signs')
    # N-2=f*r+(f-1)*s+f-2, with f=F+2. All surviving coefficients
    # are nonnegative; no sign of C, N, or any gate is needed here.
    f,r,s = {(0,):1,():2},{(1,):1},{(2,):1}
    lower = add(add(add(mul(f,r),mul(add(f,{():-1}),s)),f),{():-2})
    expected_lower = poly(data['N_minus_two_after_substitution'])
    need(lower==expected_lower==poly([[1,[0,1]],[1,[0,2]],[1,[0]],[2,[1]],[1,[2]]])
         and all(c>0 for c in lower.values()), 'unbounded nonnegative coefficient certificate for N>=2')
    need(data['guard_recovery_before_prefix'] is True, 'explicit dependency order')
    return dict(source_predicates=75,retained_original_scalar_predicates=72,unchanged_parent_predicates=75,
        new_predicates=3,initial_direct_signs=60,initial_signs_after_recovery=61,
        complete_original_row_identities=3,combined_ideal_rows=len(expected_combination),
        recovered_guard=93,recovered_lower_bound=2,power_calls_interpreted_for_recovery=0)

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path,required=True)
    args = parser.parse_args()
    if (HERE/'MANIFEST.json').exists():
        inventory = load(HERE/'MANIFEST.json')['files']
        need({str(p.relative_to(HERE)) for p in HERE.rglob('*') if p.is_file() and p.name!='MANIFEST.json'}
             ==set(inventory), 'closed full research inventory')
        for name,h in inventory.items():
            need(digest(HERE/name)==h, 'sealed research member '+name)
    pins = load(HERE/'SOURCE_PINS.json')
    for name,h in pins['files'].items():
        need(digest(ROOT/name)==h, 'entire frozen source dependency '+name)
    parent = ROOT/pins['parent76']
    for name,h in load(parent/'MANIFEST.json')['files'].items():
        need(digest(parent/name)==h, 'each complete parent76 member '+name)
    data = load(HERE/'CERTIFICATE.json')
    need(digest(ROOT/data['source_certificate'])==data['source_certificate_sha256'], 'whole local factorial certificate')
    local = load(ROOT/data['source_certificate'])
    raw = load(ROOT/'candidates/projected-radius-mixed-bounds/source/raw_builder.json')
    old = load(ROOT/'candidates/projected-radius-comparison-base/domain_certificate.json')
    prior = load(ROOT/'research/main-root-and-modulus-signs/CERTIFICATE.json')
    parent76 = load(parent/'SOURCE_PINS.json')
    result = verify(data,pins,raw,local,old,parent76,prior)
    rejected = []
    def reject(label,action):
        try:
            action()
        except (ValueError,KeyError,TypeError,IndexError):
            rejected.append(label)
        else:
            raise ValueError('corruption accepted '+label)
    bad = deepcopy(data)
    bad['combined']['row_combination'][0]['multiplier'][0][0] += 1
    reject('changed combined original-row multiplier',lambda:verify(bad,pins,raw,local,old,parent76,prior))
    bad = deepcopy(data)
    bad['combined']['polynomial'][0][0] += 1
    reject('changed early-N identity coefficient',lambda:verify(bad,pins,raw,local,old,parent76,prior))
    badpins = deepcopy(pins)
    badpins['new_predicates'][-1]['lower'] = 1
    reject('weaken f>=2 without restoring the missing lower bound',lambda:verify(data,badpins,raw,local,old,parent76,prior))
    badpins = deepcopy(pins)
    badpins['removed_original_predicates'].append(95)
    reject('remove a required direct remainder-sign predicate',lambda:verify(data,badpins,raw,local,old,parent76,prior))
    parent_replays = {}
    with tempfile.TemporaryDirectory(prefix='factorial-output-sign75-') as tmp:
        for optimized in (False,True):
            mode = 'optimized' if optimized else 'normal'
            output = Path(tmp)/(mode+'.json')
            command = [sys.executable,'-B']+(['-O'] if optimized else [])
            command += [str(parent/'check.py'),'--output',str(output)]
            proc = subprocess.run(command,capture_output=True,text=True)
            need(proc.returncode==0, 'parent76 scratch replay: '+proc.stderr)
            report = load(output)
            need(report['status']=='PASS' and report['optimized_python']==optimized, 'parent76 mode and status')
            parent_replays[mode] = report
    a,b = deepcopy(parent_replays['normal']),deepcopy(parent_replays['optimized'])
    a.pop('optimized_python');b.pop('optimized_python')
    need(a==b, 'parent source replays agree except interpreter mode')
    result.update(status='PASS',optimized_python=bool(sys.flags.optimize),rejected_corruptions=rejected,
        source_pins={str((HERE/name).relative_to(ROOT)):digest(HERE/name)
                     for name in ['PROOF.md','SOURCE_PINS.json','CERTIFICATE.json','check.py']},
        parent76_normal_and_optimized_replays=parent_replays,
        source_builder_optimizer_or_emitter_executed=False,
        projected_equation_or_metrics_claimed=False,
        scope='Ordinary75-predicate extension only: recover raw93>=2 from direct f/r/s premises before prefix closure, then inherit76. No power meaning, projected metric, Lean or internal-ZFC theorem is used to recover the sign.')
    text = json.dumps(result,indent=2,sort_keys=True)+'\n'
    args.output.write_text(text)
    print(text,end='')

if __name__ == '__main__':
    main()
