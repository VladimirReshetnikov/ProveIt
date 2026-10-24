#!/usr/bin/env python3
"""Independent frozen-source strict dependency and signed-output diagnostics.

No builder, optimizer, author checker, archive code or Lean is imported/run.
The unbounded signed-output lemma is PEER_SIGNED_OUTPUT.md. The fresh
producer/author must separately bind and replay the changed complete frame.
"""
import argparse
from collections import Counter
from hashlib import sha256
import json
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
PINS = {
 'research/common-squared-radius-source-prototype/MANIFEST.json':'64bbe1b16ef87b8c339b69e2763cdf2a452ceda537765f66c5217b716fd01fdb',
 'research/common-squared-radius-source-prototype/source/raw_builder.json':'0998af28037471adee8aebabf6080c0e97ec4ff13ab6c7f5b02fe2f2f3f84ac5',
 'research/common-factorial-square-radius/CERTIFICATE.json':'c1ea6502883a056df7ad5927304e4ea54d8fddc38886ca5f8c7b3a26a801a15d',
 'research/common-factorial-square-radius/MANIFEST.json':'9518b7b6bdf40c21bfa294d925f4089f520133e92c5a05890c1f3b10ab03fe49',
 'research/main-root-and-modulus-signs/CERTIFICATE.json':'96097a2984ab34468413c32898af70ee01c96d35470aaacc773654aca1140970',
}
QUOTIENTS = {575,584,592,600,609,618,627,636}
OUTPUTS = {573,583,591,599,607,617,625,635}
EXPECTED = [573,575,579,580,583,584,587,588,591,592,595,596,599,600,603,604,607,609,613,614,617,618,621,622,625,627,631,632,635,636,639,640]


def require(ok, message):
    if not ok:
        raise ValueError(message)


def read(path):
    return json.loads(path.read_bytes())


def digest(path):
    return sha256(path.read_bytes()).hexdigest()


def variables(terms):
    return {v for coefficient, monomial in terms for v in monomial}


def polynomial(terms):
    result = Counter()
    for coefficient, monomial in terms:
        result[tuple(sorted(monomial))] += coefficient
    return {m:c for m,c in result.items() if c}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', required=True, type=Path)
    args = parser.parse_args()
    for name, expected in PINS.items():
        require(digest(ROOT/name) == expected, 'whole frozen dependency: '+name)
    raw = read(ROOT/'research/common-squared-radius-source-prototype/source/raw_builder.json')
    prior = read(ROOT/'research/main-root-and-modulus-signs/CERTIFICATE.json')
    common = read(ROOT/'research/common-factorial-square-radius/CERTIFICATE.json')
    signs = [s for stage in prior['prefix_proof']['five_stages'] for s in stage['preceding_sign_steps']]
    signs += prior['prefix_proof']['final_sign_steps']
    signs = [dict(s, **common['changed_sign_steps'].get(str(s['variable']),{})) for s in signs]
    missing = set(QUOTIENTS)
    while True:
        before = set(missing)
        for s in signs:
            if set(s.get('dependencies',[])) & missing:
                missing.add(s['variable'])
        if before == missing:
            break
    require(sorted(missing) == EXPECTED, 'complete32-coordinate sign dependency closure')
    known = set(range(643)) - {59,104} - missing
    strict = {4,5,129,87,93,105}
    strict_rows = []
    for step in prior['positive_prefix']['steps']:
        v = step['variable']
        if v in {105,137}:
            continue
        row = polynomial(raw['rows'][step['row']]['terms'])
        require(row.get((v,)) == 1, 'complete actual strict row pivot')
        rhs = {m:-c for m,c in row.items() if m!=(v,)}
        selected = tuple(step['positive_monomial'])
        require(all(c>0 for c in rhs.values()), 'positive strict RHS coefficients')
        require({w for m in rhs for w in m} <= known, 'every strict RHS operand remains in prefix')
        require(rhs.get(selected,0)>0 and set(selected)<=strict, 'ordered selected positive monomial')
        strict.add(v)
        strict_rows.append(step['row'])
    require(len(strict_rows) == 429, 'all429 inherited strict constructors remain')
    bounds = prior['prefix_proof']['preliminary_t_n_bounds'] + prior['prefix_proof']['five_stages']
    for step in bounds:
        require(not ((variables(step['factor'])|variables(step['rhs'])) & missing), 'all bound target/factor dependencies retained')
    require(len(bounds) == 7, 'all seven ordered bounds')
    for group in ['early_cuts','unchanged_local_cuts','full_source_cuts']:
        for cut in common[group].values():
            require(not (variables(cut.get('polynomial',cut.get('expanded_polynomial',[]))) & missing), 'pre-power/local/full cut targets retained')
    for seed in prior['seeds']:
        require(not (set(seed['aliases'].values())&missing), 'all seed aliases independent of missing32')
        require(seed['aliases']['k'] in strict, 'every seed index still positive')
    affected = [c['index'] for c in prior['power_calls'] if {c[k] for k in ['base','exponent','output']}&missing]
    require(affected == [10,12,13,14,15,17,18,20], 'only eight range power outputs affected')
    retained = set(common['retained_original_guard_indices'])-QUOTIENTS
    relevant_seeds = [s for s in prior['seeds'] if s['aliases']['k'] in {44,46,48,50,52,54,56,58}]
    require(len(relevant_seeds) == 8 and all(s['aliases']['YminusK'] in retained for s in relevant_seeds), 'all eight positive-ordinate guards retained')
    remainders = {q[k] for q in common['fused_range_interfaces'] for k in ['remainder','slack']}
    require(len(remainders) == 16 and remainders<=retained, 'all sixteen remainder/slack guards retained')
    occurrences = {str(v):[i for i,row in enumerate(raw['rows']) if v in variables(row['terms'])] for v in sorted(missing)}
    for v in missing-OUTPUTS:
        require(all(i<643 for i in occurrences[str(v)]), 'quotient/intermediate has no hidden private or frame export')
    negative_controls = 0
    positive_controls = 0
    identity_controls = 0
    for W in range(4,13):
        A = W**W+1
        for n in range(3,W):
            T = 2*A*n-n*n-1
            require(T>A and (W-1)**W+1<W**W, 'unbounded lemma bound diagnostics')
            X,Y = 1,0
            for k in range(1,W):
                X,Y = A*X+(A*A-1)*Y, X+A*Y
                power = n**k
                require((X-(A-n)*Y-power)%T == 0, 'positive Pell polynomial power identity')
                require(((-X-(A-n)*Y)*power+1)%T == 0, 'negative abscissa unit identity')
                identity_controls += 1
                for m in range(1-W,W):
                    require(m*power+1 != 0 and abs(m*power+1)<T, 'signed nonzero negative-orientation residue')
                    require((-X-(A-n)*Y-m)%T != 0, 'negative abscissa impossible for every signed small output')
                    negative_controls += 1
                    if (X-(A-n)*Y-m)%T == 0:
                        require(m==power and m>0, 'positive orientation restores exact positive output')
                        positive_controls += 1
    result = {'status':'PASS','optimized_python':bool(sys.flags.optimize),'source_pins':PINS,'deleted_quotient_signs':sorted(QUOTIENTS),'missing_sign_coordinates':EXPECTED,'remaining_prefix_coordinates':len(known),'inherited_strict_steps_checked':len(strict_rows),'strict_steps_skipped':[],'bound_targets_checked':7,'seed_alias_sets_checked':15,'positive_ordinate_slacks':[s['aliases']['YminusK'] for s in relevant_seeds],'affected_power_calls':affected,'retained_remainder_slack_guards':sorted(remainders),'complete_source_occurrences':occurrences,'signed_negative_orientation_controls':negative_controls,'positive_output_controls':positive_controls,'pell_modular_identity_controls':identity_controls,'audit_sha256':digest(Path(__file__)),'lemma_sha256':digest(HERE/'PEER_SIGNED_OUTPUT.md'),'new_frame_or_full_prefix_replay_claimed':False,'projected_metrics_claimed':False,'builder_optimizer_archive_program_or_lean_run':False,'scope':'Independent strict dependency audit against frozen source and signed-output diagnostics. Unbounded lemma in PEER_SIGNED_OUTPUT.md; new whole-source/frame binding and full retained-prefix replay remain separate.'}
    content = json.dumps(result,indent=2,sort_keys=True)+'\n'
    if args.output.exists():
        require(args.output.read_text()==content,'refuse changed receipt overwrite')
    else:
        args.output.write_text(content)
    print(content,end='')


if __name__ == '__main__':
    main()
