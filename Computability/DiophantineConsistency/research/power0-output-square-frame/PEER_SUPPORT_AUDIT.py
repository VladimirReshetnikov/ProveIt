#!/usr/bin/env python3
"""Independent frozen64 dependency and actual call8 support-interface audit."""
import argparse
from hashlib import sha256
import json
from pathlib import Path
import sys

HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]
BASE=ROOT/'research/squared-range-frame-source-prototype'
PINS={
 'research/squared-range-frame-source-prototype/MANIFEST.json':'63ac958f76364edd07e8a68150d4781c0473ae6b9b8e554b1c6b46baca4ca81b',
 'research/squared-range-frame-source-prototype/source/raw_builder.json':'2d91052f7b2efd282900da4a04890a435f27423d5f28abb7aedfd2112d3b9789',
 'research/range-output-square-frame/MANIFEST.json':'49d6911ca3ba46204de8a559e18c351154075aee4e13562398e083fce12189b7',
 'research/range-output-square-frame/CERTIFICATE.json':'a3259f4856df00152c26315f20d5d66e0e4d412d3564c85524224dde4ec8fe43',
 'research/main-root-and-modulus-signs/CERTIFICATE.json':'96097a2984ab34468413c32898af70ee01c96d35470aaacc773654aca1140970',
}


def need(ok,why):
    if not ok:raise ValueError(why)


def load(path):return json.loads(path.read_bytes())
def digest(path):return sha256(path.read_bytes()).hexdigest()
def variables(terms):return {v for c,m in terms for v in m}


def poly(terms):
    out={}
    for c,m in terms:
        k=tuple(sorted(m));out[k]=out.get(k,0)+c
    return {m:c for m,c in out.items() if c}


def add(a,b):
    out=dict(a)
    for m,c in b.items():out[m]=out.get(m,0)+c
    return {m:c for m,c in out.items() if c}


def mul(a,b):
    out={}
    for m,c in a.items():
        for n,d in b.items():
            k=tuple(sorted(m+n));out[k]=out.get(k,0)+c*d
    return {m:c for m,c in out.items() if c}


def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--output',required=True,type=Path);args=ap.parse_args()
    for name,h in PINS.items():need(digest(ROOT/name)==h,'complete frozen dependency '+name)
    raw=load(BASE/'source/raw_builder.json');parent=load(BASE/'raw/parent.json');domain=load(BASE/'raw/domain.json')
    for name,h in load(BASE/'MANIFEST.json')['files'].items():need(digest(BASE/name)==h,'entire frozen64 member '+name)
    prior=load(ROOT/'research/main-root-and-modulus-signs/CERTIFICATE.json');old64=load(ROOT/'research/range-output-square-frame/CERTIFICATE.json')
    occurrences=[i for i,row in enumerate(raw['rows']) if 6 in variables(row['terms'])]
    need(occurrences==[2,649,1135],'complete raw6 source occurrences')
    need(raw['rows'][2]==dict(gate=7,label='multiplication',terms=[[-1,[6,6]],[1,[7]]]),'existing unconditional square')
    missing=set(old64['prefix_missing32'])|{6}
    signs=[s for stage in prior['prefix_proof']['five_stages'] for s in stage['preceding_sign_steps']]+prior['prefix_proof']['final_sign_steps']
    require7=[s for s in signs if s['variable']==7]
    need(len(require7)==1 and require7[0]['dependencies']==[] and poly(require7[0]['rhs'])==poly([[1,[6,6]]]),'square7 has no odd dependency on raw6')
    for original in signs:
        s=dict(original,**old64['changed_sign_steps'].get(str(original['variable']),{}))
        if set(s.get('dependencies',[]))&missing:need(s['variable'] in missing,'no additional missing descendants')
    strict_count=0
    for s in prior['positive_prefix']['steps']:
        if s['variable'] in {105,137}:continue
        deps=variables(raw['rows'][s['row']]['terms'])-{s['variable']}
        need(not(deps&missing),'all strict RHS dependencies survive');strict_count+=1
    need(strict_count==429,'all429 strict steps')
    bounds=prior['prefix_proof']['preliminary_t_n_bounds']+prior['prefix_proof']['five_stages']
    for s in bounds:need(not((variables(s['factor'])|variables(s['rhs']))&missing),'all bound factor/target dependencies survive')
    for seed in prior['seeds']:need(not(set(seed['aliases'].values())&missing),'all fifteen seed alias sets survive')
    retained=set(old64['retained_original_guard_indices'])-{6}
    need({549,550,562,563,694}<=retained,'actual support-output and initialA direct guard premises retained')
    call8=prior['power_calls'][8];call0=prior['power_calls'][0]
    need({k:call8[k] for k in ['base','exponent','output','X','Y','modulus','quotient']}==dict(base=530,exponent=4,output=547,X=670,Y=671,modulus=810,quotient=851),'complete actual call8 aliases')
    need([call0[k] for k in ['exponent','X','Y']]==[call8[k] for k in ['exponent','X','Y']],'exact same t main pair')
    rows=[poly(r['terms']) for r in raw['rows']]
    identities=0
    def collect(cut,target):
        nonlocal identities
        out={}
        for item in cut['row_combination']:out=add(out,mul(poly(item['multiplier']),rows[item['row']]))
        need(out==poly(target),'complete actual support polynomial ideal');identities+=1
    collect(old64['unchanged_local_cuts']['choose1_remainder'],[[1,[547]],[-1,[549]],[-1,[550]],[-1,[]]])
    for call in [call8,call0]:
        collect(call['cut'],[[1,[call['X']]],[-1,[644,call['Y']]],[1,[call['base'],call['Y']]],[-1,[call['output']]],[-1,[call['modulus'],call['quotient']]]])
    controls=0;n2controls=0
    for W in range(4,12):
        A=W**W+1
        for n in range(2,W):
            T=2*A*n-n*n-1;need(T>A,'positive base2 modulus bound')
            X,Y=1,0
            for k in range(1,W):
                X,Y=A*X+(A*A-1)*Y,X+A*Y
                for m in range(1-W,W):
                    actual=(X-(A-n)*Y-m)%T==0
                    need(actual==(m==n**k),'fully positive t-pair restores exact signed output')
                    controls+=1;n2controls+=n==2
    result=dict(status='PASS',optimized_python=bool(sys.flags.optimize),source_pins=PINS,raw6_occurrences=occurrences,proposed_only_frame_row=1135,existing_square_port=7,early_prefix_coordinates=608,additional_delayed_sign_steps=0,strict_steps_checked=strict_count,bound_targets_checked=len(bounds),seed_alias_sets_checked=15,actual_support_call=8,support_output_guard_premises=[549,550],initial_A_modulus_guard=694,complete_source_identities=identities,signed_positive_pair_controls=controls,signed_base2_controls=n2controls,new_basic_source_or_whole_theorem_approved=False,projected_metrics_claimed=False,audit_sha256=digest(Path(__file__)),proof_sha256=digest(HERE/'PEER_SUPPORT.md'),scope='Independent prospective raw6-only source dependency/support audit. Actual new source binding and full ordinary proof remain separate.')
    text=json.dumps(result,indent=2,sort_keys=True)+'\n'
    if args.output.exists():need(args.output.read_text()==text,'refuse changed receipt overwrite')
    else:args.output.write_text(text)
    print(text,end='')


if __name__=='__main__':main()
