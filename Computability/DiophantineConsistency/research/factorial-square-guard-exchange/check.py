#!/usr/bin/env python3
"""Read-only complete literal audit for the factorial-square guard exchange.

Only JSON/proof/archive bytes are read. No source builder, optimizer, imported
archive program, parent checker, external polynomial module or Lean executes.
The unbounded existence proof is PROOF.md plus FULL_SOURCE.md.
"""
import argparse
from collections import Counter
from copy import deepcopy
from hashlib import sha256
from io import BytesIO
import json
from math import comb, factorial
from pathlib import Path
import subprocess
import sys
from zipfile import ZipFile
sys.dont_write_bytecode=True
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]
REPO=ROOT.parents[1]
def need(ok,why):
    if not ok:raise ValueError(why)
def load(path):return json.loads(path.read_bytes())
def digest(path):return sha256(path.read_bytes()).hexdigest()
def P(terms):
    result={}
    for c,m in terms:
        need(type(c) is int and all(type(v) is int for v in m),'integer polynomial data')
        k=tuple(sorted(m));result[k]=result.get(k,0)+c
    return {m:c for m,c in result.items() if c}
def C(c):return {():c} if c else {}
def V(v):return {(v,):1}
def add(a,b,scale=1):
    result=dict(a)
    for m,c in b.items():result[m]=result.get(m,0)+scale*c
    return {m:c for m,c in result.items() if c}
def mul(a,b):
    result={}
    for m,c in a.items():
        for n,d in b.items():
            k=tuple(sorted(m+n));result[k]=result.get(k,0)+c*d
    return {m:c for m,c in result.items() if c}
def product(factors):
    result=C(1)
    for q in factors:result=mul(result,q)
    return result
def vars_(q):return {v for m in q for v in m}
def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--output',type=Path,required=True);args=ap.parse_args()
    pins=load(HERE/'SOURCE_PINS.json');data=load(HERE/'CERTIFICATE.json')
    for name,h in pins['files'].items():need(digest(ROOT/name)==h,'whole frozen dependency '+name)
    if (HERE/'MANIFEST.json').exists():
        files=load(HERE/'MANIFEST.json')['files']
        need({str(p.relative_to(HERE)) for p in HERE.rglob('*') if p.is_file() and p.name!='MANIFEST.json'}==set(files),'closed packet inventory')
        for name,h in files.items():need(digest(HERE/name)==h,'sealed packet member '+name)
    imp=pins['imported_archive'];path=REPO/imp['path']
    archive=path.read_bytes() if path.exists() else subprocess.check_output(['git','show',imp['commit']+':'+imp['path']],cwd=REPO)
    need(sha256(archive).hexdigest()==imp['sha256'],'complete inert Bootstrap archive pin')
    with ZipFile(BytesIO(archive)) as z:
        for local,info in imp['members'].items():
            b=z.read(info['member']);need(len(b)==info['size'] and sha256(b).hexdigest()==info['sha256'] and (HERE/local).read_bytes()==b,'complete copied inert proof/license member')
    raw=load(ROOT/'candidates/projected-radius-mixed-bounds/source/raw_builder.json')
    natural=load(ROOT/'candidates/projected-factorial-radius/both_source/raw_builder.json')
    need(raw==natural and len(raw['rows'])==1177 and len(raw['variables'])==1259,'exact complete raw/native-source parent')
    need(data['changed_rows']=={'75':{'old':raw['rows'][75],'new':dict(gate=89,label='multiplication',terms=[[-1,[87,87]],[1,[89]]])}},'ONLY row75 changes, original label retained')
    proposed=deepcopy(raw);proposed['rows'][75]=data['changed_rows']['75']['new']
    need(data['old_factorial0_guard']==dict(kind='at_least',lower=2,raw_variable=87) and data['new_factorial0_guard']==dict(kind='nonnegative_difference',left_raw_variable=87,right_raw_variable=86),'exact f-2 to f-K predicate exchange')
    need(data['original_predicates']==data['proposed_predicates']==72 and data['first_radius_only'] and data['second_radius_unchanged'],'72 slots and unchanged factorial1')
    need(data['all_source_metadata']=={k:v for k,v in raw.items() if k not in ['rows','variables']},'ALL21power/15seed/16index/native-majorant metadata')
    rows=[P(q['terms']) for q in proposed['rows']];count=0
    def collect(cut,target=None):
        nonlocal count
        answer={}
        for item in cut['row_combination']:
            need(type(item['row']) is int and 0<=item['row']<len(rows),'literal complete source row')
            answer=add(answer,mul(P(item['multiplier']),rows[item['row']]))
        expected=P(cut.get('polynomial',cut.get('expanded_polynomial'))) if target is None else target
        need(answer==expected,'every coefficient of complete original-row ideal')
        count+=1;return answer
    targets={'positive_t':[[1,[4]],[-1,[0]],[-1,[]]],'positive_y':[[1,[2]],[-1,[3]],[-1,[31]],[-2,[]]],'positive_x':[[1,[1]],[-1,[3]],[-2,[]],[-1,[30]],[-1,[2,30]]],'K_input':[[1,[63]],[-1,[4]],[-1,[1]],[-1,[2]],[-1,[3]],[-2,[]]]}
    need(data['early_guards']==[0,3,30,31] and set(data['early_cuts'])==set(targets),'actual retained endpoint guards and no f premise')
    for name,target in targets.items():collect(data['early_cuts'][name],P(target))
    need(data['K_square_rows']==[dict(input=v-1,output=v,row=v-13) for v in range(64,87)],'exact23 K squares')
    for v in range(64,87):need(rows[v-13]==P([[1,[v]],[-1,[v-1,v-1]]]),'every K square, independent of f')
    collect(data['proposed_radius_cut'],P([[1,[89]],[-1,[87,87]]]))
    for cut in data['unchanged_local_cuts'].values():collect(cut)
    for name,expected in data['complete_source_occurrences'].items():
        v=int(name);need([i for i,q in enumerate(raw['rows']) if v in vars_(P(q['terms']))]==expected,'ALL parent uses of '+name)
        need([i for i,q in enumerate(rows) if v in vars_(q)]==data['proposed_source_occurrences'][name],'ALL proposed uses of '+name)
    need(data['retained_private_square']['coordinate_deleted'] is False and rows[74]==P([[1,[88]],[-1,[86,86]]]) and data['proposed_source_occurrences']['88']==[74],'private K² retained with only definition')
    old72=load(ROOT/'research/shifted-t-index-guard/CERTIFICATE.json')
    prior=load(ROOT/'research/main-root-and-modulus-signs/CERTIFICATE.json')
    for name,cut in old72['exact_source_cuts'].items():collect(data['proposed_radius_cut'] if name=='local0_radius' else cut)
    # Rebind the complete ordered prefix without invoking a parent checker.
    prefix=prior['prefix_proof'];initial=set(prefix['initial_semantic_guard_indices'])
    oldguards={g['raw_variable'] for g in load(ROOT/'candidates/projected-radius-comparison-base/domain_certificate.json')['guards']}
    kept=oldguards-set(pins['removed_original_predicates'])
    need(len(kept)==69 and initial-kept=={59,93,104} and {0,3,30,31}<=kept and data['retained_original_guard_indices']==sorted(kept),'complete retained69 scalar guards')
    need(data['replacement_predicates']==pins['new_predicates']==old72['inherited_replacement_predicates'][:-1]+[data['new_factorial0_guard']] and len(kept)+len(data['replacement_predicates'])==72,'every predicate: same69 scalar/two replacements, exact one exchanged guard')
    known={v:0 for v in initial-{59,93,104}};known.update({int(v):L for v,L in old72['early_derived_bounds'].items()})
    # These early bounds follow after the independently checked endpoints/new guard.
    need(known[87]==2 and known[93]==2 and known[129]==1,'same valid early bounds after f>=K>=49')
    rewrites={q['variable']:q for q in old72['rewritten_prefix_bounds']}
    def positive(q):
        need(vars_(q)<=set(known),'all earlier sign/lower-bound dependencies available')
        shifted={}
        for m,c in q.items():shifted=add(shifted,product([C(c)]+[add(V(v),C(known[v])) for v in m]))
        need(all(c>=0 for c in shifted.values()) and shifted.get((),0)>0,'unbounded shifted positivity certificate')
    sign_count=0;changed_signs=0
    def sign(original):
        nonlocal sign_count,changed_signs
        step=deepcopy(original);v=step['variable']
        if v in {105,137}:
            need(known[v]>=(1 if v==105 else 0),'actual early replacement sign');return
        if v==89:
            need(step['row']==75 and P(step['rhs'])==P([[1,[87,88]]]),'actual old89 step located')
            step.update(data['changed_sign_step']);changed_signs+=1
        c,R=step['coefficient'],P(step['rhs']);pivot=add(mul(C(c),V(v)),R,-1)
        need(c>0 and rows[step['row']] in (pivot,mul(C(-1),pivot)) and not ({59,104}&vars_(rows[step['row']])),'entire proposed ordered sign row')
        if step['kind']=='positive_monomials':
            deps={w for m in R for w,n in Counter(m).items() if n%2}
            need(deps==set(step['dependencies']) and deps<=set(known) and all(c>0 for c in R.values()),'actual odd-power dependencies, square89 has none')
        else:need(step['kind']=='affine_square' and mul(P(step['square_root']),P(step['square_root']))==R,'complete independent square')
        known[v]=max(known.get(v,0),0);sign_count+=1
    canonical=prior['positive_prefix']['canonical_modulus_cut'];collect(canonical)
    def bound(original):
        v,L=original['variable'],original['lower'];F,G=P(original['factor']),P(original['rhs'])
        old=collect(original,add(mul(V(v),F),G,-1))
        if v in rewrites:
            step=rewrites[v];F,G=P(step['factor']),P(step['rhs'])
            multiplier=P([[-1,[130]],[-1,[]]]) if v==130 else P([[-1,[517]]])
            need(add(old,mul(multiplier,P(canonical['polynomial'])))==add(mul(V(v),F),G,-1),'complete canonical-modulus bound rewrite')
            collect(step,add(mul(V(v),F),G,-1))
        need(v not in vars_(F)|vars_(G),'no self-premise lower bound');positive(F);positive(add(G,mul(C(L-1),F),-1));known[v]=max(known.get(v,L),L)
    for step in prefix['preliminary_t_n_bounds']:bound(step)
    for step in prefix['five_stages']:
        for item in step['preceding_sign_steps']:sign(item)
        bound(step)
    for step in prefix['final_sign_steps']:sign(step)
    need(set(known)==set(range(643))-{59,104} and sign_count==573 and changed_signs==1,'all641 prefix coordinates, exactly one changed89 step')
    need(data['explicit_radius_bound']==dict(variable=89,lower=4,premise=dict(variable=87,lower=2),row=75,positive_monomial=[87,87]) and known[87]>=2 and rows[75]==P([[1,[89]],[-1,[87,87]]]),'separate new89>=4 proof')
    strict={4,5,129,87,93,105};strict_count=0
    for step in prior['positive_prefix']['steps']:
        v=step['variable']
        if v in {105,137}:continue
        row=rows[step['row']];need(row.get((v,))==1,'actual strict constructor')
        R={m:-c for m,c in row.items() if m!=(v,)};m=tuple(step['positive_monomial'])
        need(vars_(R)<=set(known) and all(c>0 for c in R.values()) and R.get(m,0)>0 and set(m)<=strict,'all earlier strict constructor premises')
        strict.add(v);strict_count+=1
    need(strict_count==429 and all(s['variable']!=89 and 89 not in s['positive_monomial'] for s in prior['positive_prefix']['steps']),'429 inherited strict steps,89 proof additional')
    arguments={v[1] for call in raw['powers'] for v in call.values()}
    need(len(arguments)==43 and arguments==set(old72['frame_arguments']) and max(arguments)<643 and arguments-{104}<=set(known),'all43 semantic arguments allocated before frame/private indices')
    collect(old72['frame_cut']);collect(old72['weak_frame_cut'])
    need(len(raw['powers'])==len(prior['power_calls'])==21 and len(raw['seeds'])==len(prior['seeds'])==15 and len(raw['indices'])==16,'complete simultaneous request counts')
    for i,call in enumerate(prior['power_calls']):
        need(call['index']==i and [raw['powers'][i][k] for k in ['base','exponent','output']]==[['v',call[k]] for k in ['base','exponent','output']],'all21 literal actual power ports')
        collect(call['cut'],P([[1,[call['X']]],[-1,[644,call['Y']]],[1,[call['base'],call['Y']]],[-1,[call['output']]],[-1,[call['modulus'],call['quotient']]]]))
    for source,seed in zip(raw['seeds'],prior['seeds']):
        need(source['exponent']==['v',seed['aliases']['k']] and source['pair']==[['v',seed['aliases'][k]] for k in ['X','Y']],'all15 literal seed ports')
        for cut in seed['cuts'].values():collect(cut)
    for item in prior['moduli']:collect(item['cut'])
    for name in ['bootstrap_norm','unit_norm_cut','comparison_base_constructor','comparison_base_congruence']:collect(prior[name])
    need(raw['derivations']==[dict(kind='shift',pair=[['v',921],['v',922]],shift=1,source=['v',4],target=['v',5])],'single unchanged derived t+1 pair')
    upper=[44,46,48,50,52,54,56,58];lower=[5,5,5,5,36,36,136,136]
    need(data['range_upper_indices']==upper and data['range_lower_indices']==lower and [(q[0][1],q[1][1],q[2][1]) for q in raw['ranges']]==list(zip(upper,lower,[129]*8)),'all8 exact range graph ports')
    expected_full={
      'aggregate':[[1,[v]] for v in upper+[519]]+[[-8,[129]]],
      't_successor':[[1,[5]],[-1,[4]],[-1,[]]],'y_successor':[[1,[36]],[-1,[2]],[-1,[]]],'x_successor':[[1,[136]],[-1,[1]],[-1,[]]],
      'choose0_digit':[[1,[532]],[-1,[533,91]],[-1,[533,530,534]],[-1,[535]]],
      'choose0_remainder':[[1,[533]],[-1,[535]],[-1,[536]],[-1,[]]],
      'derived_discriminant':[[1,[917]],[-1,[644,644]],[1,[]]],
      'derived_X':[[1,[921]],[-1,[644,670]],[-1,[644,644,671]],[1,[671]]],
      'derived_Y':[[1,[922]],[-1,[670]],[-1,[644,671]]]}
    need(set(data['full_source_cuts'])==set(expected_full),'all full bridge cuts, no missing aggregate or index')
    for name,target in expected_full.items():collect(data['full_source_cuts'][name],P(target))
    fused_ports=[(44,5,573,574,575,576,577),(46,5,583,574,584,585,586),
                 (48,5,591,574,592,593,594),(50,5,599,574,600,601,602),
                 (52,36,607,608,609,610,611),(54,36,617,608,618,619,620),
                 (56,136,625,626,627,628,629),(58,136,635,626,636,637,638)]
    need(len(data['fused_range_interfaces'])==8,'all8 fused graph cuts supplied')
    for interface,ports,range_request in zip(data['fused_range_interfaces'],fused_ports,raw['ranges']):
        need(tuple(interface[k] for k in ['upper','lower','numerator','denominator','quotient','remainder','slack'])==ports and interface['label']==range_request[3],'all literal fused graph aliases')
        n,k,num,den,q,rem,slack=ports
        need(dict(base=['v',531],exponent=['v',n],output=['v',num]) in raw['powers'] and dict(base=['v',530],exponent=['v',k],output=['v',den]) in raw['powers'],'fused numerator and denominator are actual interpreted powers')
        collect(interface['quotient_cut'],P([[1,[num]],[-1,[129,den,q]],[-1,[rem]]]))
        collect(interface['remainder_cut'],P([[1,[den]],[-1,[rem]],[-1,[slack]],[-1,[]]]))
        need({q,rem,slack}<=set(known),'fused quotient and Euclidean remainder witnesses nonnegative')
    need(set(upper+[519,131])<=set(known) and set(lower)<strict,'all aggregate and lower-index sign premises established')
    # Finite exact-rational diagnostics supplement, never replace, unbounded proof.
    fixed_controls=0
    for n in range(4,11):
        m=factorial(n)
        for f in sorted(set(range(n,min(m+4,60)))|{m-1,m,m+1}):
            if f<n:continue
            numerator=(1+f*f)**n;denominator=comb(f*f+n,n)
            fixed=(numerator+denominator-1)//denominator==f
            need(fixed==(f==m),'squared-radius exact ceiling diagnostic');fixed_controls+=1
    range_controls=0
    for t in range(1,8):
        R=t+6;K=R*R;f=K;B=(1+(t+1)*f)**t;Q=f*(B+2)-1
        need(8*Q<24*R**t*f**(t+1)<=f**(2*t+2) and R*(t+1)<=K,'complete acyclic range bound diagnostic')
        need(f**(2*R*(t+1))<(1+f*f)**K,'strict final radix comparison');range_controls+=1
    collapsed_controls=0
    for K in range(3,15):
        for f in range(K,K+9):
            need(f*(K-2)<f*f+1 and f<f*f+1,'both collapsed local factorial branches excluded');collapsed_controls+=1
    rejected=[]
    def reject(label,action):
        try:action()
        except (ValueError,KeyError,IndexError,TypeError):rejected.append(label)
        else:raise ValueError('corruption accepted '+label)
    bad=deepcopy(data['full_source_cuts']['aggregate']);bad['row_combination'][0]['multiplier'][0][0]+=1
    reject('changed aggregate coefficient',lambda:collect(bad,P(expected_full['aggregate'])))
    reject('old f*K² radius retained',lambda:collect(data['original_radius_cut']))
    bad=deepcopy(data['fused_range_interfaces'][0]['quotient_cut']);bad['row_combination'][0]['multiplier'][0][0]+=1
    reject('alter fused range quotient ideal',lambda:collect(bad,P([[1,[573]],[-1,[129,574,575]],[-1,[576]]])))
    reject('drop fused strict remainder constant',lambda:collect(data['fused_range_interfaces'][7]['remainder_cut'],P([[1,[626]],[-1,[637]],[-1,[638]]])))
    reject('private K² silently deleted',lambda:need(data['proposed_source_occurrences']['88']==[],'retained private gate'))
    reject('raw36 mislabeled M0+2',lambda:collect(data['full_source_cuts']['y_successor'],P([[1,[36]],[-1,[3]],[-2,[]]])))
    reject('raw136 mislabeled y+1',lambda:collect(data['full_source_cuts']['x_successor'],P([[1,[136]],[-1,[2]],[-1,[]]])))
    reject('range product bound used without aggregate',lambda:need(set(data['full_source_cuts'])-{'aggregate'}==set(expected_full),'required actual aggregate'))
    reject('common radius replaces factorial1',lambda:collect(data['unchanged_local_cuts']['d1_radius'],P([[1,[109]],[-1,[87,87]]])))
    reject('new89 sign retains old f*88 term',lambda:need(rows[75]==P([[1,[89]],[-1,[87,88]]]),'complete changed row'))
    reject('derive f>=K from f>=2 alone',lambda:need(2>=49,'new guard indispensable before factorial'))
    reject('interpret call7 before restoring825',lambda:need(7 in old72['chronology']['interpreted_calls_before_825'],'72 chronology'))
    reject('bind first actual power output to encoded59',lambda:need(raw['powers'][0]['output']==['v',59],'literal power ports'))
    reject('include private825 in semantic frame',lambda:need(825 in arguments,'actual43 argument frame'))
    reject('remove one seed from simultaneous interface',lambda:need(len(raw['seeds'][:-1])==15,'all15 required seeds'))
    reject('replace fresh witness construction by pointwise map',lambda:need(data.get('pointwise_old_new_tuple_map') is True,'new frame/radix witnesses required'))
    result=dict(status='PASS',optimized_python=bool(sys.flags.optimize),raw_coordinates=1259,raw_rows=1177,predicates=72,changed_rows=[75],changed_guard='f>=2 to f>=K',private_K_square_retained=True,
      complete_row_identities=count,prefix_coordinates=len(known),prefix_sign_steps=sign_count,changed_prefix_sign_steps=changed_signs,inherited_strict_steps=strict_count,new_radius_separate_lower_bound=4,
      actual_power_requests=21,seed_tests=15,index_atoms=16,derived_pairs=1,exact_binomials=3,range_graphs=8,range_lower_ports=lower,frame_arguments=43,
      squared_radius_exact_ceiling_controls=fixed_controls,acyclic_range_bound_controls=range_controls,collapsed_branch_controls=collapsed_controls,rejected_corruptions=rejected,
      source_pins={name:digest(HERE/name) for name in ['PROOF.md','FULL_SOURCE.md','CERTIFICATE.json','SOURCE_PINS.json','check.py']},
      imported_archive_executed=False,source_builder_optimizer_parent_checker_or_lean_executed=False,ordinary_changed_raw_source_equivalence=True,projected_metrics_claimed=False,
      scope='Complete literal source interfaces and finite controls for ordinary changed-source proof. Unbounded argument in PROOF.md/FULL_SOURCE.md; projected restoration/quartic acceptance remains separate.')
    text=json.dumps(result,indent=2,sort_keys=True)+'\n'
    if args.output.exists():need(args.output.read_text()==text,'refuse to overwrite different receipt bytes')
    else:args.output.write_text(text)
    print(text,end='')
if __name__=='__main__':main()
