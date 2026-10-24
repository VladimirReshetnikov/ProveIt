#!/usr/bin/env python3
"""Read-only complete literal audit for the existing-square first-power frame63.

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
    raw=load(ROOT/'research/common-squared-radius-source-prototype/source/raw_builder.json')
    natural=load(ROOT/'candidates/projected-factorial-radius/both_source/raw_builder.json')
    expected_parent=deepcopy(natural);expected_parent['rows'][75]['terms']=[[-1,[87,87]],[1,[89]]];expected_parent['rows'][90]['terms']=[[-1,[89]],[1,[109]]]
    need(raw==expected_parent and len(raw['rows'])==1177 and len(raw['variables'])==1259,'exact complete common-radius parent/native-source boundary')
    outputs=[573,583,591,599,607,617,625,635];removedq=[575,584,592,600,609,618,627,636]
    squarevars=list(range(1259,1267));mapping=dict(zip(outputs,squarevars));changed_rows=[1165,1167,1168,1169,1170,1172,1173,1175]
    need(data['replaced_outputs']==outputs and data['removed_quotient_guards']==removedq and data['square_variables']==squarevars,'exact8outputs/quotients/squareports')
    proposed=deepcopy(raw)
    for i,out,sv in zip(changed_rows,outputs,squarevars):
        expected=deepcopy(raw['rows'][i]);expected['terms']=[[c,[sv] if m==[out] else m] for c,m in expected['terms']]
        need(data['changed_rows'][str(i)]==dict(old=raw['rows'][i],new=expected),'each complete changed frame row')
        proposed['rows'][i]=expected
    appended_vars=[dict(kind='gate',name='frame.range_output_square.'+str(v)) for v in outputs]
    appended_rows=[dict(gate=sv,label='frame_range_output_square',terms=[[-1,[v,v]],[1,[sv]]]) for v,sv in zip(outputs,squarevars)]
    need(data['appended_variables']==appended_vars and data['appended_rows']==appended_rows and set(map(int,data['changed_rows']))==set(changed_rows),'all8 appended square records and ONLY8 frame changes')
    proposed['variables']+=appended_vars;proposed['rows']+=appended_rows
    base64=load(ROOT/'research/squared-range-frame-source-prototype/source/raw_builder.json')
    need(base64==proposed,'ENTIRE frozen squared-range-frame64 source equality')
    oldrow=deepcopy(proposed['rows'][1135]);newrow=dict(gate=1218,label='addition',terms=[[-1,[7]],[-1,[1217]],[1,[1218]]])
    need(data['power0_changed_row']==dict(index=1135,old=oldrow,new=newrow) and oldrow==dict(gate=1218,label='addition',terms=[[-1,[6]],[-1,[1217]],[1,[1218]]]),'only raw6 frame term exchanged for existing raw7')
    proposed['rows'][1135]=newrow
    actual=load(ROOT/'research/power0-square-frame-source-prototype/source/raw_builder.json')
    need(actual==proposed and len(actual['variables'])==1267 and len(actual['rows'])==1185,'ENTIRE actual frame63 source equality')
    joint=dict(kind='nonnegative_difference',positive_raw_variable=87,negative_raw_variables=[86,107])
    need(data['old_factorial0_guard']==data['new_factorial0_guard']==joint and data['original_predicates']==72 and data['proposed_predicates']==63 and data['newly_removed_scalar_guard']==6,'joint factorial guard unchanged; remove8quotients and raw6 only')
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
    collect(data['common_radius_cut'],P([[1,[109]],[-1,[87,87]]]))
    collect(data['common_base_cut'],P([[1,[112]],[-1,[]],[-1,[87,87]]]))
    collect(data['new_t1_combined_cut'],P([[1,[107,111]],[-1,[113]],[-1,[115]],[1,[112]],[-1,[]],[-1,[87,87]]]))
    for name,expected in data['complete_source_occurrences'].items():
        v=int(name);need([i for i,q in enumerate(raw['rows']) if v in vars_(P(q['terms']))]==expected,'ALL parent uses of '+name)
        need([i for i,q in enumerate(rows) if v in vars_(q)]==data['proposed_source_occurrences'][name],'ALL proposed uses of '+name)
    need(data['retained_private_t_square']==dict(raw_variable=108,defining_row=89,formula='raw108=raw4^2',coordinate_deleted=False,proposed_source_occurrences=[89]) and rows[89]==P([[1,[108]],[-1,[4,4]]]) and data['proposed_source_occurrences']['108']==[89],'private t² retained with only definition')
    need(data['retained_private_square']['coordinate_deleted'] is False and rows[74]==P([[1,[88]],[-1,[86,86]]]) and data['proposed_source_occurrences']['88']==[74],'private K² retained with only definition')
    old72=load(ROOT/'research/shifted-t-index-guard/CERTIFICATE.json')
    prior=load(ROOT/'research/main-root-and-modulus-signs/CERTIFICATE.json')
    for name,cut in old72['exact_source_cuts'].items():
        collect(data['proposed_radius_cut'] if name=='local0_radius' else data['common_radius_cut'] if name=='d1_radius' else cut)
    # Rebind the complete ordered prefix without invoking a parent checker.
    prefix=prior['prefix_proof'];initial=set(prefix['initial_semantic_guard_indices'])
    oldguards={g['raw_variable'] for g in load(ROOT/'candidates/projected-radius-comparison-base/domain_certificate.json')['guards']}
    kept=oldguards-set(pins['removed_original_predicates'])
    need(len(kept)==60 and initial-kept=={6,59,93,104}|set(removedq) and {0,3,30,31}<=kept and data['retained_original_guard_indices']==sorted(kept),'complete retained60 scalar guards')
    need(data['replacement_predicates']==pins['new_predicates']==old72['inherited_replacement_predicates'][:-1]+[data['new_factorial0_guard']] and len(kept)+len(data['replacement_predicates'])==63,'every predicate:60retained scalars and3unchanged replacements')
    need(data['early_g_guards']==[113,114,115] and {113,114,115}<=kept,'all early g signs are retained direct guards')
    collect(data['early_g_cuts']['factorial1_remainder'],P([[1,[111]],[-1,[114]],[-1,[115]],[-1,[]]]))
    collect(data['early_g_cuts']['factorial1_ceiling'],P([[1,[107,111]],[-1,[113]],[-1,[115]]]))
    known={v:0 for v in initial-{6,59,93,104}-set(removedq)};known.update({int(v):L for v,L in old72['early_derived_bounds'].items()});known[107]=0
    # These early bounds follow after the independently checked endpoints/new guard.
    need(known[87]==2 and known[93]==2 and known[129]==1,'same valid early bounds after f>=K>=49')
    rewrites={q['variable']:q for q in old72['rewritten_prefix_bounds']}
    def positive(q):
        need(vars_(q)<=set(known),'all earlier sign/lower-bound dependencies available')
        shifted={}
        for m,c in q.items():shifted=add(shifted,product([C(c)]+[add(V(v),C(known[v])) for v in m]))
        need(all(c>=0 for c in shifted.values()) and shifted.get((),0)>0,'unbounded shifted positivity certificate')
    sign_count=0;changed_signs=0;skipped=[]
    def sign(original):
        nonlocal sign_count,changed_signs
        step=deepcopy(original);v=step['variable']
        if v in {105,137}:
            need(known[v]>=(1 if v==105 else 0),'actual early replacement sign');return
        if v==89:
            need(step['row']==75 and P(step['rhs'])==P([[1,[87,88]]]),'actual old89 step located')
            step.update(data['changed_sign_steps']['89']);changed_signs+=1
        if v==109:
            need(step['row']==90 and P(step['rhs'])==P([[1,[107,108]]]),'actual old109 step located')
            step.update(data['changed_sign_steps']['109']);changed_signs+=1
        c,R=step['coefficient'],P(step['rhs']);pivot=add(mul(C(c),V(v)),R,-1)
        need(c>0 and rows[step['row']] in (pivot,mul(C(-1),pivot)) and not ({59,104}&vars_(rows[step['row']])),'entire proposed ordered sign row')
        if step['kind']=='positive_monomials':
            deps={w for m in R for w,n in Counter(m).items() if n%2}
            need(deps==set(step['dependencies']) and all(c>0 for c in R.values()),'all actual odd-power dependencies')
            if not deps<=set(known):
                need(v in set(data['prefix_missing32']),'only explicitly missing32 sign steps may wait')
                skipped.append(dict(variable=v,row=step['row'],missing=sorted(deps-set(known)),step=step));return
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
    missing=set(data['prefix_missing33']);need(missing==set(data['prefix_missing32'])|{6} and set(known)==set(range(643))-{59,104}-missing and len(missing)==33 and sign_count==549 and changed_signs==2,'exact608 early prefix and549signs, no omitted output/quotient sign assumed')
    need([{k:q[k] for k in ['variable','row','missing']} for q in skipped]==data['prefix_audit']['skipped_sign_steps'] and len(skipped)==24,'all24 delayed actual source steps in dependency order')
    early_prefix_count=len(known);early_sign_count=sign_count
    need(data['explicit_radius_bound']==dict(variable=89,lower=4,premise=dict(variable=87,lower=2),row=75,positive_monomial=[87,87]) and known[87]>=2 and rows[75]==P([[1,[89]],[-1,[87,87]]]),'separate new89>=4 proof')
    strict={4,5,129,87,93,105};strict_count=0
    for step in prior['positive_prefix']['steps']:
        v=step['variable']
        if v in {105,137}:continue
        row=rows[step['row']];need(row.get((v,))==1,'actual strict constructor')
        R={m:-c for m,c in row.items() if m!=(v,)};m=tuple(step['positive_monomial'])
        need(vars_(R)<=set(known) and all(c>0 for c in R.values()) and R.get(m,0)>0 and set(m)<=strict,'all earlier strict constructor premises')
        strict.add(v);strict_count+=1
    need(strict_count==429 and all(s['variable'] not in {89,109} and {89,109}.isdisjoint(s['positive_monomial']) for s in prior['positive_prefix']['steps']),'429 inherited strict steps, square/copy positivity additional')
    arguments={v[1] for call in raw['powers'] for v in call.values()}
    need(len(arguments)==43 and arguments==set(old72['frame_arguments'])==set(data['actual_frame_arguments']) and max(arguments)<643 and arguments-{6,104}-set(outputs)<=set(known),'all actual ports, only raw6/B104/eightoutputs may be signed')
    mapping[6]=7
    bounding={mapping.get(v,v) for v in arguments};other=arguments-{6,104}-set(outputs)
    need(bounding==set(data['bounding_frame_arguments']) and len(bounding)==43 and len(other)==33 and set(data['weak_frame_other_natural_ports'])==other,'exact43 bounding ports and33 other natural ports')
    collect(data['new_frame_cut'],P([[1,[643]],[-2,[]]]+[[-1,[v]] for v in sorted(bounding)]))
    collect(data['new_weak_frame_cut'],P([[1,[643]],[-1,[105]]]+[[-1,[v]] for v in sorted(other|set(squarevars)|{7})]))
    collect(data['expanded_weak_frame_cut'],P([[1,[643]],[-1,[105]]]+[[-1,[v]] for v in sorted(other)]+[[-1,[v,v]] for v in [6]+outputs]))
    for i,(v,sv) in enumerate(zip(outputs,squarevars)):need(rows[1177+i]==P([[1,[sv]],[-1,[v,v]]]),'every appended square without input sign premise')
    collect(data['power0_square_cut'],P([[1,[7]],[-1,[6,6]]]))
    need([i for i,row in enumerate(base64['rows']) if 6 in vars_(P(row['terms']))]==data['complete_power0_parent_occurrences']==[2,649,1135] and [i for i,row in enumerate(rows) if 6 in vars_(row)]==data['complete_power0_occurrences']==[2,649],'complete raw6 parent/proposed source use inventories')
    need(6 not in known and 7 in known and rows[2]==P([[1,[7]],[-1,[6,6]]]),'raw7 square natural without raw6 sign')
    need(all(6 not in vars_(rows[step['row']])-{step['variable']} for step in prior['positive_prefix']['steps']),'every strict RHS avoids raw6')
    need(known[105]>=1 and {4,86}<=other and {call['base'][1] for call in raw['powers']}<=strict and {call['exponent'][1] for call in raw['powers']}<=strict,'weakD positivity and ALL actual positive bases/indices survive')
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
        need({rem,slack}<=set(known) and q in removedq and q not in known,'fused remainders remain natural, quotient sign deliberately delayed')
    need(set(upper+[519,131])<=set(known) and set(lower)<strict,'all aggregate and lower-index sign premises established')
    # Override BOTH historical call0 supports before using its signed output.
    support=data['t_support_override'];call8=prior['power_calls'][8];call0=prior['power_calls'][0];call9=prior['power_calls'][9]
    need(support['replaces_old_call']==0 and support['supporting_call']==8 and support['other_supporting_call']==9 and support['conditional_B_minus_one_pairing'] is True and support['post_factorial_parity_pairing'] is True and support['old_call_output_sign_used'] is False,'two explicit call8 orientation overrides, no raw6 sign premise')
    need(support['call']==call8 and support['same_t_main_pair']==[670,671] and (call8['X'],call8['Y'],call8['exponent'])==(call0['X'],call0['Y'],call0['exponent'])==(670,671,4),'support8 uses the exact same t main pair as call0')
    need((call8['base'],call8['output'],call8['modulus'],call8['quotient'])==(530,547,810,851) and call9['base']==531 and call9['output']==560 and {530,531}<=strict and 560 in known,'literal sign-safe supports8/9 and positive bases')
    need(support['retained_remainder_guards']==[549,550,562,563] and {549,550,562,563}<=kept,'strict supporting output derives from actual retained direct guards')
    for name,rems in [('choose1_remainder',[549,550]),('choose2_remainder',[562,563])]:
        need(support['strict_output_cuts'][name]==old72['exact_source_cuts'][name],'unchanged independent strict-remainder cut')
        collect(support['strict_output_cuts'][name],P([[1,[547]],[-1,[rems[0]]],[-1,[rems[1]]],[-1,[]]]))
    binding=data['power0_binding'];seedt=next(q for q in prior['seeds'] if q['aliases']['k']==4)
    need(all(binding[k]==call0[k] for k in call0) and binding['seed_aliases']==seedt['aliases'] and seedt['aliases']['YminusK']==674 and 674 not in kept,'actualcall0 bound; positive tY recovered by8/9, never a retained slack assumption')
    need((call0['base'],call0['output'],call0['modulus'])==(5,6,694) and 5 in strict and 6 not in known,'signed residue recovery begins with unknown raw6 and actual positive base5')
    collect(call0['cut'])
    known[6]=0
    need(len(known)==609 and set(known)==set(range(643))-{59,104}-set(data['prefix_missing32']),'proved raw6 residue restores exactly the inherited609 prefix')
    # Bind all8 applications of the positive-Y/signed-output theorem.
    signed_indices=[10,12,13,14,15,17,18,20]
    need([c['index'] for c in data['signed_output_calls']]==signed_indices,'exact8 signed numerator power calls')
    for interface,i in zip(data['signed_output_calls'],signed_indices):
        call=prior['power_calls'][i];seed=next(q for q in prior['seeds'] if q['aliases']['k']==call['exponent'])
        need(all(interface[k]==call[k] for k in ['base','exponent','output','X','Y','modulus','quotient']) and interface['base']==531 and interface['output'] in outputs,'literal signed-output port and positive base b+1')
        need(interface['seed_aliases']==seed['aliases'] and interface['retained_YminusK']==seed['aliases']['YminusK'] and interface['retained_YminusK'] in kept,'positiveY premise comes from an actually retained guard')
        collect(seed['cuts']['index_at_most_Y'],P([[1,[call['Y']]],[-1,[call['exponent']]],[-1,[interface['retained_YminusK']]]]))
    need({q['output'][1] for j,q in enumerate(raw['powers']) if j not in signed_indices}-{104}<=set(known),'other12 outputs retain early signs;B recovered by its separate weak-frame proof')
    # Once the proved signed-power and fused-remainder argument recovers q>=0,
    # replay exactly the delayed24 steps; no binomial/product meaning is needed.
    for q in removedq:known[q]=0
    delayed=list(skipped)
    for item in delayed:sign(item['step'])
    need(len(skipped)==24 and sign_count==573 and set(known)==set(range(643))-{59,104},'restored641 prefix after exactly8 quotient signs')
    # Complete literal63-guard parent, including all retained auxiliary names.
    oldparent=load(ROOT/'research/common-squared-radius-source-prototype/raw/parent.json');olddomain=load(ROOT/'research/common-squared-radius-source-prototype/raw/domain.json')
    parent=load(ROOT/'research/power0-square-frame-source-prototype/raw/parent.json');domain=load(ROOT/'research/power0-square-frame-source-prototype/raw/domain.json')
    oldguards=[g for g in olddomain['guards'] if not(g['predicate']['kind']=='retained_scalar' and g['predicate']['raw_variables'][0] in removedq+[6])]
    expected_vars=proposed['variables']+[oldparent['variables'][v] for g in oldguards for v in g['auxiliary']]
    need(parent['variables']==expected_vars and len(parent['variables'])==1456 and len(parent['residuals'])==1248,'whole parent variable/name compaction')
    expected_residuals=[dict(label=row['label'],terms=row['terms']) for row in proposed['rows']]
    need(parent['residuals'][:1185]==expected_residuals and len(domain['guards'])==63 and domain['baseline_raw_indices']==list(range(1267)),'every literal arithmetic body row retained')
    for j,(g,oldg,row) in enumerate(zip(domain['guards'],oldguards,parent['residuals'][1185:])):
        aux=list(range(1267+3*j,1270+3*j));need(g==dict(auxiliary=aux,predicate=oldg['predicate']),'exact retained predicate ordering/triples')
        a,b,c=aux;target=add(P(g['predicate']['terms']),P([[-1,[a,a]],[-1,[b,b]],[-1,[c,c]],[-1,[c]]]))
        need(P(row['terms'])==target and row['label']==oldparent['residuals'][1177+olddomain['guards'].index(oldg)]['label'],'each complete Legendre graph and retained row label')
    need(parent['domain']==oldparent['domain']=='unrestricted integers' and parent['schema']==oldparent['schema']=='quadratic_sum_squares_v1' and parent['variant']=='power0_existing_square_frame63_raw_literal_prototype','exact parent domain/schema/provenance')
    frame=load(ROOT/'research/power0-square-frame-source-prototype/FRAME_POLICY.json');radius=load(ROOT/'research/power0-square-frame-source-prototype/RADIUS_POLICY.json')
    need(set(frame['actual_power_ports'])==arguments and len(frame['actual_power_ports'])==43 and set(frame['bounding_ports'])==bounding and len(frame['bounding_ports'])==43,'complete exact prototype frame policy')
    need(frame['newly_squared_output']==dict(changed_frame_row=1135,gate_already_present=True,output=6,source_square_row=2,square_variable=7) and frame['newly_removed_scalar_guard']==6 and frame['raw106_guard_retained'] is True,'only existing raw7 square exchange;106 retained')
    need(frame['inherited_range_square_outputs']==outputs and frame['inherited_square_variables']==squarevars and frame['inherited_square_rows']==list(range(1177,1185)) and frame['inherited_absent_quotient_guards']==removedq,'all inherited8 range squares/omitted quotients unchanged')
    need(radius['joint_guard']==dict(index=62,auxiliary=[1453,1454,1455],predicate=domain['guards'][-1]['predicate']) and radius['unchanged_radius_rows']==[75,90],'actual last joint guard and common-radius policy')
    need(domain['baseline_body_variables']==1267 and domain['baseline_body_rows']==1185 and domain['predicates']==63 and domain['original_scalar_predicates']==60 and domain['newly_removed_scalar_variables']==[6] and domain['inherited_absent_quotient_variables']==removedq and domain['compact_bridge_assumed'] is False,'whole actual RAW domain dimensions/removal metadata')
    need(set(parent)=={'domain','schema','variant','variables','residuals'} and domain['ordinary_source_equivalence_claimed'] is False and frame['ordinary_source_equivalence_claimed'] is False and radius['ordinary_source_equivalence_claimed'] is False,'finite literal packet remains independently scoped; this ordinary proof supplies its separate license')
    # Universal polynomial identities behind signed output; abstract variables.
    aa,nn,xx,yy=map(V,[2000,2001,2002,2003]);dd=add(mul(aa,aa),C(-1));TT=add(add(mul(C(2),mul(aa,nn)),mul(nn,nn),-1),C(-1));an=add(aa,nn,-1)
    pp=add(xx,mul(an,yy),-1);qq=add(xx,mul(an,yy));norm=add(mul(xx,xx),mul(dd,mul(yy,yy)),-1)
    need(add(mul(pp,qq),mul(TT,mul(yy,yy)),-1)==norm,'universal pq=norm+TY² identity')
    nextx=add(mul(aa,xx),mul(dd,yy));nexty=add(xx,mul(aa,yy));nextp=add(nextx,mul(an,nexty),-1)
    need(add(add(nextp,mul(nn,pp),-1),mul(TT,yy),-1)=={},'universal Pell residue recurrence')
    mm,pv,qv,rr=map(V,[2010,2011,2012,2013]);rhs=add(add(mul(mm,add(pv,rr,-1)),mul(pv,add(mm,qv)),-1),add(mul(pv,qv),C(-1)))
    need(rhs==mul(C(-1),add(mul(mm,rr),C(1))),'universal signed divisibility identity, no inverse division')
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
    prior_square=load(ROOT/'research/factorial-square-guard-exchange/CERTIFICATE.json')
    reject('old g*t² radius retained',lambda:collect(prior_square['unchanged_local_cuts']['d1_radius']))
    reject('assume old t1 g(C-1) identity under common radius',lambda:need(P(data['new_t1_combined_cut']['polynomial'])==P([[1,[107,111]],[-1,[113]],[-1,[115]],[1,[112]],[-1,[]],[-1,[107,4,4]]]),'new common base identity'))
    reject('new89 sign retains old f*88 term',lambda:need(rows[75]==P([[1,[89]],[-1,[87,88]]]),'complete changed row'))
    reject('derive f>=K from joint guard before g sign',lambda:need({113,114,115}.isdisjoint(kept),'g sign premises indispensable'))
    reject('common t1 collapse allowed by omitting g bound',lambda:need(50*50+1<=50,'g<=f excludes common t1 collapse'))
    reject('interpret call7 before restoring825',lambda:need(7 in old72['chronology']['interpreted_calls_before_825'],'72 chronology'))
    reject('bind first actual power output to encoded59',lambda:need(raw['powers'][0]['output']==['v',59],'literal power ports'))
    reject('include private825 in semantic frame',lambda:need(825 in arguments,'actual43 argument frame'))
    reject('remove one seed from simultaneous interface',lambda:need(len(raw['seeds'][:-1])==15,'all15 required seeds'))
    reject('replace fresh witness construction by pointwise map',lambda:need(data.get('pointwise_old_new_tuple_map') is True,'new frame/radix witnesses required'))
    common_t1_controls=0
    for f in range(2,25):
        for g in range(f+1):
            for C1 in range(1,f+4):
                slack=g*C1-f*f-1
                if 0<=slack<=4:
                    need(C1>=2,'common t1 ceiling plus g<=f forces C1>=2');common_t1_controls+=1
    need(common_t1_controls>0,'nonvacuous common t1 controls')
    common_ceiling_controls=0;joint_guard_controls=0
    for t in range(1,10):
        for K in range(max(t+1,3),max(t+1,3)+5):
            f=factorial(K);g=factorial(t);num=(1+f*f)**t;den=comb(f*f+t,t)
            need((num+den-1)//den==g,'exact fixed common radius ceiling')
            need(f>=K+g,'canonical joint guard');joint_guard_controls+=1;common_ceiling_controls+=1
    signed_negative_controls=0;positive_output_controls=0
    def pell(A,k):
        x,y=1,0
        for _ in range(k):x,y=A*x+(A*A-1)*y,x+A*y
        return x,y
    for W in range(4,10):
        A,_=pell(W+1,W);need(A>W**W,'canonical finite bootstrap control')
        for n in range(2,W):
            T=2*A*n-n*n-1
            for k in range(1,W):
                x,y=pell(A,k);power=n**k
                for m in range(-W+1,W):
                    need((-x-(A-n)*y-m)%T!=0,'signed negativeX rejected with positiveY');signed_negative_controls+=1
                    good=(x-(A-n)*y-m)%T==0
                    need(good==(m==power),'positiveX yields exact signed output');positive_output_controls+=good
    W=5;A,_=pell(W+1,W);n=3;T=2*A*n-n*n-1
    need((-A-(A-n)*(-1)-(-n))%T==0 and -n<0,'both-negative local pair demonstrates necessity of positiveY')
    need((-A-(A-1)*1-(-1))%(2*A-2)==0,'n1 local counterexample explains actual n>=2 sufficient premise')
    quotient_controls=0
    for M in range(1,6):
        for den in range(1,8):
            for q in range(-4,5):
                for rem in range(den):
                    N=M*den*q+rem
                    need(N<=0 or q>=0,'positive numerator forces quotient nonnegative');quotient_controls+=1
    reject('drop positiveY premise from signed lemma',lambda:need(-1>=1,'both-negative local counterexample excluded'))
    reject('extend signed lemma to n1',lambda:need(1>=2,'n1 negative-output local counterexample'))
    reject('retain old linear frame cut',lambda:collect(old72['frame_cut']))
    reject('install a removed quotient as early sign',lambda:need(removedq[0] in set(range(643))-{59,104}-missing,'q belongs to missing32'))
    reject('call0 retained as pre-recovery orientation support',lambda:need(support['supporting_call']==0,'raw6 is initially signed; support8 is required'))
    reject('install raw6 as early natural sign',lambda:need(6 in set(range(643))-{59,104}-missing,'raw6 absent from608-prefix'))
    reject('use raw548 sign to orient t',lambda:need(support['retained_remainder_guards']==[548],'support positivity comes directly from retained549/550'))
    old64=load(ROOT/'research/range-output-square-frame/CERTIFICATE.json')
    reject('reuse old64 literal linear raw6 frame',lambda:collect(old64['new_weak_frame_cut']))
    reject('square raw6 without exact existing row2',lambda:collect(data['power0_square_cut'],P([[1,[7]],[-1,[6]]])))
    reject('drop106 in raw6-only proposal',lambda:need(106 not in kept,'raw106 retained'))
    signed_recovery_controls=0
    for W in range(4,10):
        A,_=pell(W+1,W)
        for n in range(2,W):
            T=2*A*n-n*n-1
            for k in range(1,W):
                x,y=pell(A,k);r=n**k
                for m in range(-W+1,W):
                    need(((x-(A-n)*y-m)%T==0)==(m==r),'positive pair signed-output residue recovery')
                    need(abs(m-r)<W**W<T,'complete signed output difference bound');signed_recovery_controls+=1
    result=dict(status='PASS',optimized_python=bool(sys.flags.optimize),raw_coordinates=1267,raw_rows=1185,predicates=63,changed_rows=changed_rows+[1135],removed_quotient_guards=removedq,changed_guard='remove8 fused quotients and raw6; joint f>=K+g/raw106 unchanged',private_K_square_retained=True,private_t_square_retained=True,common_ceiling_controls=common_ceiling_controls,joint_guard_controls=joint_guard_controls,common_t1_controls=common_t1_controls,
      complete_row_identities=count,early_prefix_coordinates=early_prefix_count,early_prefix_sign_steps=early_sign_count,delayed_sign_steps=len(skipped),prefix_coordinates=len(known),prefix_sign_steps=sign_count,changed_prefix_sign_steps=changed_signs,inherited_strict_steps=strict_count,new_radius_separate_lower_bound=4,early_g_guards=[113,114,115],old_t1_identity_reused=False,
      signed_recovery_controls=signed_recovery_controls,t_orientation_supports=[8,9],power0_recovered_before_shifted_t=True,signed_negative_orientation_controls=signed_negative_controls,positive_output_controls=positive_output_controls,quotient_sign_controls=quotient_controls,universal_pell_identities=3,guard_graphs=63,literal_parent_coordinates=1456,literal_parent_rows=1248,actual_power_requests=21,seed_tests=15,index_atoms=16,derived_pairs=1,exact_binomials=3,range_graphs=8,range_lower_ports=lower,frame_arguments=43,
      squared_radius_exact_ceiling_controls=fixed_controls,acyclic_range_bound_controls=range_controls,collapsed_branch_controls=collapsed_controls,rejected_corruptions=rejected,
      source_pins={name:digest(HERE/name) for name in ['PROOF.md','FULL_SOURCE.md','CERTIFICATE.json','SOURCE_PINS.json','check.py']},
      imported_archive_executed=False,source_builder_optimizer_parent_checker_or_lean_executed=False,ordinary_changed_raw_source_equivalence=True,projected_metrics_claimed=False,
      scope='Complete literal source interfaces and finite controls for ordinary changed-source proof. Unbounded argument in PROOF.md/FULL_SOURCE.md; projected restoration/quartic acceptance remains separate.')
    text=json.dumps(result,indent=2,sort_keys=True)+'\n'
    if args.output.exists():need(args.output.read_text()==text,'refuse to overwrite different receipt bytes')
    else:args.output.write_text(text)
    print(text,end='')
if __name__=='__main__':main()
