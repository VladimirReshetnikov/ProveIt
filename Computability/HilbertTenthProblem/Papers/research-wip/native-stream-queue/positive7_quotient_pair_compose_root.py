"""Original one-shot structural splice; no source arithmetic is evaluated.

Read frozen JSON as records. Construct the paired quotient cut; compare
unchanged records, labels, counts, boundaries, dependencies and liveness.
Freeze after the first output and never execute or import this file again.
"""
import json
import hashlib
from pathlib import Path
from collections import Counter

WIP=Path('/home/codex/.codex/worktrees/2a71/Proofs/Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue')
PARENT=WIP/'positive7_guarded_two_form_compiler_root.json'
PIN='99e59b73bf1e6a9b0810f8ed862fefe62af00842edafd216e1c0420881ea7784'
OUT=Path('/tmp/positive7_quotient_pair_compose_root.json')
assert not OUT.exists()
data=PARENT.read_bytes();assert hashlib.sha256(data).hexdigest()==PIN
parent=json.loads(data)
def count(records):
    labels=Counter(row[1] for row in records)
    assert set(labels)<=set('+-*')
    return dict(M=labels['*'],A=labels['+']+labels['-'],operations=len(records))
def numeral(name):return {'fixed':name}
examples=[]
for before in parent['examples']:
    r=before['r'];oldrows=before['source'];cut_start=next(i for i,row in enumerate(oldrows) if row[0]=='selected_center_8')
    cut_end=next(i for i,row in enumerate(oldrows) if row[0]=='five_increment_sum_1')
    assert count(oldrows[cut_start:cut_end])==dict(M=14*r,A=16*r,operations=30*r)
    cut=[];previous=['out_a','out_b','joint_C0','out_d','out_e','out_f'];pair_ports={}
    def put(name,op,left,right):
        cut.append([name,op,left,right]);return name
    for j in range(r):
        plus=8+2*j;minus=plus+1
        for s in [plus,minus]:
            off=put('selected_center_'+str(s),'*','center_height','selector_'+str(s))
            for a in [1,2]:put('signed_selected_form_'+str(s)+'_'+str(a),'-','selected_'+str(s)+'_'+str(a),off)
        reduced=[]
        for a in [1,2]:
            terms=[]
            for b in [1,2]:
                terms.append(put(f'quotient_term_{j}_{a}_{b}','*',numeral(f'quotient_T_{j}_{a}_{b}'),f'signed_selected_form_{minus}_{b}'))
            dot=put(f'quotient_sum_{j}_{a}','+',terms[0],terms[1])
            reduced.append(put(f'quotient_difference_{j}_{a}','-',f'signed_selected_form_{plus}_{a}',dot))
        pair_ports[str(j)]=dict(plus_slot=plus,minus_slot=minus,reduced_forms=reduced)
        for i in [4,5,6]:
            for a in [1,2]:
                term=put(f'quotient_action_term_{j}_{i}_{a}','*',numeral(f'relator_E_{plus}_{i}_{a}'),reduced[a-1])
                previous[i-1]=put(f'quotient_action_sum_{j}_{i}_{a}','+',previous[i-1],term)
    assert count(cut)==dict(M=12*r,A=14*r,operations=26*r)
    binding=dict(zip(before['ports']['six_increments'],previous))
    suffix=[]
    for name,op,a,b in oldrows[cut_end:]:
        suffix.append([name,op,binding.get(a,a) if isinstance(a,str) else a,binding.get(b,b) if isinstance(b,str) else b])
    assert len(suffix)==121 and suffix[53:]==oldrows[-68:]
    rows=oldrows[:cut_start]+cut+suffix
    supplied=before['ordinary_parameters']+before['positive_auxiliaries'];seen=set(supplied);edges={};roles=set();consumers={}
    assert len(seen)==len(supplied)
    for name,op,a,b in rows:
        assert name not in seen and op in ['+','-','*']
        for position,value in enumerate([a,b]):
            if type(value) is str:
                assert value in seen;(consumers.setdefault(value,[])).append([name,position])
            elif type(value) is dict:
                assert set(value)=={'fixed'};roles.add(value['fixed'])
            else:assert type(value) is int
        seen.add(name);edges[name]=[a,b]
    live=set();pending=[before['output']]
    while pending:
        name=pending.pop()
        if type(name) is str and name not in live:live.add(name);pending.extend(edges.get(name,[]))
    assert set(edges)<=live and set(supplied)<=live
    assert len(roles)==6+18*r
    pc=before['power_cost'];cert=count(rows[:-68]);poly=count(rows)
    assert cert==dict(M=280+40*r+pc,A=550+52*r,operations=830+92*r+pc)
    assert poly==dict(M=303+40*r+pc,A=595+52*r,operations=898+92*r+pc)
    after={k:v for k,v in before.items() if k not in ['source','ports','stages','static_checks','parent_suffix_bindings','certificate_ledger','polynomial_ledger','certificate_prefix_rows']}
    after.update(source=rows,ports=dict(before['ports'],six_increments=previous),stages={('selected_quotient_pair_appends' if k=='selected_guarded_relator_appends' else k):(count(cut) if k=='selected_guarded_relator_appends' else v) for k,v in before['stages'].items()},static_checks=dict(topology=True,all_computed_live=True,all_supplied_live=True,named_fixed_roles=sorted(roles)),parent_suffix_bindings=binding,certificate_ledger=cert,polynomial_ledger=poly,certificate_prefix_rows=len(rows)-68,quotient_pair_ports=pair_ports,splice=dict(old_start_index=cut_start,old_stop_index=cut_end,old_cut_count=count(oldrows[cut_start:cut_end]),new_cut_count=count(cut),prefix_literal_equal=rows[:cut_start]==oldrows[:cut_start],finalizer_literal_equal=rows[-68:]==oldrows[-68:],comparison_list_literal_equal=True,positive_auxiliaries_literal_equal=True,new_cut_sha256=hashlib.sha256(json.dumps(cut,separators=(',',':')).encode()).hexdigest()))
    assert after['comparisons']==before['comparisons'] and after['positive_auxiliaries']==before['positive_auxiliaries']
    examples.append(after)
receipt=dict(status='FROZEN first original metadata-only quotient composition; no future replay',emitter_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),inputs=[dict(path=str(PARENT),sha256=PIN,bytes=len(data))],generic_ledger=dict(domain='r>=1',certificate='(280+40r+powcost(62+6r))M+(550+52r)A',polynomial='(303+40r+powcost(62+6r))M+(595+52r)A',operations='898+92r+powcost(62+6r)',witnesses='96+6r',equations=23,fixed_roles='6+18r',exact_saving='2rM+2rA from complete guarded parent'),r0_fallback=dict(parent['r0_fallback'],inherited_through_guarded_receipt=PIN),fixed_data_recipe=[
 'Retain actual fixed guarded forms, lambda,Cg,K and positive7/program slice; no input/domain/witness or native geometry change.',
 'For each relator A=S(P), use exact integer V=[u;v], Eplus with A-I=Eplus*V, primitive w fixed by A, and u cross v=+/-w.',
 'Choose fixed integer row c with c*w=1; U=[u;v;c] is unimodular. J0 is first2 columns of U inverse and V*J0=I2.',
 'Fixed quotient_T=V*S(P inverse)*J0 is integral SL2, independent of section, and V*S(P inverse)=quotient_T*V.',
 'The old Eminus equals -Eplus*quotient_T. Replace Eplus*tplus+Eminus*tminus by Eplus*(tplus-quotient_T*tminus).',
 'Central P=+/-I retains V=[e1;e2], Eplus=0, w=e3,c=e3^T,J0=first2 identity columns,T=I2; no zero-normal division.',
 'Runtime roles retain8 signed form_ell plus6 positive-sign relator_E and4 signed quotient_T entries per relator;6 global roles unchanged.',
 'Every new fixed product is charged, including zero/unit coefficients. Identity is for all integer runtime inputs and accumulators after fixed roles follow the same actual-relator recipe.'
],examples=examples,execution_scope='Original metadata-only record splice and name/operation/topology/liveness/count checks. No source or coefficient evaluation, degree propagation, scalar sampling, prior code execution/import or build. Exactly3 complete saved graphs r1,2,4; no additional formula-only samples.')
OUT.write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps(dict(output=str(OUT),sha256=hashlib.sha256(OUT.read_bytes()).hexdigest(),saved_rows=sum(len(g['source']) for g in examples),examples=[{k:g[k] for k in ['r','polynomial_ledger','witnesses']} for g in examples]),indent=2))
