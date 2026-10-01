"""Erase every hub idle step after the complete projective endpoint theorem.

Nonempty macro tables use only their non-idle edge hats. Their literal
polynomial is a parent specialization; accepted-input equivalence also
uses fresh histories after deleting idle positions from an accepting run.
"""
import argparse
from collections import Counter
import json
from pathlib import Path
import random

import group_projective_frozen_idle_padding as parent
import group_projective_padded_program_margin as margin

execute = parent.execute
residuals = parent.residuals


def rewrite(old):
    assert old['frozen_idle_padding']
    n = old['active_edges']-1
    if not n:
        return dict(old, idle_free_paths=True, idle_free_applied=False,
                    idle_free_saving=dict(M=0,A=0,operations=0),
                    idle_free_changed_registers=[], idle_free_plan='empty-table fallback')
    idle = 'controller__edge_hat0'
    assert old['edges'][0] == (0,0,0) and idle in old['auxiliaries']
    rows = {row[0]: row for row in old['source']}
    P = 'controller__geometry_power' if old['compute_length'] else 'P'
    private = {name for name in rows if name.startswith(
        ('controller__edge_pack_', 'frozen_idle_pack_', 'frozen_idle_R'))}
    word = 'controller__edge_word'
    assert private and word in rows
    assert all({user for user,_,a,b in old['source'] if name in (a,b)}
               <= private | {word} for name in private)
    assert not any(name in pair for name in private for pair in old['comparisons'])
    pack_names = private | {word}

    # The only other idle consumer is the hub raw sum, or the last checksum.
    hub = [edge for edge in old['flow']['groups']['hub'] if edge < old['active_edges']]
    assert hub[0] == 0
    aliases, changed, removed_checksum = {}, [], set()
    checksum = rows['computed_J'][2]
    assert rows['computed_J'] == ('computed_J','-',checksum,n+1)
    if len(hub)>1:
        first = 'controller__flow_raw_hub1'
        assert rows[first] == (first,'+',idle,f'controller__edge_hat{hub[1]}')
        aliases[first] = f'controller__edge_hat{hub[1]}'
        removed_checksum.add(first)
        previous = first
        for j,edge in enumerate(hub[2:],2):
            name = f'controller__flow_raw_hub{j}'
            assert rows[name] == (name,'+',previous,f'controller__edge_hat{edge}')
            changed.append(name)
            previous = name
        assert checksum == previous or rows[checksum][3] == previous
        if checksum != previous:
            changed.append(checksum)
    else:
        assert rows[checksum][1] == '+' and rows[checksum][3] == idle
        aliases[checksum] = rows[checksum][2]
        removed_checksum.add(checksum)
    allowed = pack_names | {f'controller__flow_raw_hub{j}' for j in range(1,len(hub))} | {checksum}
    assert {user for user,_,a,b in old['source'] if idle in (a,b)} <= allowed
    changed_set = set(changed) | removed_checksum
    assert all({user for user,_,a,b in old['source'] if name in (a,b)}
               <= changed_set | {'computed_J'} for name in changed_set)
    assert not any(name in pair for name in changed_set for pair in old['comparisons'])

    def resolved(value):
        while isinstance(value,str) and value in aliases:
            value = aliases[value]
        return value

    def power(j):
        if j == 0:return P
        name=f'controller__lane_power{j}'
        previous=P if j==1 else f'controller__lane_power{j-1}'
        assert rows[name] == (name,'*',previous,previous)
        return name

    def dyadic_repunit(j):
        if j==0:return 1
        if j==1:
            name='controller__lane_factor0'
            assert rows[name] == (name,'+',P,1)
            return name
        name=f'controller__lane_repunit{j-1}'
        factor=f'controller__lane_factor{j-1}'
        assert rows[factor] == (factor,'+',power(j-1),1)
        assert rows[name] == (name,'*',dyadic_repunit(j-1),factor)
        return name

    # Fallback retains the already audited parent packing, with the hat=1.
    keep=[(name,op,1 if a==idle else a,1 if b==idle else b)
          for name,op,a,b in old['source'] if name in pack_names]
    factored=[]
    def repunit(length):
        j=length.bit_length()-1;high=1<<j
        if high==length:return dyadic_repunit(j)
        low=repunit(length-high)
        prod=power(j)
        if low!=1:
            prod=f'idle_free_R{length}_product'
            factored.append((prod,'*',power(j),low))
        name=f'idle_free_R{length}'
        factored.append((name,'+',dyadic_repunit(j),prod))
        return name
    R=repunit(n)
    value=f'controller__edge_hat{n}'
    for i in range(n-1,0,-1):
        prod=f'idle_free_pack_mult{i}';total=f'idle_free_pack_sum{i}'
        factored += [(prod,'*',P,value),(total,'+',f'controller__edge_hat{i}',prod)]
        value=total
    factored += [('idle_free_inner_word','-',value,R),(word,'*',P,'idle_free_inner_word')]
    plans=[dict(kind='specialized parent',source=keep),dict(kind='factored non-idle',source=factored)]
    for plan in plans:
        counts=Counter('M' if op=='*' else 'A' for _,op,_,_ in plan['source'])
        plan.update(operations=len(plan['source']),M=counts['M'],A=counts['A'])
    chosen=min(plans,key=lambda plan:(plan['operations'],plan['M'],plan['kind']))
    source=[]
    for name,op,a,b in old['source']:
        if name in pack_names | removed_checksum:continue
        a,b=resolved(a),resolved(b)
        if name=='computed_J':b=n
        assert idle not in (a,b)
        source.append((name,op,a,b))
    source += chosen['source']
    auxiliaries=[name for name in old['auxiliaries'] if name!=idle]
    source=parent.parent.ports.shared.factored.index.parent.sort_source(source,{'x',*auxiliaries})
    counts=Counter('M' if op=='*' else 'A' for _,op,_,_ in source)
    saving=dict(M=old['multiplications']-counts['M'],A=old['additions_subtractions']-counts['A'],
                operations=old['operations']-len(source))
    assert saving['operations']==1+len(keep)-len(chosen['source'])>=1
    assert not any(idle in (a,b) for _,_,a,b in source)
    return dict(old,source=source,auxiliaries=auxiliaries,operations=len(source),
                multiplications=counts['M'],additions_subtractions=counts['A'],
                positive_witnesses=len(auxiliaries),idle_free_paths=True,idle_free_applied=True,
                idle_free_saving=saving,idle_free_changed_registers=changed,
                idle_free_plan=chosen['kind'],idle_free_pack_plans=plans,
                idle_free_removed_registers=sorted(pack_names|removed_checksum))


def build(codes,alpha=24,beta=12,variant='joint',controller_mask=False,compute_length=False):
    return rewrite(parent.build(codes,alpha,beta,variant,controller_mask,compute_length))


def polynomial_source(packet):return parent.polynomial_source(packet)


def degree_top(packet,weights):
    expanded=dict(weights)
    if packet['idle_free_applied']:expanded['controller__edge_hat0']=0
    return parent.degree_top(packet,expanded)


def source_checks():
    rng=random.Random(2613504);records=[];cases=signed=0;example=None
    tables=[(),((1,),),((1,),(2,)),((1,2),),((1,2,3),),((1,2),(3,4)),
            ((1,),(2,3,4),(5,)),((1,2,3,4,5,6,7,8,1,2),),
            (tuple(1+i%8 for i in range(14)),),(tuple(1+i%8 for i in range(16)),)]
    for codes in tables:
      for variant in ('four','six','shifted','strong','joint'):
       for reuse in (False,True):
        if reuse and parent.build(codes)['m']<8:continue
        for comp in (False,True):
            old=parent.build(codes,variant=variant,controller_mask=reuse,compute_length=comp)
            packet=rewrite(old);source,out=polynomial_source(packet);prior,prior_out=parent.polynomial_source(old)
            assert packet['comparisons']==old['comparisons']
            assert packet['positive_witnesses']==old['positive_witnesses']-packet['idle_free_applied']
            for case in range(24):
                positive=case<16
                values={name:rng.randrange(1,6) if positive else rng.randrange(-3,4)
                        for name in packet['parameters']+packet['auxiliaries']}
                restored=dict(values)
                if packet['idle_free_applied']:restored['controller__edge_hat0']=1
                env,before=execute(source,values),execute(prior,restored)
                changed=set(packet['idle_free_changed_registers'])
                assert all(env[name]==before[name] for name,_,_,_ in source if name in before and name not in changed)
                assert residuals(packet,env)==residuals(old,before) and env[out]==before[prior_out]
                assert all(before[name]-env[name]==1 for name in changed)
                if packet['idle_free_applied']:
                    P=env['controller__geometry_power'] if comp else values['P']
                    n=packet['active_edges']-1
                    direct=sum((values[f'controller__edge_hat{i}']-1)*P**i for i in range(1,n+1))
                    assert env['controller__edge_word']==direct
                    assert env['computed_J']==sum(values[f'controller__edge_hat{i}']-1 for i in range(1,n+1))
                    for plan in packet['idle_free_pack_plans']:
                        outputs={row[0] for row in plan['source']}
                        probe=execute(plan['source'],{name:v for name,v in before.items() if name not in outputs})
                        assert probe['controller__edge_word']==direct
                cases+=1;signed+=not positive
            weights={name:1+i%3 for i,name in enumerate(packet['parameters']+packet['auxiliaries'])}
            weights['selection__tau_gap']=1
            degree,top=degree_top(packet,weights)[:2]
            assert top!=0
            counts=Counter('M' if op=='*' else 'A' for _,op,_,_ in source)
            records.append(dict(nonidle_edges=packet['active_edges']-1,m=packet['m'],variant=variant,
                controller_mask=reuse,compute_length=comp,plan=packet['idle_free_plan'],
                saving=packet['idle_free_saving'],certificate_operations=packet['operations'],
                polynomial_operations=len(source),polynomial_M=counts['M'],polynomial_A=counts['A'],
                equations=packet['equations'],positive_witnesses=packet['positive_witnesses'],exact_degree=degree))
            if codes==tables[7] and variant=='joint' and reuse and comp:
                example=dict(packet,polynomial_finalizer=source[packet['operations']:],polynomial_output=out)
                assert (packet['operations'],len(source),counts['M'],counts['A'],degree,packet['positive_witnesses'])==(244,261,113,148,3504,36)
    return dict(records=records,source_example=example,exact_specialization_cases=cases,signed_cases=signed)


def positive_path_checks():
    model=margin.parent.parent.parent
    physical=model.physical
    word=model.reflect_codes((physical.target_word(36),))[0]
    assert word and 0 not in word
    states=model.trace(word,37)
    assert states[0]==[1,37,1,37] and states[-1]==[0,1,0,1]
    padded=(0,0)+tuple(v for letter in word for v in (letter,0))+(0,)
    padded_states=model.trace(padded,37)
    assert padded_states[-1]==states[-1]
    assert tuple(letter for letter in padded if letter)==word
    D=1<<(max(37,1+max(abs(v) for row in states for v in row))).bit_length()
    B=16*D;P=B**len(word);J=(P-1)//(B-1)
    rows=[[D-1+v for v in row] for row in states[:-1]]
    H=[sum(row[i]*B**j for j,row in enumerate(rows)) for i in range(4)]
    Z=[sum((label==i+1)*rows[j][(i//2)^1]*B**j for j,label in enumerate(word)) for i in range(8)]
    E=[sum((label==i)*B**j for j,label in enumerate(word)) for i in range(16)]
    assert E[0]==0 and all(v==0 for v in E[9:]) and sum(E)==J
    records=[]
    for reuse in (False,True):
      for comp in (False,True):
        packet=build(tuple((i,) for i in range(1,9)),controller_mask=reuse,compute_length=comp)
        values={name:1 for name in packet['parameters']+packet['auxiliaries']}
        values.update(height_slack=D-37,selection__bound_global=P-sum(H)-sum(Z)-7)
        if not comp:values['P']=P
        values.update({f'H{i}':v for i,v in enumerate(H)})
        values.update({f'Zhat{i}':v+1 for i,v in enumerate(Z)})
        values.update({f'controller__edge_hat{i}':E[i]+1 for i in range(1,9)})
        assert min(values.values())>0
        env=execute(packet['source'],values)
        assert env['D']==D and env['computed_J']==J
        assert (env['controller__geometry_power'] if comp else values['P'])==P
        assert env['joint_bound_unit']==1
        for a,b in packet['comparisons']:
            if a=='eight_units':continue
            assert (env[a] if isinstance(a,str) else a)==(env[b] if isinstance(b,str) else b)
        assert env['range_H'] & env['range_M']==env['range_Z']
        records.append(dict(controller_mask=reuse,compute_length=comp,duration=len(word),
                            deleted_idle_positions=len(padded)-len(word),D=D,
                            positive_outer_coordinates=True,history_flow_and_AND=True))
    return dict(fixtures=records,
                scope='Genuine non-idle reflected endpoint paths with all outer constraints. Native Pell witnesses are placeholders; their positive extension is the imported parametric theorem.')


def verify():
    return dict(status='PASS_GROUP_PROJECTIVE_IDLE_FREE_PATHS',source=source_checks(),
                positive_paths=positive_path_checks(),
                scope='Every nonempty macro table can omit all hub idle selectors. Full polynomial specialization is exact; accepted-input equivalence reconstructs fresh shorter histories. Empty tables retain the parent. No universal numerical alphabet or smaller75/88 bound is claimed.')


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--write',action='store_true');args=parser.parse_args()
    result=json.loads(json.dumps(verify()));path=Path(__file__).with_suffix('.json')
    if args.write:path.write_text(json.dumps(result,indent=2)+'\n')
    else:assert json.loads(path.read_text())==result,'receipt mismatch'
    print(result['status'])
