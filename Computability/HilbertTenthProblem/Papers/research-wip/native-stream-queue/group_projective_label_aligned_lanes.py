"""Choose paid label-aligned controller lane positions within fixed geometry.

Only the controller packing changes. Physical codes, edge IDs, chronological
state flow, scale, origin mask, and all supplied coordinates remain fixed.
The current complete compiler is an explicit no-increase fallback.
"""
import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import random

import sympy as sp
import group_projective_reindexed_shared_pack as parent

execute=parent.execute
residuals=parent.residuals
packing=parent.packing
geometry=parent.geometry


def assignments(base):
    n=base['active_edges']-1;m=base['m']
    if not n:return []
    labels={e:base['edges'][e][2]-1 for e in range(1,n+1)}
    proposals=[]
    # At most two phase choices and two orders. Out-of-capacity preferred
    # lanes are reassigned to unused lanes, so m is never enlarged.
    for phase in sorted({0,min(labels.values())}):
      for reverse in (False,True):
        used=set();positions={};occurrence=Counter();overflow=[]
        for e in sorted(labels,reverse=reverse):
            label=labels[e];p=label-phase+8*occurrence[label];occurrence[label]+=1
            if 0<=p<m:
                assert p not in used
                positions[e]=p;used.add(p)
            else:overflow.append(e)
        holes=iter(sorted(set(range(m))-used))
        for e in overflow:positions[e]=next(holes)
        proposals.append((f'layered phase{phase} '+('reverse' if reverse else 'forward'),positions))
    for reverse in (False,True):
        order=sorted(labels,key=lambda e:(labels[e],-e if reverse else e))
        proposals.append(('contiguous label groups '+('reverse' if reverse else 'forward'),
                          {e:p for p,e in enumerate(order)}))
    unique={}
    for tag,positions in proposals:
        assert set(positions)==set(labels) and len(set(positions.values()))==n
        assert min(positions.values())>=0 and max(positions.values())<m
        unique.setdefault(tuple(sorted(positions.items())),(tag,positions))
    return list(unique.values())


def scaffold(base,positions):
    """An entirely paid direct word that the existing planner may improve."""
    n=base['active_edges']-1;P='controller__geometry_power' if base['compute_length'] else 'P'
    rows={row[0]:row for row in base['source']};word='controller__edge_word'
    private={name for name in rows if name.startswith(('controller__edge_pack_',
        'frozen_idle_pack_','frozen_idle_R','idle_free_pack_','idle_free_R'))}
    private.update(name for name in ('idle_free_inner_word',) if name in rows)
    assert word in rows
    assert all({name for name,_,a,b in base['source'] if v in (a,b)}<=private|{word} for v in private)
    assert not any(v in pair for v in private for pair in base['comparisons'])
    source=[row for row in base['source'] if row[0] not in private|{word}]
    # Reuse only exactly proved pure P powers. New powers stay private and
    # disappear if the sharing planner selects a different expression.
    exponents={P:1};powers={0:1,1:P}
    for name,op,a,b in source:
        if name==P:continue
        if op=='*' and a in exponents and b in exponents:
            exponents[name]=exponents[a]+exponents[b]
            powers.setdefault(exponents[name],name)
    added=[]
    def emit(op,a,b):
        if op=='*' and b==1:return a
        if op=='*' and a==1:return b
        if isinstance(a,int) and isinstance(b,int):
            return a*b if op=='*' else a+b if op=='+' else a-b
        name=f'idle_free_pack_lane_{len(added)}';added.append((name,op,a,b));return name
    def power(e):
        if e not in powers:
            half=e//2
            value=emit('*',power(half),power(half))
            if e%2:value=emit('*',value,P)
            powers[e]=value
        return powers[e]
    order=sorted(positions,key=positions.get,reverse=True)
    value=f'controller__edge_hat{order[0]}';mask=1;last=positions[order[0]]
    for e in order[1:]:
        p=positions[e];gap=last-p
        value=emit('+',f'controller__edge_hat{e}',emit('*',power(gap),value))
        mask=emit('+',1,emit('*',power(gap),mask));last=p
    value=emit('-',value,mask)
    value=emit('*',power(last),value)
    assert added and added[-1][0]==value
    added[-1]=(word,*added[-1][1:]);source+=added
    source=packing.parent.parent.parent.ports.shared.factored.index.parent.sort_source(source,{'x',*base['auxiliaries']})
    counts=Counter('M' if op=='*' else 'A' for _,op,_,_ in source)
    lanes=[(0,0,0)]*base['m']
    for e,p in positions.items():lanes[p]=base['edges'][e]
    candidate=dict(base,source=source,operations=len(source),multiplications=counts['M'],
        additions_subtractions=counts['A'],packed_edge_exponents=positions,lane_edges=lanes)
    variables=[f'controller__edge_hat{e}' for e in range(1,n+1)]
    expected={v:packing.monomial(positions[e]) for e,v in enumerate(variables,1)}
    constant=(0,)
    for poly in expected.values():constant=packing.padd(constant,poly,-1)
    expected[None]=constant
    assert packing.linear_audit(source,word,P,variables)==expected
    return candidate


def rewrite(base):
    """Input is the unshared reindexed geometry packet; baseline is current245."""
    old=packing.rewrite(base);choices=[('current compiler',old)]
    for tag,positions in assignments(base):
        if positions==base['packed_edge_exponents']:continue
        choices.append((tag,packing.rewrite(scaffold(base,positions))))
    # A tie preserves the current compiler, not merely an equal-count new map.
    tag,chosen=min(choices,key=lambda row:(row[1]['operations'],row[0]!='current compiler',
                                          row[1]['multiplications'],row[0]))
    changed=tag!='current compiler'
    saving=dict(M=old['multiplications']-chosen['multiplications'],
                A=old['additions_subtractions']-chosen['additions_subtractions'],
                operations=old['operations']-chosen['operations'])
    assert saving['operations']>=0
    assert all(chosen[k]==old[k] for k in ('parameters','auxiliaries','comparisons','m','h','scale_exponent','edges','codes'))
    return dict(chosen,label_aligned_lanes=True,label_lane_plan=tag,label_lanes_changed=changed,
        label_lane_saving=saving,previous_packed_edge_exponents=base['packed_edge_exponents'],
        label_lane_candidates=[dict(plan=name,operations=p['operations'],M=p['multiplications'],
                                   A=p['additions_subtractions'],positions=p['packed_edge_exponents'],
                                   sharing_plan=p['shared_selector_plan']) for name,p in choices])


def build(codes,alpha=24,beta=12,variant='joint',controller_mask=False,compute_length=False):
    return rewrite(geometry.build(codes,alpha,beta,variant,controller_mask,compute_length))


def polynomial_source(packet):return parent.polynomial_source(packet)


def degree_top(packet,weights):
    if not packet['label_lanes_changed']:return parent.degree_top(packet,weights)
    # General lane-to-coordinate map; physical coefficients never change.
    w=dict(weights)
    for lane in range(packet['m']):w[f'controller__edge_hat{lane}']=0
    for e,p in packet['packed_edge_exponents'].items():w[f'controller__edge_hat{p}']=weights[f'controller__edge_hat{e}']
    return geometry.parent.parent.parent.degree_top(dict(packet,edges=packet['lane_edges']),w)


def source_checks():
    rng=random.Random(227196)
    tables=[(),((1,),),((8,),),((1,2),(3,4)),(tuple(range(1,9)),),
            ((8,6,4,2,7,5,3,1),),((8,6,4),(2,7),(5,3,1)),
            ((1,2,3,4,5,6,7,8,1,2),),((1,)*8,),
            ((8,8,8,8,1,2,3,4,5,6,7,1),),
            ((8,7,6,5,4,3,2,1)*2,),((8,),(1,2),(7,),(6,3,4,5))]
    records=[];cases=signed=0;example=None
    for codes in tables:
      for variant in ('four','six','shifted','strong','joint'):
       for reuse in (False,True):
        if reuse and geometry.parent.build(codes)['m']<8:continue
        for comp in (False,True):
            base=geometry.build(codes,variant=variant,controller_mask=reuse,compute_length=comp)
            old=packing.rewrite(base);packet=rewrite(base);source,out=polynomial_source(packet)
            prior,prior_out=geometry.polynomial_source(base)
            assert len(packet['label_lane_candidates'])<=7
            assert packet['operations']<=old['operations']
            if not packet['label_lanes_changed']:assert packet['source']==old['source']
            for case in range(16):
                positive=case<12
                values={name:rng.randrange(1,6) if positive else rng.randrange(-3,4)
                        for name in packet['parameters']+packet['auxiliaries']}
                env=execute(source,values)
                before=execute(base['source'],values)
                P=before['controller__geometry_power'] if comp else values['P']
                n=packet['active_edges']-1
                if n:
                    direct=sum((values[f'controller__edge_hat{e}']-1)*P**pos
                               for e,pos in packet['packed_edge_exponents'].items())
                    assert env['controller__edge_word']==direct
                else:direct=before['controller__edge_word']
                probe=dict(values)
                for name,op,a,b in prior:
                    if name=='controller__edge_word':probe[name]=direct;continue
                    aa=probe[a] if isinstance(a,str) else a;bb=probe[b] if isinstance(b,str) else b
                    probe[name]=aa*bb if op=='*' else aa+bb if op=='+' else aa-bb
                assert residuals(packet,env)==residuals(base,probe)
                assert env[out]==probe[prior_out]
                assert all(env[name]==probe[name] for name,_,_,_ in packet['source'] if name in probe)
                for name in ('computed_J','controller__origin_mask','selection__Mbatch','selection__Hbatch','selection__Zbatch'):
                    assert env[name]==before[name]
                assert env['selection__q']==before['selection__q']
                cases+=1;signed+=not positive
            w={name:1+i%3 for i,name in enumerate(packet['parameters']+packet['auxiliaries'])}
            w['selection__tau_gap']=1
            for e,name in enumerate(packet['controller_edge_coordinates']):w[name]=1<<e
            degree,top=degree_top(packet,w)[:2]
            assert (degree,top)==parent.degree_top(old,w)[:2] and top
            counts=Counter('M' if op=='*' else 'A' for _,op,_,_ in source)
            records.append(dict(codes=codes,variant=variant,m=packet['m'],controller_mask=reuse,compute_length=comp,
                plan=packet['label_lane_plan'],positions=packet['packed_edge_exponents'],saving=packet['label_lane_saving'],
                old_certificate_operations=old['operations'],certificate_operations=packet['operations'],
                polynomial_operations=len(source),polynomial_M=counts['M'],polynomial_A=counts['A'],
                equations=packet['equations'],positive_witnesses=packet['positive_witnesses'],exact_degree=degree))
            if codes==tables[5] and variant=='joint' and reuse and comp:
                example=dict(packet,polynomial_finalizer=source[packet['operations']:],polynomial_output=out)
                assert (packet['operations'],len(source),counts['M'],counts['A'],degree)==(210,227,98,129,2240)
            if codes==tables[7] and variant=='joint' and reuse and comp:
                assert len(source)==245 and not packet['label_lanes_changed']
    return dict(records=records,source_example=example,full_scalar_interface_and_polynomial_cases=cases,signed_cases=signed)


def degree_checks():
    t=sp.Symbol('t');results=[]
    examples=[(((8,6,4,2,7,5,3,1),),True,True),
              (((8,6,4),(2,7),(5,3,1)),False,False),
              (((8,8,8,8,1,2,3,4,5,6,7,1),),True,True),
              (((8,),(1,2),(7,),(6,3,4,5)),False,True)]
    for codes,reuse,comp in examples:
        packet=build(codes,controller_mask=reuse,compute_length=comp)
        names=packet['parameters']+packet['auxiliaries'];w={name:1+i%3 for i,name in enumerate(names)}
        w['selection__tau_gap']=1
        for e,name in enumerate(packet['controller_edge_coordinates']):w[name]=1<<e
        values={name:sp.Poly(w[name]*t+i+1,t) for i,name in enumerate(names)}
        factors=['first_unit','selection__R15','selection__P17','index_unit','linear_unit','strong_unit','joint_bound_unit']
        rows={row[0]:row for row in packet['source']};needed=set()
        def visit(name):
            if not isinstance(name,str) or name not in rows or name in needed:return
            needed.add(name);visit(rows[name][2]);visit(rows[name][3])
        for name in factors:visit(name)
        for pair in packet['comparisons']:
            if pair!=('eight_units',1):
                for name in pair:visit(name)
        env=execute([row for row in packet['source'] if row[0] in needed],values)
        def value(v):return env[v] if isinstance(v,str) else sp.Poly(v,t)
        outer=[value(a)-value(b) for a,b in packet['comparisons'] if (a,b)!=('eight_units',1)]
        od=max(v.degree() for v in outer);outer_top=sum(v.LC()**2 for v in outer if v.degree()==od)
        ud=sum(env[name].degree() for name in factors);ut=1
        for name in factors:ut*=env[name].LC()
        assert (ud+2*od,ut*outer_top)==degree_top(packet,w)[:2]
        top=abs(int(ut*outer_top));encoded=top.to_bytes((top.bit_length()+7)//8,'big')
        results.append(dict(codes=codes,controller_mask=reuse,compute_length=comp,degree=ud+2*od,
                            unit_degree=ud,outer_residual_degree=od,top_sha256=hashlib.sha256(encoded).hexdigest()))
    return results


def positive_path_checks():
    model=geometry.parent.margin.parent.parent.parent;physical=model.physical
    word=model.reflect_codes((physical.target_word(36),))[0];states=model.trace(word,37)
    assert states[0]==[1,37,1,37] and states[-1]==[0,1,0,1]
    D=1<<(max(37,1+max(abs(v) for row in states for v in row))).bit_length()
    B=16*D;P=B**len(word);J=(P-1)//(B-1)
    rows=[[D-1+v for v in row] for row in states[:-1]]
    H=[sum(row[i]*B**j for j,row in enumerate(rows)) for i in range(4)]
    Z=[sum((label==i+1)*rows[j][(i//2)^1]*B**j for j,label in enumerate(word)) for i in range(8)]
    permutation=(8,6,4,2,7,5,3,1);codes=tuple((i,) for i in permutation)
    E={e:sum((label==physical_label)*B**j for j,label in enumerate(word))
       for e,physical_label in enumerate(permutation,1)}
    results=[]
    for reuse in (False,True):
      for comp in (False,True):
        packet=build(codes,controller_mask=reuse,compute_length=comp)
        assert packet['label_lanes_changed']
        values={name:1 for name in packet['parameters']+packet['auxiliaries']}
        values.update(height_slack=D-37,selection__bound_global=P-sum(H)-sum(Z)-7)
        if not comp:values['P']=P
        values.update({f'H{i}':v for i,v in enumerate(H)})
        values.update({f'Zhat{i}':v+1 for i,v in enumerate(Z)})
        values.update({f'controller__edge_hat{e}':v+1 for e,v in E.items()})
        assert min(values.values())>0
        env=execute(packet['source'],values)
        assert env['computed_J']==J and env['joint_bound_unit']==1
        for a,b in packet['comparisons']:
            if a=='eight_units':continue
            assert (env[a] if isinstance(a,str) else a)==(env[b] if isinstance(b,str) else b)
        assert env['range_H']&env['range_M']==env['range_Z']
        assert env['controller__edge_word']==sum(E[e]*P**pos for e,pos in packet['packed_edge_exponents'].items())
        results.append(dict(controller_mask=reuse,compute_length=comp,duration=len(word),
                            same_physical_trace=True,all_outer_comparisons_and_AND=True))
    return dict(fixtures=results,scope='Genuine physical path with permuted packed lanes; native placeholders are not Pell zeros. Full fresh native extension is proved parametrically.')


def verify():
    return dict(status='PASS_GROUP_PROJECTIVE_LABEL_ALIGNED_LANES',source=source_checks(),
                degrees=degree_checks(),positive_paths=positive_path_checks(),
                scope='Same fixed-m ordinary-input existential predicate, with fresh native witnesses. '
                      'No physical action order, edge ID, state-flow equation or source scale changes. '
                      'Current compiler is a no-increase fallback; numerical universal alphabet remains uninstantiated.')


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--write',action='store_true');args=parser.parse_args()
    result=json.loads(json.dumps(verify()));path=Path(__file__).with_suffix('.json')
    if args.write:path.write_text(json.dumps(result,indent=2)+'\n')
    else:assert json.loads(path.read_text())==result,'receipt mismatch'
    print(result['status'])
