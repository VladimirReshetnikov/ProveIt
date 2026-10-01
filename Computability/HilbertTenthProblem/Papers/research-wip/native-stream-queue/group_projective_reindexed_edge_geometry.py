"""Move non-idle controller lanes down one place, optionally halving geometry.

The physical table and positive edge coordinate names stay unchanged.  The
new subset word uses explicitly recorded exponents; no identity of old and
new native tuples is asserted.  The parent is retained on its other pack plan.
"""
import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import random

import sympy as sp
import group_projective_idle_free_paths as parent

execute = parent.execute
residuals = parent.residuals


def rewrite(old):
    assert old['idle_free_paths']
    n = old['active_edges']-1
    coordinates = [f'controller__edge_hat{e}' for e in range(1,n+1)]
    base = dict(old, reindexed_edge_geometry=True, old_geometry_m=old['m'],
                controller_edge_coordinates=coordinates,
                packed_edge_exponents={e:e for e in range(1,n+1)})
    if not n or old['idle_free_plan'] != 'factored non-idle':
        return dict(base, reindexed_edges=False, geometry_halved=False,
                    reindexed_saving=dict(M=0,A=0,operations=0),
                    reindexed_removed_registers=[], reindexed_aliases={})
    rows = {row[0]:row for row in old['source']}
    P = 'controller__geometry_power' if old['compute_length'] else 'P'
    word,inner = 'controller__edge_word','idle_free_inner_word'
    assert rows[word] == (word,'*',P,inner)
    assert rows[inner][1] == '-'
    assert {name for name,_,a,b in old['source'] if inner in (a,b)} == {word}
    assert not any(inner in pair for pair in old['comparisons'])
    aliases={inner:word}; removed={word}; replacements={inner:(word,*rows[inner][1:])}
    halved = (n>=2 and n&(n-1)==0 and old['m']==2*n
               and (not old['controller_mask'] or n>=8))
    m=n if halved else old['m'];h=m.bit_length()-1
    scale_exponent=2*m+10 if old['controller_mask'] else m+18

    def power(j):
        if not j:return P
        name=f'controller__lane_power{j}'
        previous=P if j==1 else f'controller__lane_power{j-1}'
        assert rows[name]==(name,'*',previous,previous)
        return name

    def repunit(j):
        if j==1:
            name='controller__lane_factor0'
            assert rows[name]==(name,'+',P,1)
            return name
        name=f'controller__lane_repunit{j-1}'
        assert rows[name]==(name,'*',repunit(j-1),f'controller__lane_factor{j-1}')
        return name

    if halved:
        assert rows['controller__origin_mask']==('controller__origin_mask','*','computed_J',repunit(old['h']))
        replacements['controller__origin_mask']=('controller__origin_mask','*','computed_J',repunit(h))
        powers={P:1}
        for name,op,a,b in old['source']:
            if op=='*' and a in powers and b in powers:powers[name]=powers[a]+powers[b]
        P8,old_Pm=rows['joint_scale'][2:]
        assert rows['joint_scale'][1]=='*' and powers[P8]==8 and powers[old_Pm]==old['m']
        new_Pm=power(h)
        replacements['joint_scale']=('joint_scale','*',P8,new_Pm)
        if old['controller_mask']:
            assert rows['range_body_scale']==('range_body_scale','*','joint_scale',old_Pm)
            replacements['range_body_scale']=('range_body_scale','*','joint_scale',new_Pm)
        if old_Pm=='joint_Pm':
            assert rows[old_Pm]==(old_Pm,'*',power(old['h']-1),power(old['h']-1))
            allowed={'joint_scale'} | ({'range_body_scale'} if old['controller_mask'] else set())
            assert {name for name,_,a,b in old['source'] if old_Pm in (a,b)}==allowed
            assert not any(old_Pm in pair for pair in old['comparisons'])
            removed.add(old_Pm)

    source=[]
    for name,op,a,b in old['source']:
        if name in removed:continue
        source.append(replacements.get(name,(name,op,aliases.get(a,a),aliases.get(b,b))))
    # Only now-private dyadic geometry gates are candidates for deletion.
    candidates={name for name in rows if name.startswith(
        ('controller__lane_power','controller__lane_factor','controller__lane_repunit'))}
    while True:
        used={v for _,_,a,b in source for v in (a,b) if isinstance(v,str)}
        used.update(v for pair in old['comparisons'] for v in pair if isinstance(v,str))
        dead={row[0] for row in source if row[0] in candidates and row[0] not in used}
        if not dead:break
        removed.update(dead);source=[row for row in source if row[0] not in dead]
    counts=Counter('M' if op=='*' else 'A' for _,op,_,_ in source)
    saving=dict(M=old['multiplications']-counts['M'],A=old['additions_subtractions']-counts['A'],
                operations=old['operations']-len(source))
    expected=dict(M=3,A=1,operations=4) if halved and n>=8 else dict(M=1,A=0,operations=1)
    assert saving==expected,(n,old['m'],saving,expected)
    assert old['comparisons']==base['comparisons'] and old['auxiliaries']==base['auxiliaries']
    return dict(base,source=source,m=m,h=h,scale_exponent=scale_exponent,
        operations=len(source),multiplications=counts['M'],additions_subtractions=counts['A'],
        reindexed_edges=True,geometry_halved=halved,reindexed_saving=saving,
        reindexed_removed_registers=sorted(removed|{inner}),reindexed_aliases=aliases,
        packed_edge_exponents={e:e-1 for e in range(1,n+1)},
        lane_edges=list(old['edges'][1:n+1])+[(0,0,0)]*(m-n))


def build(codes,alpha=24,beta=12,variant='joint',controller_mask=False,compute_length=False):
    return rewrite(parent.build(codes,alpha,beta,variant,controller_mask,compute_length))


def polynomial_source(packet):return parent.polynomial_source(packet)


def degree_top(packet,weights):
    if not packet['reindexed_edges']:return parent.degree_top(packet,weights)
    # Degree-only relabeling: coordinate e keeps its source name, but occupies
    # lane e-1.  Skip the parent's old fixed-idle weight specializations.
    n=packet['active_edges']-1;expanded=dict(weights)
    for lane in range(packet['m']):
        expanded[f'controller__edge_hat{lane}']=(weights[f'controller__edge_hat{lane+1}'] if lane<n else 0)
    view=dict(packet,edges=packet['lane_edges'])
    return parent.parent.parent.degree_top(view,expanded)


def source_checks():
    rng=random.Random(2602240);records=[];cases=signed=0;example=None
    tables=[(),((1,),),((1,),(2,)),((1,2,3),),((1,2),(3,4)),
            (tuple(range(1,8)),),(tuple(range(1,9)),),
            ((1,2,3,4,5,6,7,8,1,2),), (tuple(range(1,9))*2,),
            ((1,2,3),(4,5),(6,7,8)), (tuple(range(1,9))*4,)]
    for codes in tables:
      for variant in ('four','six','shifted','strong','joint'):
       for reuse in (False,True):
        if reuse and parent.build(codes,alpha=120)['m']<8:continue
        for comp in (False,True):
            alpha=120 if sum(map(len,codes))>16 else 24
            old=parent.build(codes,alpha=alpha,beta=12,variant=variant,controller_mask=reuse,compute_length=comp)
            packet=rewrite(old);source,out=polynomial_source(packet)
            assert packet['comparisons']==old['comparisons'] and packet['auxiliaries']==old['auxiliaries']
            for case in range(16):
                positive=case<12
                values={name:rng.randrange(1,5) if positive else rng.randrange(-2,3)
                        for name in packet['parameters']+packet['auxiliaries']}
                env=execute(source,values);before=execute(old['source'],values)
                if not packet['reindexed_edges']:
                    assert residuals(packet,env)==residuals(old,before)
                else:
                    P=env['controller__geometry_power'] if comp else values['P']
                    n=packet['active_edges']-1;m=packet['m'];J=env['computed_J']
                    word=sum((values[f'controller__edge_hat{e}']-1)*P**(e-1) for e in range(1,n+1))
                    mask=J*sum(P**i for i in range(m))
                    Hb,Mb,Zb=(env['selection__'+tag+'batch'] for tag in ('H','M','Z'))
                    T=P**(m+8);T2=P**(2*m+8 if reuse else m+16)
                    range_mask=(2*env['D']-1)*(mask if reuse else J*sum(P**i for i in range(8)))
                    H=Hb+P**8*word+T*Hb+T2*env['B']
                    M=Mb+P**8*mask+T*range_mask+T2*(env['B']-1)
                    Z=Zb+P**8*word+T*Hb
                    assert (env['controller__edge_word'],env['controller__origin_mask'])==(word,mask)
                    assert before['controller__edge_word']==P*word
                    assert (env['range_H'],env['range_M'],env['range_Z'],env['selection__q'])==(H,M,Z,16*P**packet['scale_exponent'])
                    # Independent old-source replay at precisely the changed
                    # scalar interface, then recompute every downstream gate.
                    overrides={'controller__edge_word':word,'controller__origin_mask':mask,
                               'joint_scale':T,'range_body_scale':T2}
                    probe=dict(values)
                    for name,op,a,b in old['source']:
                        if name in overrides:probe[name]=overrides[name];continue
                        aa=probe[a] if isinstance(a,str) else a;bb=probe[b] if isinstance(b,str) else b
                        probe[name]=aa*bb if op=='*' else aa+bb if op=='+' else aa-bb
                    assert residuals(packet,env)==residuals(old,probe)
                    oldfinal,oldout=parent.polynomial_source(old)
                    for name,op,a,b in oldfinal[old['operations']:]:
                        aa=probe[a] if isinstance(a,str) else a;bb=probe[b] if isinstance(b,str) else b
                        probe[name]=aa*bb if op=='*' else aa+bb if op=='+' else aa-bb
                    assert env[out]==probe[oldout]
                cases+=1;signed+=not positive
            weights={name:1+i%3 for i,name in enumerate(packet['parameters']+packet['auxiliaries'])}
            weights['selection__tau_gap']=1
            for e,name in enumerate(packet['controller_edge_coordinates']):weights[name]=1<<e
            degree,top=degree_top(packet,weights)[:2];assert top!=0
            counts=Counter('M' if op=='*' else 'A' for _,op,_,_ in source)
            records.append(dict(codes=codes,old_m=old['m'],m=packet['m'],variant=variant,
                controller_mask=reuse,compute_length=comp,reindexed=packet['reindexed_edges'],
                halved=packet['geometry_halved'],saving=packet['reindexed_saving'],
                certificate_operations=packet['operations'],polynomial_operations=len(source),
                polynomial_M=counts['M'],polynomial_A=counts['A'],equations=packet['equations'],
                positive_witnesses=packet['positive_witnesses'],exact_degree=degree))
            if codes==tables[7] and variant=='joint' and reuse and comp:
                example=dict(packet,polynomial_finalizer=source[packet['operations']:],polynomial_output=out)
                assert (packet['operations'],len(source),counts['M'],counts['A'],degree)==(243,260,112,148,3504)
    return dict(records=records,source_example=example,scalar_interface_and_full_output_cases=cases,signed_cases=signed)


def degree_checks():
    # Exact univariate certificate factors and small outer sums.  Never expand
    # the several-thousand-degree full product merely to square it again.
    results=[];t=sp.Symbol('t')
    for n,reuse,comp in ((2,False,False),(4,False,True),(8,False,False),(8,True,True),(10,True,True),(16,True,True)):
        packet=build((tuple(1+i%8 for i in range(n)),),controller_mask=reuse,compute_length=comp)
        names=packet['parameters']+packet['auxiliaries']
        w={name:1+i%3 for i,name in enumerate(names)};w['selection__tau_gap']=1
        for e,name in enumerate(packet['controller_edge_coordinates']):w[name]=1<<e
        values={name:sp.Poly(w[name]*t+i+1,t) for i,name in enumerate(names)}
        factors=['first_unit','selection__R15','selection__P17','index_unit',
                 'linear_unit','strong_unit','joint_bound_unit']
        rows={row[0]:row for row in packet['source']};needed=set()
        def visit(name):
            if not isinstance(name,str) or name not in rows or name in needed:return
            needed.add(name);visit(rows[name][2]);visit(rows[name][3])
        for name in factors:visit(name)
        for pair in packet['comparisons']:
            if pair!=('eight_units',1):
                for name in pair:visit(name)
        env=execute([row for row in packet['source'] if row[0] in needed],values)
        expected_degree,expected_top,parts=degree_top(packet,w)
        def value(a):return env[a] if isinstance(a,str) else sp.Poly(a,t)
        outer=[value(a)-value(b) for a,b in packet['comparisons'] if (a,b)!=('eight_units',1)]
        od=max(v.degree() for v in outer)
        outer_top=sum(v.LC()**2 for v in outer if v.degree()==od)
        unit_degree=sum(env[name].degree() for name in factors)
        unit_top=1
        for name in factors:unit_top*=env[name].LC()
        actual_degree=unit_degree+2*od
        actual_top=unit_top*outer_top
        assert (actual_degree,actual_top)==(expected_degree,expected_top)
        unsigned=abs(int(actual_top));encoded=unsigned.to_bytes((unsigned.bit_length()+7)//8,'big')
        digest=hashlib.sha256(encoded).hexdigest()
        results.append(dict(n=n,m=packet['m'],controller_mask=reuse,compute_length=comp,
                            degree=actual_degree,unit_degree=unit_degree,
                            outer_residual_degree=od,leading_coefficient_sha256=digest))
    return results


def positive_path_checks():
    model=parent.margin.parent.parent.parent;physical=model.physical
    word=model.reflect_codes((physical.target_word(36),))[0];states=model.trace(word,37)
    assert states[0]==[1,37,1,37] and states[-1]==[0,1,0,1]
    D=1<<(max(37,1+max(abs(v) for row in states for v in row))).bit_length()
    B=16*D;P=B**len(word);J=(P-1)//(B-1)
    rows=[[D-1+v for v in row] for row in states[:-1]]
    H=[sum(row[i]*B**j for j,row in enumerate(rows)) for i in range(4)]
    Z=[sum((label==i+1)*rows[j][(i//2)^1]*B**j for j,label in enumerate(word)) for i in range(8)]
    E=[sum((label==i)*B**j for j,label in enumerate(word)) for i in range(1,9)]
    results=[]
    for reuse in (False,True):
      for comp in (False,True):
        packet=build(tuple((i,) for i in range(1,9)),controller_mask=reuse,compute_length=comp)
        values={name:1 for name in packet['parameters']+packet['auxiliaries']}
        values.update(height_slack=D-37,selection__bound_global=P-sum(H)-sum(Z)-7)
        if not comp:values['P']=P
        values.update({f'H{i}':v for i,v in enumerate(H)})
        values.update({f'Zhat{i}':v+1 for i,v in enumerate(Z)})
        values.update({f'controller__edge_hat{i+1}':v+1 for i,v in enumerate(E)})
        assert min(values.values())>0
        env=execute(packet['source'],values)
        assert env['computed_J']==J and env['joint_bound_unit']==1 and packet['m']==8
        for a,b in packet['comparisons']:
            if a=='eight_units':continue
            assert (env[a] if isinstance(a,str) else a)==(env[b] if isinstance(b,str) else b)
        assert env['range_H']&env['range_M']==env['range_Z']
        assert env['controller__edge_word']==sum(v*P**i for i,v in enumerate(E))
        results.append(dict(m=8,old_m=16,controller_mask=reuse,compute_length=comp,
                            duration=len(word),positive_outer_and_scalar_AND=True))
    return dict(fixtures=results,scope='Genuine signed-shear path and complete outer scalar/AND checks. Placeholder native coordinates are not claimed Pell zeros; the theorem supplies the positive native extension.')


def verify():
    return dict(status='PASS_GROUP_PROJECTIVE_REINDEXED_EDGE_GEOMETRY',source=source_checks(),
                degrees=degree_checks(),positive_paths=positive_path_checks(),
                scope='Same ordinary-input existential predicate with fresh native witnesses; literal scalar interfaces and paid gates audited. No numerical universal alphabet instantiated.')


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--write',action='store_true');args=parser.parse_args()
    result=json.loads(json.dumps(verify()));path=Path(__file__).with_suffix('.json')
    if args.write:path.write_text(json.dumps(result,indent=2)+'\n')
    else:assert json.loads(path.read_text())==result,'receipt mismatch'
    print(result['status'])
