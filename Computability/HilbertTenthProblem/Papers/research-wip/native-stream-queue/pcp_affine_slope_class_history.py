"""Complete affine histories with selected products only for slope exceptions.

Original tile selectors retain chronological meaning.  Selected histories
are grouped by equal slope, with one baseline class omitted per coordinate.
"""
import argparse
from collections import Counter
import json
from pathlib import Path
import random

import pcp_uniform_affine_pair_history as parent
import pcp_uniform_affine_pair_units as units

execute=parent.execute
scalar=parent.scalar


def classes(maps,coordinate,baseline):
    groups={}
    for i,row in enumerate(maps):groups.setdefault(row[coordinate],[]).append(i)
    assert baseline in groups
    return [dict(slope=slope,difference=slope-baseline,tiles=members)
            for slope,members in sorted(groups.items(),key=lambda item:item[1][0])
            if slope!=baseline]


def emit_forms(g,forms):
    """Simple literal fallback; metadata permits a later exact linear-form pass."""
    outputs=[]
    for number,form in enumerate(forms):
        terms=[g.mul(coefficient,name,f'linear{number}_coefficient')
               for name,coefficient in form['coefficients'].items()]
        outputs.append(g.add(g.total(terms,f'linear{number}_sum'),form['constant'],f'linear{number}_constant'))
    return outputs


def build_raw(maps=parent.DEFAULT_MAPS,*,baseline_U='auto',baseline_V='auto',linear_emitter=None):
    maps=parent.validate_maps(maps)
    choices_U=sorted({row[0] for row in maps}) if baseline_U=='auto' else [baseline_U]
    choices_V=sorted({row[2] for row in maps}) if baseline_V=='auto' else [baseline_V]
    if baseline_U=='auto' or baseline_V=='auto':
        candidates=[build_raw(maps,baseline_U=a,baseline_V=b,linear_emitter=linear_emitter)
                    for a in choices_U for b in choices_V]
        chosen=min(candidates,key=lambda p:(p['operations'],p['multiplications'],p['baselines']))
        return dict(chosen,baseline_candidates=[dict(baselines=p['baselines'],operations=p['operations'],
                       multiplications=p['multiplications'],additions_subtractions=p['additions_subtractions'])
                       for p in candidates])
    groupsU=classes(maps,0,baseline_U);groupsV=classes(maps,2,baseline_V)
    u,v=len(groupsU),len(groupsV);count=u+v;s=len(maps)
    threshold=max(8,s+4,1+max(max(a+c,b+d) for a,c,b,d in maps))
    K=1<<(threshold-1).bit_length()
    g=parent.DAG()
    D=g.total(parent.PARAMETERS+['height_slack'],'height_sum')
    B=g.mul(K,D,'B')
    J=g.sub(g.total([f'Shat{i}' for i in range(s)],'selector_sum'),s,'J')
    Bm1=g.sub(B,1,'Bm1');P=g.add(g.mul(Bm1,J,'P_product'),1,'P')
    g.powers[1]=P
    zhats=[f'ZUhat{i}' for i in range(u)]+[f'ZVhat{i}' for i in range(v)]
    global_lhs=g.add(g.total(['H_U','H_V']+zhats,'global_sum'),'global_bound','global_lhs')
    pairs=[(global_lhs,P)]
    forms=[]
    for tag,base,groups,offset in [('U',baseline_U,groupsU,1),('V',baseline_V,groupsV,3)]:
        coefficients={f'H_{tag}':base}
        coefficients.update({f'Z{tag}hat{i}':entry['difference'] for i,entry in enumerate(groups)})
        coefficients.update({f'Shat{i}':row[offset] for i,row in enumerate(maps) if row[offset]})
        constant=-sum(entry['difference'] for entry in groups)-sum(row[offset] for row in maps)
        forms.append(dict(coefficients=coefficients,constant=constant))
    nextU,nextV=(linear_emitter or emit_forms)(g,forms)
    for form,result in zip(forms,(nextU,nextV)):form['output']=result
    lhsU=g.add(g.mul(B,nextU,'U_update'),1,'U_lhs')
    lhsV=g.add(g.mul(B,nextV,'V_update'),'Vinitial','V_lhs')
    rhsU=g.add('H_U',g.mul(P,'Ufinal','U_terminal'),'U_rhs')
    rhsV=g.add('H_V',g.mul(P,'Vfinal','V_terminal'),'V_rhs')
    pairs += [(lhsU,rhsU),(lhsV,rhsV)]

    S=g.hatpack([f'Shat{i}' for i in range(s)])
    Mc=g.mul(J,g.repunit(s),'controller_mask')
    T=g.add('H_U',g.mul(P,'H_V','range_second_history'),'range_histories')
    hatsU=[];hatsV=[]
    for groups,outputs in ((groupsU,hatsU),(groupsV,hatsV)):
        for entry in groups:
            outputs.append(g.sub(g.total([f'Shat{i}' for i in entry['tiles']],'group_sum'),
                                 len(entry['tiles'])-1,'group_hat'))
    group_hats=hatsU+hatsV
    shared_partition=bool(hatsU) and hatsU==hatsV
    if shared_partition:
        Gpack=g.mul(g.add(1,g.power(u),'shared_group_repeat'),g.hatpack(hatsU),'shared_group_pack')
    else:
        Gpack=g.hatpack(group_hats) if group_hats else 0
    if u==v and u:
        Hb=g.mul(g.add('H_U',g.mul(g.power(u),'H_V','physical_second_history'),'physical_histories'),
                 g.repunit(u),'history_batch')
    else:
        Hu=g.mul('H_U',g.repunit(u),'U_repeated')
        Hv=g.mul('H_V',g.repunit(v),'V_repeated')
        Hb=g.add(Hu,g.mul(g.power(u),Hv,'V_region'),'history_batch')
    Mb=g.mul(Bm1,Gpack,'mask_batch')
    Zb=g.hatpack(zhats) if zhats else 0
    RM=g.mul(g.mul(g.sub(D,1,'range_cell'),J,'range_repunit'),g.add(1,P,'range_duplicate'),'range_mask')
    ec,er,et,N=count,count+s,count+s+2,count+s+4
    common=g.add(g.mul(g.power(ec),S,'controller_region'),g.mul(g.power(er),T,'range_region'),'common_joined')
    H=g.total([Hb,common,g.mul(g.power(et),B,'top_history')],'joined_H')
    M=g.total([Mb,g.mul(g.power(ec),Mc,'controller_mask_region'),
               g.mul(g.power(er),RM,'range_mask_region'),g.mul(g.power(et),Bm1,'top_mask')],'joined_M')
    Z=g.add(Zb,common,'joined_Z');scale=g.power(N)
    wrapper=list(g.source)
    aliases=dict(P=scale,Hhat=H,Mhat=M,Zhat=Z)
    old,pairs_native,_=parent.native.source('and64_prescribed')
    def alias(value):return value if isinstance(value,int) else aliases.get(value,'and__'+value)
    kernel=[]
    for name,op,a,b in old:
        if name in ('padded_A','padded_B','F3'):op,b='+',{'padded_A':12,'padded_B':10,'F3':8}[name]
        kernel.append(('and__'+name,op,alias(a),alias(b)))
    source=wrapper+kernel;pairs += [(alias(a),alias(b)) for a,b in pairs_native]
    native_aux=parent.native.domains('and64_prescribed')[1]
    aux=['height_slack','H_U','H_V','global_bound']+[f'Shat{i}' for i in range(s)]+zhats
    aux += ['and__'+name for name in native_aux]
    names=set(parent.PARAMETERS+aux)
    for name,_,a,b in source:
        assert name not in names and all(not isinstance(value,str) or value in names for value in (a,b))
        names.add(name)
    counts=Counter('M' if op=='*' else 'A' for _,op,_,_ in source)
    assert len(aux)==s+count+26 and len(pairs)==19
    return dict(maps=maps,layout='slope_classes',tiles=s,K=K,baselines=(baseline_U,baseline_V),
                groups_U=groupsU,groups_V=groupsV,selected_products=count,scale_exponent=N,
                source=source,comparisons=pairs,parameters=list(parent.PARAMETERS),auxiliaries=aux,
                operations=len(source),multiplications=counts['M'],additions_subtractions=counts['A'],
                equations=19,witnesses=len(aux),positive_witnesses=len(aux),unit_product=False,
                exact_degree=24*N+16,wrapper_operations=len(wrapper),linear_forms=forms,
                group_hat_registers=group_hats,shared_group_partition=shared_partition,
                native_auxiliaries=native_aux,native_prefix='and__',
                region_exponents=dict(controller=ec,range=er,top=et),
                interfaces=dict(D=D,B=B,J=J,P=P,S=S,Mc=Mc,T=T,Hb=Hb,Mb=Mb,Zb=Zb,
                                Gpack=Gpack,RM=RM,H=H,M=M,Z=Z,scale=scale,nextU=nextU,nextV=nextV))


def build(maps=parent.DEFAULT_MAPS,*,baseline_U='auto',baseline_V='auto',unit_product=True,linear_emitter=None):
    raw=build_raw(maps,baseline_U=baseline_U,baseline_V=baseline_V,linear_emitter=linear_emitter)
    if not unit_product:return raw
    packet=units.rewrite(raw);N=raw['scale_exponent']
    return dict(packet,unit_product=True,raw_packet=raw,exact_degree=58*N+28,alternative_SOS_degree=84*N+16)


def build_from_tiles(tiles,width,**options):return build(parent.maps_from_tiles(tiles,width),**options)


def polynomial_source(packet,*,sum_of_squares=False):
    return (units.polynomial_source(packet,sum_of_squares=sum_of_squares) if packet['unit_product']
            else parent.polynomial_source(packet))


def manual(packet,values):
    assert not packet['unit_product']
    s=packet['tiles'];u=len(packet['groups_U']);v=len(packet['groups_V']);g=u+v
    D=sum(values[name] for name in parent.PARAMETERS)+values['height_slack'];B=packet['K']*D
    selectors=[values[f'Shat{i}']-1 for i in range(s)];J=sum(selectors);P=(B-1)*J+1
    ZU=[values[f'ZUhat{i}']-1 for i in range(u)];ZV=[values[f'ZVhat{i}']-1 for i in range(v)]
    GU=[sum(selectors[i] for i in group['tiles']) for group in packet['groups_U']]
    GV=[sum(selectors[i] for i in group['tiles']) for group in packet['groups_V']]
    pack=lambda row:sum(value*P**i for i,value in enumerate(row))
    S=pack(selectors);Mc=J*sum(P**i for i in range(s))
    T=values['H_U']+P*values['H_V']
    Hb=pack([values['H_U']]*u+[values['H_V']]*v)
    Gpack=pack(GU+GV);Mb=(B-1)*Gpack;Zb=pack(ZU+ZV)
    RM=(D-1)*J*(1+P)
    ec,er,et=[packet['region_exponents'][key] for key in ('controller','range','top')]
    common=P**ec*S+P**er*T
    H=Hb+common+P**et*B
    M=Mb+P**ec*Mc+P**er*RM+P**et*(B-1)
    Z=Zb+common;scale=P**packet['scale_exponent']
    a0,b0=packet['baselines']
    nextU=a0*values['H_U']+sum(group['difference']*z for group,z in zip(packet['groups_U'],ZU))
    nextV=b0*values['H_V']+sum(group['difference']*z for group,z in zip(packet['groups_V'],ZV))
    nextU+=sum(row[1]*selector for row,selector in zip(packet['maps'],selectors))
    nextV+=sum(row[3]*selector for row,selector in zip(packet['maps'],selectors))
    residuals=[values['H_U']+values['H_V']+sum(ZU)+sum(ZV)+g+values['global_bound']-P,
               B*nextU+1-values['H_U']-P*values['Ufinal'],
               B*nextV+values['Vinitial']-values['H_V']-P*values['Vfinal']]
    native_values={name:values['and__'+name] for name in packet['native_auxiliaries']}
    native_values.update(P=scale,Hhat=H+1,Mhat=M+1,Zhat=Z+1)
    old,pairs,_=parent.native.source('and64_prescribed');env=execute(old,native_values)
    residuals += [scalar(a,env)-scalar(b,env) for a,b in pairs]
    return residuals,dict(D=D,B=B,J=J,P=P,S=S,Mc=Mc,T=T,Hb=Hb,Mb=Mb,Zb=Zb,
                          Gpack=Gpack,RM=RM,H=H,M=M,Z=Z,scale=scale,nextU=nextU,nextV=nextV)


def positive_outer_fixture(packet,selection,Vinitial=1):
    raw=packet['raw_packet'] if packet['unit_product'] else packet
    assert selection and Vinitial>0
    U,V=1,Vinitial;historyU=[];historyV=[]
    for tile in selection:
        assert 0<=tile<raw['tiles']
        historyU.append(U);historyV.append(V)
        a,c,b,d=raw['maps'][tile];U,V=a*U+c,b*V+d
    total=Vinitial+U+V;D=1<<total.bit_length();B=raw['K']*D;P=B**len(selection)
    pack=lambda row:sum(value*B**j for j,value in enumerate(row))
    values=dict(Vinitial=Vinitial,Ufinal=U,Vfinal=V,height_slack=D-total,
                H_U=pack(historyU),H_V=pack(historyV))
    for i in range(raw['tiles']):values[f'Shat{i}']=pack([int(tile==i) for tile in selection])+1
    zsum=0
    for tag,groups,hist in [('U',raw['groups_U'],historyU),('V',raw['groups_V'],historyV)]:
        for i,group in enumerate(groups):
            value=pack([x if tile in group['tiles'] else 0 for tile,x in zip(selection,hist)])
            values[f'Z{tag}hat{i}']=value+1;zsum+=value+1
    values['global_bound']=P-values['H_U']-values['H_V']-zsum
    values.update({'and__'+name:1 for name in raw['native_auxiliaries']})
    rr,face=manual(raw,values)
    assert rr[:3]==[0,0,0] and face['P']==P and face['H']&face['M']==face['Z']
    fields=parent.native.parent.truth_fields(face['scale'],face['H'],face['M'])
    values.update({f'and__F{i}':fields[i] for i in range(3)})
    if packet['unit_product']:
        values={name:values[name] for name in packet['parameters']+packet['auxiliaries'] if name in values}
        values['and__tau_gap']=1
    assert all(value>0 for value in values.values())
    env=execute(packet['source'],values)
    assert all(scalar(a,env)==scalar(b,env) for a,b in packet['comparisons'][:3])
    assert env['and__F3']==fields[3]
    return values


def ledger(packet):
    keys=('tiles','baselines','selected_products','scale_exponent','unit_product','operations',
          'multiplications','additions_subtractions','equations','witnesses','exact_degree')
    answer={key:packet[key] for key in keys};e=packet['equations']
    answer['polynomial']=dict(operations=packet['operations']+3*e-1,
        multiplications=packet['multiplications']+e,additions_subtractions=packet['additions_subtractions']+2*e-1)
    if packet['unit_product']:answer['alternative_SOS_degree']=packet['alternative_SOS_degree']
    return answer


def verify():
    tables=[((1,0,1,0),),((3,1,5,0),(3,0,5,2)),parent.DEFAULT_MAPS,
            ((2,0,4,1),(2,1,4,0),(8,3,16,5),(8,0,16,1)),
            ((2,0,2,0),(4,1,8,1),(8,2,4,2),(2,3,8,3))]
    rng=random.Random(32643);records=[];rawcases=unitcases=outer=0
    for maps in tables:
      for a0 in sorted({row[0] for row in maps}):
       for b0 in sorted({row[2] for row in maps}):
        raw=build_raw(maps,baseline_U=a0,baseline_V=b0)
        new=build(maps,baseline_U=a0,baseline_V=b0)
        records += [ledger(raw),ledger(new)]
        for p in (raw,new):
            source,out=polynomial_source(p);histogram=Counter('M' if op=='*' else 'A' for _,op,_,_ in source)
            expected=ledger(p)['polynomial']
            assert len(source)==expected['operations']
            assert histogram==dict(M=expected['multiplications'],A=expected['additions_subtractions'])
        for case in range(24):
            values={name:rng.randrange(1,5) if case<16 else rng.randrange(-3,4)
                    for name in raw['parameters']+raw['auxiliaries']}
            rr,face=manual(raw,values);source,out=polynomial_source(raw);env=execute(source,values)
            assert rr==[scalar(a,env)-scalar(b,env) for a,b in raw['comparisons']]
            assert env[out]==sum(r*r for r in rr)
            assert all(scalar(raw['interfaces'][key],env)==value for key,value in face.items())
            if case<16:assert face['P']>=1 and min(face[key] for key in ('H','M','Z'))>=0
            rawcases+=1
            v={name:rng.randrange(1,5) if case<16 else rng.randrange(-3,4)
               for name in new['parameters']+new['auxiliaries']}
            if case<16:v[new['root_coordinate']]=2*rng.randrange(1,5)+1
            units.audit_identity(raw,new,v);unitcases+=1
        for case in range(12):
            selection=tuple(rng.randrange(len(maps)) for _ in range(1+case%5))
            for p in (raw,new):positive_outer_fixture(p,selection,1+case%3);outer+=1
      automatic=build_raw(maps)
      assert automatic['operations']==min(p['operations'] for p in automatic['baseline_candidates'])
    # A concrete compiled nonuniversal program, retaining its actual tile order.
    import gpcp_complete_fixed_program as complete
    old=complete.odd_machine()['history_packet'];large=build(old['maps'])
    comparisons=dict(parent_raw_operations=old['operations'],parent_scale_exponent=old['scale_exponent'],
                     parent_unit_polynomial=old['operations']+32,new=ledger(large))
    sample=build(parent.DEFAULT_MAPS)
    degrees=[]
    for maps in tables[:3]:
        raw=build_raw(maps);new=build(maps)
        degrees.append(parent.degree_check(raw));degrees.append(units.degree_audit(new))
    return dict(status='PASS_PCP_AFFINE_SLOPE_CLASS_HISTORY',ledgers=records,
        illustrative_actual_program=comparisons,
        example=dict(ledger=ledger(sample),groups_U=sample['groups_U'],groups_V=sample['groups_V'],
            parameters=sample['parameters'],auxiliaries=sample['auxiliaries'],source=sample['source'],
            comparisons=sample['comparisons'],linear_forms=sample['linear_forms']),
        checks=dict(raw_full_residual_SOS_identities=rawcases,unit_full_restoration_identities=unitcases,
                    genuine_outer_paths=outer,full_Pell_witnesses_materialized=False),
        degree_audits=degrees,
        scope='Complete nonempty common affine-tile word relation for every fixed positive-slope table; '
              'fresh native witnesses follow from the scalar AND theorem. No numerical universal table.')


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--write',action='store_true');args=parser.parse_args()
    result=json.loads(json.dumps(verify()));path=Path(__file__).with_suffix('.json')
    if args.write:path.write_text(json.dumps(result,indent=2)+'\n')
    else:assert json.loads(path.read_text())==result,'receipt mismatch'
    print(result['status'])
