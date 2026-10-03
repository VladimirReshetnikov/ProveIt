"""Share the physical selector pack with the controller's edge packing.

Every chosen rewrite is a polynomial identity on the complete supplied
coordinates. A literal paid planner retains the parent when no anchor
offset gives a cheaper source.
"""
import argparse
from collections import Counter
import json
from pathlib import Path
import random

import group_projective_idle_free_paths as parent

execute=parent.execute
residuals=parent.residuals


def trim(a):
    a=list(a)
    while len(a)>1 and not a[-1]:a.pop()
    return tuple(a)


def padd(a,b,sign=1):
    return trim((a[i] if i<len(a) else 0)+sign*(b[i] if i<len(b) else 0)
                for i in range(max(len(a),len(b))))


def pmul(a,b):
    result=[0]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b):result[i+j]+=x*y
    return trim(result)


def monomial(e):return (0,)*e+(1,)


def linear_audit(source,root,P,variables):
    rows={n:(op,a,b) for n,op,a,b in source}
    cache={P:{None:(0,1)},**{n:{n:(1,)} for n in variables}}
    def visit(value):
        if isinstance(value,int):return {None:(value,)} if value else {}
        if value in cache:return cache[value]
        op,a,b=rows[value];a,b=visit(a),visit(b)
        if op in ('+','-'):
            out={key:padd(a.get(key,(0,)),b.get(key,(0,)),1 if op=='+' else -1) for key in a.keys()|b.keys()}
        else:
            if a.keys() <= {None}:a,b=b,a
            assert b.keys() <= {None}, 'unexpected product of two edge-dependent expressions'
            out={key:pmul(poly,b.get(None,(0,))) for key,poly in a.items()}
        cache[value]={key:poly for key,poly in out.items() if poly!=(0,)}
        return cache[value]
    return visit(root)


def rewrite(old):
    assert old['idle_free_paths']
    n=old['active_edges']-1
    if not n:
        return dict(old,shared_selector_pack=True,shared_selector_saving=dict(M=0,A=0,operations=0),
                    shared_selector_plan='empty-table fallback')
    rows={name:(name,op,a,b) for name,op,a,b in old['source']}
    P='controller__geometry_power' if old['compute_length'] else 'P'
    selector='selection__Sbatch';word='controller__edge_word'
    # The coordinate names remain physical edge IDs even when later packets
    # reindex their controller lanes. Default parent uses positions1,...,n.
    positions=old.get('packed_edge_exponents',
                      old.get('controller_edge_positions',{e:e for e in range(1,n+1)}))
    positions={int(e):v for e,v in positions.items()}
    assert set(positions)==set(range(1,n+1)) and len(set(positions.values()))==n
    assert min(positions.values())>=0
    variables=[f'controller__edge_hat{e}' for e in range(1,n+1)]
    labels={e:old['edges'][e][2]-1 for e in range(1,n+1)}
    assert all(0<=label<8 for label in labels.values())
    selector_expected={f'controller__edge_hat{e}':monomial(labels[e]) for e in labels}
    controller_expected={f'controller__edge_hat{e}':monomial(positions[e]) for e in labels}
    for expected in (selector_expected,controller_expected):
        constant=(0,)
        for poly in expected.values():constant=padd(constant,poly,-1)
        expected[None]=constant
    assert linear_audit(old['source'],selector,P,variables)==selector_expected
    assert linear_audit(old['source'],word,P,variables)==controller_expected
    private={name for name in rows if name.startswith(('controller__edge_pack_',
        'frozen_idle_pack_','frozen_idle_R','idle_free_pack_','idle_free_R'))}
    private.update(name for name in ('idle_free_inner_word',) if name in rows)
    assert word in rows
    assert all({user for user,_,a,b in old['source'] if name in (a,b)}<=private|{word} for name in private)
    assert not any(name in pair for name in private for pair in old['comparisons'])
    removed=private|{word}
    available=[row for row in old['source'] if row[0] not in removed]
    # Discover exact existing P-polynomials outside the private old pack.
    known={P:(0,1)};polynomial_register={(0,1):P}
    max_degree=max(old['m']*2+20,max(positions.values())+15)
    for name,op,a,b in available:
        if name==P:continue
        aa=(a,) if isinstance(a,int) else known.get(a)
        bb=(b,) if isinstance(b,int) else known.get(b)
        if aa is None or bb is None:continue
        if op=='*' and len(aa)+len(bb)-2>max_degree:continue
        poly=pmul(aa,bb) if op=='*' else padd(aa,bb,1 if op=='+' else -1)
        known[name]=poly
        if len(poly)>1:polynomial_register.setdefault(poly,name)
    groups={}
    for e,label in labels.items():groups.setdefault(positions[e]-label,[]).append(e)
    base=min(positions.values())
    anchors=sorted({base}|{offset for offset in groups if offset>=base})
    old_counts=Counter('M' if op=='*' else 'A' for name,op,_,_ in old['source'] if name in removed)
    plans=[]

    def make_plan(anchor):
        added=[];pcache=dict(polynomial_register);counter=0
        def key(op,a,b):
            if op in ('+','*') and repr(a)>repr(b):a,b=b,a
            return op,a,b
        operations={key(op,a,b):name for name,op,a,b in available}
        def emit(op,a,b):
            nonlocal counter
            if isinstance(a,int) and isinstance(b,int):
                return a+b if op=='+' else a-b if op=='-' else a*b
            if op=='+' and a==0:return b
            if op in ('+','-') and b==0:return a
            if op=='*':
                if a==0 or b==0:return 0
                if a==1:return b
                if b==1:return a
            if op=='-' and a==b:return 0
            k=key(op,a,b)
            if k in operations:return operations[k]
            name=f'shared_selector_gate{counter}';counter+=1
            assert name not in rows
            added.append((name,op,a,b));operations[k]=name
            return name
        def polynomial(coefficients):
            coefficients=trim(coefficients)
            if len(coefficients)==1:return coefficients[0]
            if coefficients in pcache:return pcache[coefficients]
            degree=len(coefficients)-1
            split=1<<(degree.bit_length()-1)
            low=polynomial(coefficients[:split])
            high=polynomial(coefficients[split:])
            # Construct an absent monomial by its binary exponent, rather
            # than recursing on itself at the split boundary.
            power=monomial(split)
            if power not in pcache:
                assert split>1
                half=polynomial(monomial(split//2))
                pcache[power]=emit('*',half,half)
            result=emit('+',low,emit('*',pcache[power],high))
            pcache[coefficients]=result
            return result
        total=emit('*',polynomial(monomial(anchor-base)),selector)
        corrections=[]
        for offset,edges in sorted(groups.items()):
            if offset==anchor:continue
            edges=sorted(edges,key=lambda e:labels[e]);lo=labels[edges[0]]
            value=f'controller__edge_hat{edges[-1]}'
            for left,right in zip(reversed(edges[:-1]),reversed(edges[1:])):
                value=emit('+',f'controller__edge_hat{left}',
                           emit('*',polynomial(monomial(labels[right]-labels[left])),value))
            mask=tuple(int(j+lo in {labels[e] for e in edges}) for j in range(labels[edges[-1]]-lo+1))
            group=emit('-',value,polynomial(mask))
            first=offset+lo-base;second=anchor+lo-base
            assert min(first,second)>=0 and first!=second
            coefficient=polynomial(padd(monomial(first),monomial(second),-1))
            correction=emit('*',coefficient,group)
            total=emit('+',total,correction)
            corrections.append(dict(offset=offset,edges=edges,lowest_label=lo,
                                    coefficient_exponents=[first,second]))
        output=emit('*',polynomial(monomial(base)),total)
        # Reuse the designated output register without a paid copy gate.
        aliases={}
        if added and added[-1][0]==output:
            last=added[-1];added[-1]=(word,*last[1:])
        else:
            # A zero-based aligned pack is already exactly Sbatch. Rename
            # its defining gate and all consumers, charging no copy gate.
            assert not added and output in {row[0] for row in available}
            assert not any(output in pair for pair in old['comparisons'])
            aliases[output]=word
        counts=Counter('M' if op=='*' else 'A' for _,op,_,_ in added)
        plan=dict(anchor=anchor,base=base,source=added,operations=len(added),
                  M=counts['M'],A=counts['A'],corrections=corrections)
        if aliases:plan['aliases']=aliases
        return plan

    for anchor in anchors:plans.append(make_plan(anchor))
    chosen=min(plans,key=lambda plan:(plan['operations'],plan['M'],plan['anchor']))
    if chosen['operations']>=len(removed):
        return dict(old,shared_selector_pack=True,shared_selector_saving=dict(M=0,A=0,operations=0),
                    shared_selector_plan='parent fallback',shared_selector_candidates=plans)
    aliases=chosen.get('aliases',{})
    source=[tuple(aliases.get(v,v) if isinstance(v,str) else v for v in row)
            for row in available]+chosen['source']
    source=parent.parent.parent.ports.shared.factored.index.parent.sort_source(source,{'x',*old['auxiliaries']})
    assert linear_audit(source,word,P,variables)==controller_expected
    counts=Counter('M' if op=='*' else 'A' for _,op,_,_ in source)
    saving=dict(M=old_counts['M']-chosen['M'],A=old_counts['A']-chosen['A'],
                operations=len(removed)-chosen['operations'])
    assert len(source)==old['operations']-saving['operations']
    return dict(old,source=source,operations=len(source),multiplications=counts['M'],
                additions_subtractions=counts['A'],shared_selector_pack=True,
                shared_selector_saving=saving,shared_selector_plan='anchor correction',
                shared_selector_anchor=chosen['anchor'],shared_selector_base=base,
                shared_selector_removed_registers=sorted(removed),
                shared_selector_candidates=plans)


def build(codes,alpha=24,beta=12,variant='joint',controller_mask=False,compute_length=False):
    return rewrite(parent.build(codes,alpha,beta,variant,controller_mask,compute_length))


def polynomial_source(packet):return parent.polynomial_source(packet)


def degree_top(packet,weights):return parent.degree_top(packet,weights)


def verify():
    rng=random.Random(2463504);records=[];cases=signed=0;example=None
    tables=[(),((1,),),((8,),),((1,2),),((1,2,3),),((1,2),(3,4)),
            ((8,6,4,2,7,5,3,1),),((1,2,3,4,5,6,7,8,1,2),),
            ((1,),(2,3,4),(5,)),(tuple(1+i%8 for i in range(16)),)]
    for codes in tables:
      for variant in ('four','six','shifted','strong','joint'):
       for reuse in (False,True):
        if reuse and parent.build(codes)['m']<8:continue
        for comp in (False,True):
            old=parent.build(codes,variant=variant,controller_mask=reuse,compute_length=comp)
            packet=rewrite(old);source,out=polynomial_source(packet);prior,prior_out=parent.polynomial_source(old)
            assert packet['comparisons']==old['comparisons'] and packet['auxiliaries']==old['auxiliaries']
            for case in range(24):
                positive=case<16
                values={name:rng.randrange(1,6) if positive else rng.randrange(-3,4)
                        for name in packet['parameters']+packet['auxiliaries']}
                env,before=execute(source,values),execute(prior,values)
                assert all(env[name]==before[name] for name,_,_,_ in source if name in before)
                assert residuals(packet,env)==residuals(old,before) and env[out]==before[prior_out]
                cases+=1;signed+=not positive
            weights={name:1+i%3 for i,name in enumerate(packet['parameters']+packet['auxiliaries'])}
            weights['selection__tau_gap']=1
            degree,top=degree_top(packet,weights)[:2];assert top
            counts=Counter('M' if op=='*' else 'A' for _,op,_,_ in source)
            records.append(dict(codes=codes,m=packet['m'],variant=variant,controller_mask=reuse,
                compute_length=comp,plan=packet['shared_selector_plan'],saving=packet['shared_selector_saving'],
                certificate_operations=packet['operations'],polynomial_operations=len(source),
                polynomial_M=counts['M'],polynomial_A=counts['A'],equations=packet['equations'],
                positive_witnesses=packet['positive_witnesses'],exact_degree=degree))
            if codes==tables[7] and variant=='joint' and reuse and comp:
                example=dict(packet,polynomial_finalizer=source[packet['operations']:],polynomial_output=out)
                assert (packet['operations'],len(source),counts['M'],counts['A'],degree)==(229,246,105,141,3504)
    return dict(status='PASS_GROUP_PROJECTIVE_SHARED_SELECTOR_PACK',records=records,source_example=example,
                complete_source_identity_cases=cases,signed_cases=signed,
                scope='Paid anchor corrections reuse the physical selector pack. Complete integer polynomial identity; no new witness or compiler semantic relaxation. No global circuit optimality or numerical75/88 improvement is claimed.')


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--write',action='store_true');args=parser.parse_args()
    result=json.loads(json.dumps(verify()));path=Path(__file__).with_suffix('.json')
    if args.write:path.write_text(json.dumps(result,indent=2)+'\n')
    else:assert json.loads(path.read_text())==result,'receipt mismatch'
    print(result['status'])
