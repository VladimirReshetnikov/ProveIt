#!/usr/bin/env python3
"""Fresh static source review and independent scalar formula checks only."""
import hashlib
import json
from pathlib import Path

ROOT = Path('/home/codex/.codex/worktrees/2a71/Proofs')
WIP = ROOT/'Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue'
AUTHOR = Path('/tmp/neary_woods_hierarchical_history250_tesla')

def require(v, s):
    if not v:
        raise RuntimeError(s)

def digest(data):
    return hashlib.sha256(data).hexdigest()

def pin(p):
    b=p.read_bytes()
    return dict(path=str(p), sha256=digest(b), bytes=len(b))

def canonical(v):
    return json.dumps(v, sort_keys=True, separators=(',', ':')).encode()

def static(parent, child):
    old=parent['source']; new=child['source']
    remove={'hist__pack_product__44','hist__pack_sum__45',
        'hist__repunit_product__53','shared_history_selector_high',
        'hist__pack_sum__49','hist__unhat_pack__54',
        'hist__controller_mask__55','hist__P7__81'}
    replace={
        'hist__range_region__82':['hist__range_region__82','*','hist__P6__80','hist__range_histories__57'],
        'hist__P9__86':['tree_P8','*','hist__P6__80','hist__P2__51'],
        'hist__top_history__87':['hist__top_history__87','*','hist__B__3','tree_P8'],
        'hist__range_mask_region__91':['hist__range_mask_region__91','*','hist__P6__80','hist__range_mask__77'],
        'hist__top_mask__92':['hist__top_mask__92','*',2,'tree_P8'],
        'hist__controller_region__79':['hist__controller_region__79','*','hist__P3__78','hist__unhat_pack__65'],
        'hist__joined_M__95':['hist__joined_M__95','+','hist__joined_M__94','tree_P8'],
    }
    addition=[
        ['tree_group12','-','hist__group_sum__58',2],
        ['tree_mask_product','*','hist__P_product__9','tree_group12'],
        ['tree_mask_sum','+','hist__J__7','tree_mask_product'],
        ['tree_mask_shift','*','hist__P__10','tree_mask_sum'],
        ['hist__controller_mask__55','+','hist__J__7','tree_mask_shift'],
    ]
    expected=[]
    for row in old:
        if row[0] in remove:
            continue
        if row[0]=='hist__controller_region__79':
            expected.extend(addition)
        expected.append(replace.get(row[0],row))
    require(expected==new,'complete static reconstruction')
    require(len(old)==253 and len(new)==250,'row totals')
    for key in ['parameters','auxiliaries','domains','comparisons','unit_factors',
                'merged','fixed_numeral_recipes','fixed_u9_recipe','output']:
        require(parent[key]==child[key],'interface '+key)
    old_by={r[0]:r for r in old}; new_by={r[0]:r for r in new}
    require(all(old_by[k]==new_by[k] for k in child['unit_factors']),'factor rows')
    require(old[-18:]==new[-18:],'whole finalizer tail')
    private=[x for x in child['auxiliaries'] if x.startswith('and__')]
    require(len(private)==12 and len(child['auxiliaries'])==43,'private scope')
    known=set(child['parameters']+child['auxiliaries']); fixed=set()
    consumers={n:[] for n in known}
    for row in new:
        name,op,left,right=row
        require(op in ['+','-','*'] and name not in known,'fresh binary operation')
        for operand in [left,right]:
            if isinstance(operand,str):
                require(operand in known,'topological input')
                consumers.setdefault(operand,[]).append(name)
            elif isinstance(operand,dict):
                require(set(operand)=={'fixed_numeral'},'numeral syntax')
                fixed.add(operand['fixed_numeral'])
            else:
                require(type(operand) is int,'integer literal')
        known.add(name)
    require(fixed==set(child['fixed_numeral_recipes']) and len(fixed)==11,'numerals')
    require(all(all(y.startswith('and__') for y in consumers[x]) for x in private),'private leaf consumers')
    pending=[child['output']]; live=set()
    while pending:
        n=pending.pop()
        if n in live: continue
        live.add(n)
        if n in new_by:
            pending.extend(x for x in new_by[n][2:] if isinstance(x,str))
    require(known<=live,'complete gate and port liveness')
    m=sum(r[1]=='*' for r in new)
    require((m,len(new)-m)==(130,120),'operation ledger')
    unchanged=[r for r in old if r[0] not in remove|set(replace)]
    require(len(unchanged)==238 and all(new_by[r[0]]==r for r in unchanged),'literal retention')
    return dict(merged=child['merged'],parent_rows=253,child_rows=250,
        literal_rows=238,removed_rows=8,added_rows=5,edited_rows=7,
        M=m,A=len(new)-m,positive_witnesses=43,
        ordinary_plus_program_ports=len(child['parameters']),fixed_numeral_roles=11,
        all_gates_and_ports_live=True,private_joint_witnesses=private,
        retained_witnesses=31,source_sha256=digest(canonical(new)))

def partition_controls():
    total=valid=0
    for J in range(32):
        for group in range(J+1):
            for S0 in range(J-group+1):
                for S1 in range(group+1):
                    S=(S0,S1,group-S1,J-group-S0)
                    tree=(group&J)==group and (S0&(J-group))==S0 and (S1&group)==S1
                    bit_oracle=all(sum((s>>j)&1 for s in S)==((J>>j)&1)
                                   for j in range(max(1,J.bit_length())))
                    require(tree==bit_oracle,'independent bit-occupancy oracle')
                    total+=1;valid+=tree
    return dict(J_inclusive=[0,31],tuples=total,partitions=valid)

def signed_controls():
    total=negative=height_one=0
    for height in [1,2,7]:
        b=32*height
        for J in range(1,9):
            selectors=set()
            for i in range(4):
                for j in range(4):
                    s=[0]*4;s[i]+=J//2;s[j]+=J-J//2
                    selectors.add(tuple(s))
            for epsilon in [-1,1]:
                P=(b-1)*J+epsilon
                for s in sorted(selectors):
                    group=s[1]+s[2]
                    ctl=group+P*s[0]+P*P*s[1]
                    mask=J+P*(J+(b-1)*J*group)
                    require(mask==J+P*(s[0]+s[3]+(1-epsilon)*group)+P*P*group,'negative-sign expansion')
                    require(mask+2<P**3 and ctl<P**3,'controller bounds')
                    for i in range(6):
                        for j in range(i+1,6):
                            values=[1]*6
                            values[i]+=(P-6)//2
                            values[j]+=P-6-(P-6)//2
                            hu,hv,zu,zv0,zv1,beta=values
                            require(sum(values)==P and beta>0,'positive global sum')
                            hb=hu+P*hv+P*P*hv
                            zb=zu-1+P*(zv0-1)+P*P*(zv1-1)
                            mb=(b-1)*ctl
                            hr=hu+P*hv; mr=(height-1)*J*(1+P)
                            T=P**8
                            H0=hb+P**3*ctl+P**6*hr
                            M0=mb+P**3*mask+P**6*mr
                            Z=zb+P**3*ctl+P**6*hr
                            H=H0+2*T;M=M0+T;Q=b*T
                            require(0<=H0<T and 0<=M0<T and 0<=Z<T,'full lower bounds')
                            require(H-Z>=T+1 and M-Z>=1 and Q-H-M+Z>=(b-5)*T+2,'truth-field margins')
                            total+=1;negative+=epsilon==-1;height_one+=height==1
    return dict(cases=total,negative_sign=negative,height_one=height_one,
                scope='Handwritten scalar pretyping formulas, no compiler zeros')

def hand_degrees():
    # Independently derived by hand from the displayed producer cones.
    # No row loop propagates degree or evaluates a saved expression.
    joint={'and__R15':129,'and__P17':322,'and__first_unit':73,
           'and__f_square_minus_one':178,'and__index_unit':57,'and__linear_unit':57}
    unchanged={'geo__R15':14,'geo__P17':40,'geo__first_unit':9,
        'geo__f_square_minus_one':24,'geo__index_unit':6,'geo__linear_unit':6,
        'mask_repunit_unit':4,'history_upper_unit':2,'history_global_unit':2,'lower_history_unit':3}
    require(sum(unchanged.values())==110 and sum(joint.values())+110==926,'hand sum')
    return dict(joint=joint,unchanged=unchanged,total=926,
                exact_degree=False,saved_array_degree_propagation=False)

def main():
    child=json.loads(AUTHOR.with_suffix('.json').read_text())
    p=WIP/'neary_woods_universal_tail_quotient253.json'
    require(pin(p)['sha256']=='48d604caf52af6cc6e37f77614787b1a02a549b03c1f5acdb53a5a7277c7504f','parent pin')
    parent=json.loads(p.read_text())
    checks=[static(f['packet'],c) for f,c in zip(parent['forms'],child['forms'],strict=True)]
    require(len(checks)==2,'both interfaces')
    degrees=hand_degrees()
    for f in child['forms']:
        require(f['manual_degree']['joint_factors']==degrees['joint'],'author joint degree')
        require(f['manual_degree']['unchanged_factor_sum']==110 and f['manual_degree']['total_upper_bound']==926,'author total degree')
    dependencies=[]
    for dep in child['dependencies']:
        file=ROOT/dep['path']; actual=pin(file)
        require(actual['sha256']==dep['sha256'],'dependency pin')
        dependencies.append(actual)
    return dict(status='PASS',reviewer_helper=pin(Path(__file__)),
        author=[pin(AUTHOR.with_suffix(x)) for x in ['.md','.py','.json']],
        dependencies=dependencies,source_checks=checks,
        partition_controls=partition_controls(),signed_controls=signed_controls(),
        manual_degree=degrees,
        supplied_or_predecessor_helpers_executed=False,
        saved_source_arrays_evaluated=False,saved_source_arrays_degree_propagated=False)

if __name__=='__main__':
    print(json.dumps(main(),sort_keys=True,indent=2))
