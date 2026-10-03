#!/usr/bin/env python3
"""Independent checks of newly authored paired_compiler; no upstream execution."""
import hashlib
import json
from pathlib import Path
import random
import sys

ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT))
import paired_compiler as pc

PIN='506144b361b2bea634d468a94921644d91868dc089a257fe289a0bf51b74cec9'

def require(ok,description):
    if not ok:
        raise RuntimeError(description)

def rejected(call,description):
    try:
        call()
    except (ValueError,TypeError,KeyError):
        return
    raise RuntimeError('invalid input accepted: '+description)

def mm(a,b):
    return [[sum(x*y for x,y in zip(row,col)) for col in zip(*b)] for row in a]

def inv(a):
    return [[a[1][1],-a[0][1]],[-a[1][0],a[0][0]]]

def eye(n):
    return [[int(i==j) for j in range(n)] for i in range(n)]

def generic_product(gens,seq):
    answer=eye(4)
    for name in [f'A{i}' for i in seq]+['C']+[f'B{i}' for i in reversed(seq)]:
        answer=mm(answer,gens[name])
    return answer

def oracle_residuals(gens,r,values,mode):
    def state(z,s):
        return eye(2) if s==0 else [[values[f'{z}_{s}_{i}{j}_p']-values[f'{z}_{s}_{i}{j}_n'] for j in range(2)] for i in range(2)]
    h=[[[v for v in row[:2]] for row in gens[f'A{i}'][:2]] for i in range(1,115)]
    g=[inv([row[:2] for row in gens[f'B{i}'][:2]]) for i in range(1,115)]
    c=[row[:2] for row in gens['C'][:2]]
    out={}
    for s in range(1,r+1):
        es=[values[f'e_{s}_{i}'] for i in range(1,115)]
        out[f'select_{s}']=sum(es)-1
        for z,mats in [('H',h),('G',g)]:
            previous,current=state(z,s-1),state(z,s)
            weighted=[[sum(es[i]*mats[i][a][b] for i in range(114)) for b in range(2)] for a in range(2)]
            following=mm(previous,weighted)
            for a in range(2):
                for b in range(2):
                    out[f'update_{z}_{s}_{a}{b}']=current[a][b]-following[a][b]
        for z in ('H','G'):
            for a in range(2):
                for b in range(2):
                    out[f'canonical_{z}_{s}_{a}{b}']=values[f'{z}_{s}_{a}{b}_p']*values[f'{z}_{s}_{a}{b}_n']
    target=[[values[f'T_{a}{b}'] if mode=='signed' else values[f'T_{a}{b}_p']-values[f'T_{a}{b}_n'] for b in range(2)] for a in range(2)]
    hc,tg=mm(state('H',r),c),mm(target,state('G',r))
    for a in range(2):
        for b in range(2):
            out[f'terminal_{a}{b}']=hc[a][b]-tg[a][b]
    if mode=='natural':
        for a in range(2):
            for b in range(2):
                out[f'canonical_T_{a}{b}']=values[f'T_{a}{b}_p']*values[f'T_{a}{b}_n']
    return out

class CountInt:
    multiplications=0
    additions=0
    subtractions=0
    negations=0
    def __init__(self,value):
        self.value=value.value if isinstance(value,CountInt) else value
    def __mul__(self,other):
        type(self).multiplications+=1
        return CountInt(self.value*CountInt(other).value)
    __rmul__=__mul__
    def __add__(self,other):
        type(self).additions+=1
        return CountInt(self.value+CountInt(other).value)
    __radd__=__add__
    def __sub__(self,other):
        type(self).subtractions+=1
        return CountInt(self.value-CountInt(other).value)
    def __neg__(self):
        type(self).negations+=1
        return CountInt(-self.value)
    def __eq__(self,other):
        return self.value==CountInt(other).value


def main():
    raw=(ROOT/'data/semigroup.json').read_bytes()
    require(hashlib.sha256(raw).hexdigest()==PIN,'local literal copy hash')
    data=json.loads(raw)
    gens={x['name']:x['matrix'] for x in data['generators']}
    constants=pc.load_constants()
    CountInt.additions=CountInt.multiplications=0
    pc.multiply([[CountInt(2),CountInt(3)],[CountInt(5),CountInt(7)]],[[CountInt(11),CountInt(13)],[CountInt(17),CountInt(19)]])
    require((CountInt.multiplications,CountInt.additions)==(8,4),'2x2 multiply exact operation count')
    CountInt.multiplications=CountInt.subtractions=CountInt.negations=0
    pc.inverse([[CountInt(1),CountInt(2)],[CountInt(0),CountInt(1)]])
    require((CountInt.multiplications,CountInt.subtractions,CountInt.negations)==(2,1,2),'inverse exact operation count')
    inverse_calls=0
    original_inverse=pc.inverse
    def counted_inverse(a):
        nonlocal inverse_calls
        inverse_calls+=1
        return original_inverse(a)
    pc.inverse=counted_inverse
    try:
        pc.load_constants()
    finally:
        pc.inverse=original_inverse
    require(inverse_calls==572,'fixed loader inverse calls')
    randomizer=random.Random(731197)
    sequences=[[]]+[[i] for i in range(1,115)]+[[1,2],[2,1],[114,21],[21,114]]
    sequences += [[randomizer.randrange(1,115) for _ in range(r)] for r in range(2,10) for _ in range(8)]
    certificates=0
    for seq in sequences:
        full=generic_product(gens,seq)
        require(all(full[i][j]==0 for i in range(4) for j in range(4) if (i<2)!=(j<2)),'oracle block diagonal')
        require([row[2:] for row in full[2:]]==[[1,2],[0,1]],'oracle lower marker')
        top=[row[:2] for row in full[:2]]
        for mode in ('signed','natural'):
            cert=pc.certificate(constants,seq,mode=mode)
            require(cert['target']==top,'generic product matches certificate target')
            require(pc.evaluate(constants,len(seq),cert['values'],mode)['zero'],'valid certificate is zero')
            require(pc.certificate(constants,seq,target=top,mode=mode)['values']==cert['values'],'deterministic canonical tuple')
            certificates+=1
    arbitrary_points=0
    for mode in ('signed','natural'):
        for r in range(5):
            ledger=pc.ledger(constants,r,mode)
            require(ledger['natural_auxiliary_count']==130*r,'auxiliary count')
            require(ledger['residual_count']==17*r+(4 if mode=='signed' else 8),'residual count')
            require(ledger['sos_total_degree']==(2 if r==0 and mode=='signed' else 4),'degree ledger')
            for _ in range(8):
                values={name:randomizer.randrange(5) for name in pc.auxiliary_names(r)}
                values.update({name:randomizer.randrange(-3,4) if mode=='signed' else randomizer.randrange(5) for name in pc.external_names(mode)})
                expected=oracle_residuals(gens,r,values,mode)
                actual={name:pc.evaluate_poly(q,values) for name,q in pc.residuals(constants,r,mode)}
                require(actual==expected,'independent direct residual oracle')
                require(pc.evaluate(constants,r,values,mode)['sos']==sum(x*x for x in expected.values()),'independent SOS oracle')
                arbitrary_points+=1
            values={name:CountInt(2) for name in list(pc.auxiliary_names(r))+list(pc.external_names(mode))}
            CountInt.additions=CountInt.multiplications=0
            total=0
            for _,q in pc.residuals(constants,r,mode):
                residual=pc.evaluate_poly({m:CountInt(c) for m,c in q.items()},values)
                total += residual*residual
            require(CountInt.additions==ledger['generic_sparse_evaluator_additions'],'instrumented exact addition count')
            require(CountInt.multiplications==ledger['generic_sparse_evaluator_multiplications'],'instrumented exact multiplication count')
    tamper_checks=0
    for mode in ('signed','natural'):
        seq=[2,21,114]
        cert=pc.certificate(constants,seq,mode=mode)
        original=cert['values']
        for name in pc.auxiliary_names(3):
            vals=dict(original);vals[name]+=1
            require(not pc.evaluate(constants,3,vals,mode)['zero'],'one-coordinate auxiliary tamper')
            tamper_checks+=1
        for z in ('H','G'):
            vals=dict(original)
            vals[f'{z}_3_00_p']+=1;vals[f'{z}_3_00_n']+=1
            require(not pc.evaluate(constants,3,vals,mode)['zero'],'preserving signed state but breaking complementarity')
            tamper_checks+=1
        for r in (0,1,3):
            cert=pc.certificate(constants,seq[:r],target=[[0,0],[0,0]],mode=mode)
            require(not pc.evaluate(constants,r,cert['values'],mode)['zero'],'singular target not witnessed')
            tamper_checks+=1
        vals=pc.certificate(constants,[],mode=mode)['values']
        if mode=='natural':
            vals['T_00_p']+=1;vals['T_00_n']+=1
            require(not pc.evaluate(constants,0,vals,mode)['zero'],'noncanonical external target rejected by SOS at r0')
            tamper_checks+=1
    base=pc.certificate(constants,[1])['values']
    invalid_cases=[]
    for r in (-1,True,1.0,'1'):
        invalid_cases.append((lambda r=r:list(pc.residuals(constants,r)),f'r={r!r}'))
    invalid_cases.append((lambda:list(pc.residuals(constants,1,'bad')),'unknown target mode'))
    invalid_cases.append((lambda:pc.target_values([[1,0],[0,1]],'bad'),'unknown mode in target_values helper'))
    for sequence in ([0],[115],[True],[1.0],'1',None):
        invalid_cases.append((lambda sequence=sequence:pc.certificate(constants,sequence),'invalid sequence '+repr(sequence)))
    for target in ([[True,0],[0,1]],[[1.0,0],[0,1]],[[1,0],[0]],[[1,0,0],[0,1,0]]):
        invalid_cases.append((lambda target=target:pc.certificate(constants,[],target),'invalid target '+repr(target)))
    for kind in ('negative','boolean','missing','extra','float'):
        v=dict(base)
        if kind=='negative':v['e_1_1']=-1
        if kind=='boolean':v['e_1_1']=True
        if kind=='float':v['e_1_1']=1.0
        if kind=='missing':del v['e_1_1']
        if kind=='extra':v['extra']=0
        invalid_cases.append((lambda v=v:pc.evaluate(constants,1,v),'invalid assignment '+kind))
    v=pc.certificate(constants,[],mode='natural')['values'];v['T_00_n']=-1
    invalid_cases.append((lambda:pc.evaluate(constants,0,v,'natural'),'negative natural external target'))
    wrong_full=generic_product(gens,[]);wrong_full[2][2]=0
    invalid_cases.append((lambda:pc.target_upper(wrong_full),'wrong lower block'))
    wrong_full2=generic_product(gens,[]);wrong_full2[0][2]=1
    invalid_cases.append((lambda:pc.target_upper(wrong_full2),'nonzero cross block'))
    for call,description in invalid_cases:
        rejected(call,description)
    print(json.dumps({'status':'PASS','source_sha256':PIN,'upstream_code_executed':False,
        'reviewed_compiler_sha256':hashlib.sha256((ROOT/'paired_compiler.py').read_bytes()).hexdigest(),
        'instrumented_2x2_multiply_counts':{'multiplications':8,'additions':4},
        'instrumented_2x2_inverse_counts':{'multiplications':2,'subtractions':1,'negations':2},
        'instrumented_loader_inverse_calls':inverse_calls,
        'generic_product_certificate_cases':certificates,'all_single_tile_choices_checked':114,
        'arbitrary_assignment_residual_oracle_cases':arbitrary_points,
        'instrumented_operation_count_cases':10,
        'auxiliary_and_target_tamper_cases':tamper_checks,
        'invalid_input_rejection_cases':len(invalid_cases),
        'sequence_lengths_covered':sorted({len(s) for s in sequences}),
        'check_limits':'Finite tests support, but do not replace, the general proof.'},indent=2))

if __name__=='__main__':
    main()
