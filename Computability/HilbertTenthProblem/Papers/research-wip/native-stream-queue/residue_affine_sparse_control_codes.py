"""Injective paid control codes for the fixed ordinary-input U21 compiler.

Selector sums already used by prime/action lanes also price its control
chronology. Positive zeros agree; arbitrary outputs have an exact correction.
"""
import argparse
from collections import Counter
import copy
import hashlib
import json
from pathlib import Path
import random

import residue_affine_sparse_terminal537 as parent

TABLE, PRIMES = parent.TABLE, parent.PRIMES
units, ps = parent.units, parent.ps
execute, at = parent.execute, parent.at
polynomial_source, ledger = parent.polynomial_source, parent.ledger
DEFAULT_PLAN = dict(
    prime_weights={2:0,3:1,5:2,7:3,11:8,13:9,17:17,19:10},
    increment_coefficient=4,
    corrections={9:1,11:16,12:32,13:32,14:48,18:16},
    halt_code=63,
    target_basis=[(1,tuple(range(36))),(4,(2,6,8,11)),(1,(5,8,9))])


def leaves(value):
    if isinstance(value,str):return {value}
    if isinstance(value,dict):value=value.values()
    elif not isinstance(value,(tuple,list)):return set()
    return set().union(set(),*(leaves(v) for v in value))


def normalize_plan(plan,packet):
    plan=copy.deepcopy(DEFAULT_PLAN if plan is None else plan)
    assert set(plan)==set(DEFAULT_PLAN)
    weights=plan['prime_weights'];correction=plan['corrections']
    assert set(weights)==set(PRIMES) and all(type(k)is int and type(v)is int for k,v in weights.items())
    assert all(type(q)is int and 1<=q<=len(TABLE) and type(v)is int for q,v in correction.items())
    assert type(plan['increment_coefficient'])is int and type(plan['halt_code'])is int
    weights=dict(sorted(weights.items()));correction=dict(sorted((q,v) for q,v in correction.items() if v))
    codes={0:0,len(TABLE)+1:plan['halt_code']}
    for q,(op,register,*_) in enumerate(TABLE,1):
        codes[q]=weights[PRIMES[register]]+plan['increment_coefficient']*(op=='I')+correction.get(q,0)
    assert len(set(codes.values()))==len(TABLE)+2,'state code collision'
    assert all(0<v<3*packet['radix_multiplier'] for q,v in codes.items() if q),'positive code below unconditional radix required'
    basis=[]
    for coefficient,indices in plan['target_basis']:
        assert type(coefficient)is int and coefficient
        indices=tuple(indices)
        assert indices and all(type(i)is int and 0<=i<len(packet['edges']) for i in indices)
        assert len(set(indices))==len(indices)
        basis.append((coefficient,tuple(sorted(indices))))
    return dict(prime_weights=weights,increment_coefficient=plan['increment_coefficient'],
        corrections=correction,halt_code=plan['halt_code'],target_basis=basis),codes


def ancestors(source,roots):
    nodes={n:(a,b) for n,_,a,b in source};live=set();pending=list(roots)
    while pending:
        n=pending.pop()
        if isinstance(n,str) and n in nodes and n not in live:
            live.add(n);pending.extend(nodes[n])
    return live


class Emitter:
    """Literal two-input gates with exact cache reuse and fresh names."""
    def __init__(self,source,reserved):
        self.source=list(source);self.reserved=set(reserved);self.serial=0;self.cache={}
        for n,op,a,b in source:self.cache[self.key(op,a,b)]=n
    @staticmethod
    def key(op,a,b):
        return (op,*sorted((a,b),key=repr)) if op in ('+','*') else (op,a,b)
    def emit(self,op,a,b,label):
        if op=='+' and (a==0 or b==0):return b if a==0 else a
        if op=='*' and (a==1 or b==1):return b if a==1 else a
        if op=='*' and (a==0 or b==0):return 0
        key=self.key(op,a,b)
        if key in self.cache:return self.cache[key]
        while True:
            n=f'control_codes__{label}_{self.serial}';self.serial+=1
            if n not in self.reserved:break
        self.reserved.add(n);self.source.append((n,op,a,b));self.cache[key]=n
        return n
    def total(self,terms,label):
        result=0
        for term in terms:result=self.emit('+',result,term,label)
        return result
    def signed(self,terms,label):
        positive=[];negative=[]
        for coefficient,word in terms:
            if coefficient:
                value=self.emit('*',abs(coefficient),word,label+'_multiple')
                (positive if coefficient>0 else negative).append(value)
        result=self.total(positive,label+'_positive')
        if negative:result=self.emit('-',result,self.total(negative,label+'_negative'),label+'_difference')
        return result


def selector_vectors(source,edge_names):
    m=len(edge_names);vectors={n:tuple(int(i==j) for i in range(m)) for j,n in enumerate(edge_names)}
    for n,op,a,b in source:
        if n in vectors:continue
        if op in ('+','-') and a in vectors and b in vectors:
            vectors[n]=tuple(x+y if op=='+' else x-y for x,y in zip(vectors[a],vectors[b]))
        elif op=='*':
            if type(a)is int and b in vectors:vectors[n]=tuple(a*x for x in vectors[b])
            elif type(b)is int and a in vectors:vectors[n]=tuple(b*x for x in vectors[a])
    return vectors


def remap(value,aliases):
    if isinstance(value,str):return aliases.get(value,value)
    if isinstance(value,list):return [remap(v,aliases) for v in value]
    if isinstance(value,tuple):return tuple(remap(v,aliases) for v in value)
    if isinstance(value,dict):return {k:remap(v,aliases) for k,v in value.items()}
    return value


def rewrite(old,plan=None):
    assert not old.get('injective_control_codes')
    assert old['table']==TABLE and old['primes']==PRIMES,'fixed literal U21 and primes only'
    expected=parent.build(TABLE,old['form'],PRIMES,old['shared'])
    assert old==expected,'complete canonical537 caller required'
    plan,codes=normalize_plan(plan,old)
    ports=old['interfaces'];nodes={n:(op,a,b) for n,op,a,b in old['source']}
    control=old['comparisons'][1];left,right=control
    assert nodes[left]==('*',ports['B'],ports['next_control'])
    assert nodes[right][0:2]==('+',ports['current_control'])
    assert nodes[nodes[right][2]]==('*',len(TABLE)+1,ports['P'])
    live=ancestors(old['source'],[v for pair in old['comparisons'] if pair!=control for v in pair])
    base=[row for row in old['source'] if row[0] in live]
    removed=set(nodes)-live
    aliases={ports['current_control']:None,ports['next_control']:None}
    for key in ('interfaces','public_registers'):
        assert not (removed-set(aliases))&leaves(old.get(key,{}))
    assert not removed&set(old['unit_factors'])
    edge_names=[]
    for i in range(len(old['edges'])):
        matches=[n for n,op,a,b in base if (op,a,b)==('-',f'edge{i}_hat',1)]
        assert len(matches)==1;edge_names.append(matches[0])
    vectors=selector_vectors(base,edge_names);discoveries=[]
    def known(indices):
        indices=tuple(sorted(indices));wanted=tuple(int(i in indices) for i in range(len(edge_names)))
        found=next((n for n,v in vectors.items() if v==wanted),None)
        assert found is not None,('selector sum not already paid',indices)
        discoveries.append(dict(indices=indices,register=found));return found
    g=Emitter(base,set(nodes)|set(old['parameters']+old['auxiliaries']))
    J=known(range(len(edge_names)));L=known((0,1));edges=old['edges']
    terms=[];w2=plan['prime_weights'][2]
    if w2:terms.append((w2,g.emit('-',J,L,'body_rows')))
    for prime,weight in plan['prime_weights'].items():
        if prime!=2 and weight!=w2:
            terms.append((weight-w2,known(i for i,e in enumerate(edges) if e[3]==prime)))
    alpha=plan['increment_coefficient']
    if alpha:
        I=known(i for i,e in enumerate(edges) if e[2]=='I')
        terms.append((alpha,g.emit('-',I,L,'body_increments')))
    correction=plan['corrections']
    for value in sorted(set(correction.values())):
        words=[g.total([edge_names[i] for i,e in enumerate(edges) if e[0]==q],'duplicate_state')
               for q,v in correction.items() if v==value]
        terms.append((value,g.total(words,'duplicate_group')))
    current=g.signed(terms,'current');current_gates=len(g.source)-len(base)
    target_start=len(g.source)
    basis=[(coefficient,known(indices)) for coefficient,indices in plan['target_basis']]
    residual=[codes[e[1]]-sum(c*vectors[n][i] for c,n in basis) for i,e in enumerate(edges)]
    terms=[(c,g.total([edge_names[i] for i,v in enumerate(residual) if v==c],'target_class'))
           for c in sorted(set(residual)-{0})]+basis
    following=g.signed(terms,'target');target_gates=len(g.source)-target_start
    newleft=g.emit('*',ports['B'],following,'left')
    newright=g.emit('+',current,g.emit('*',codes[len(TABLE)+1],ports['P'],'halt'),'right')
    comparisons=[(newleft,newright) if pair==control else pair for pair in old['comparisons']]
    source=ps.sort_source(g.source,old['parameters']+old['auxiliaries'])
    aliases={ports['current_control']:current,ports['next_control']:following}
    # Every remaining active export is retained literally; two changed ports are remapped recursively.
    packet=ps.metadata(dict(old,source=source,comparisons=comparisons,
        interfaces=remap(old['interfaces'],aliases),injective_control_codes=True,
        control_code_parent=old,control_code_plan=plan,state_codes=codes,
        old_control_comparison=control,control_comparison=(newleft,newright),
        deleted_control_registers=sorted(removed),paid_selector_discoveries=discoveries,
        target_residual_coefficients=residual,
        control_gate_counts=dict(old=len(removed),current=current_gates,target=target_gates,
            new=len(source)-len(base)),
        equivalence_scope='Identical supplied positive zeros after unchanged typing and injective coded chronology; exact off-zero finalizer correction, not polynomial equality.'))
    if 'public_registers' in old:packet['public_registers']=remap(old['public_registers'],aliases)
    ps.checked_source(source,packet['parameters'],packet['auxiliaries'])
    actual=selector_vectors(source,edge_names)
    assert actual[current]==tuple(codes[e[0]] for e in edges)
    assert actual[following]==tuple(codes[e[1]] for e in edges)
    assert packet['unit_factors']==old['unit_factors'] and packet['auxiliaries']==old['auxiliaries']
    for sos in (False,True):
        ss,out=polynomial_source(packet,sum_of_squares=sos)
        assert ancestors(ss,[out])=={n for n,_,_,_ in ss}
        assert units.degree_bound(packet,sum_of_squares=sos)==units.degree_bound(old,sum_of_squares=sos)
    active=set(packet['parameters']+packet['auxiliaries'])|{n for n,_,_,_ in source}
    assert leaves(packet['interfaces'])<=active
    return packet


def build(form='coupled',*,shared=True,plan=None):
    return rewrite(parent.build(TABLE,form,PRIMES,shared),plan)


def source_audit(packet,cases=48,seed=509123):
    old=packet['control_code_parent'];rng=random.Random(seed);counts=Counter()
    oldpair=packet['old_control_comparison'];newpair=packet['control_comparison']
    for case in range(cases):
        signed=case>=cases//2
        values={n:rng.randrange(-4,5) if signed else rng.randrange(1,6)
                for n in packet['parameters']+packet['auxiliaries']}
        for sos in (False,True):
            ss,so=polynomial_source(packet,sum_of_squares=sos);bs,bo=polynomial_source(old,sum_of_squares=sos)
            a=execute(ss,values);b=parent.parent.replay(bs,values)
            rr=at(a,newpair[0])-at(a,newpair[1]);r0=at(b,oldpair[0])-at(b,oldpair[1])
            change=rr*rr-r0*r0
            assert a[so]==b[bo]+(change if sos else b[old['unit_register']]*change)
            assert all(a[n]==b[n] for n,_,_,_ in old['source'] if n not in packet['deleted_control_registers'])
            ee=[values[f'edge{i}_hat']-1 for i in range(len(packet['edges']))]
            for key,index in (('current_control',0),('next_control',1)):
                assert at(a,packet['interfaces'][key])==sum(packet['state_codes'][e[index]]*v for e,v in zip(packet['edges'],ee))
            assert all(at(a,packet['interfaces'][k])==at(b,v) for k,v in old['interfaces'].items() if k not in ('current_control','next_control'))
            counts['complete_register_factor_interface_finalizer_corrections']+=1
        counts['signed_assignments']+=signed
    return dict(counts)


def sharing_audit(form,plan,cases=24):
    a=build(form,shared=True,plan=plan);b=build(form,shared=False,plan=plan);rng=random.Random(509456)
    for case in range(cases):
        values={n:rng.randrange(-3,4) if case>=cases//2 else rng.randrange(1,5) for n in a['parameters']+a['auxiliaries']}
        for sos in (False,True):
            ss,so=polynomial_source(a,sum_of_squares=sos);bs,bo=polynomial_source(b,sum_of_squares=sos)
            aa=execute(ss,values);bb=execute(bs,values)
            assert aa[so]==bb[bo]
            assert all(at(aa,v)==at(bb,b['interfaces'][k]) for k,v in a['interfaces'].items())
    return dict(shared_unshared_outputs=2*cases,signed_assignments=cases//2)


def chronology_audit(packet):
    rng=random.Random(509891);codes=packet['state_codes'];edges=packet['edges'];counts=Counter()
    # A shortest suffix to halt gives genuine control words covering every edge.
    from collections import deque
    def path(start,target):
        todo=deque([(start,[])]);seen={start}
        while todo:
            q,history=todo.popleft()
            if q==target:return history
            for i,e in enumerate(edges):
                if e[0]==q and e[1] not in seen:seen.add(e[1]);todo.append((e[1],history+[i]))
        raise AssertionError('unreachable control state')
    fixtures=[path(0,e[0])+[i]+path(e[1],len(TABLE)+1) for i,e in enumerate(edges)]
    for _ in range(400):fixtures.append([rng.randrange(len(edges)) for _ in range(rng.randrange(1,9))])
    for word in fixtures:
        B=packet['radix_multiplier']*rng.choice((3,4,8));P=B**len(word)
        oldc=sum(edges[i][0]*B**j for j,i in enumerate(word));oldn=sum(edges[i][1]*B**j for j,i in enumerate(word))
        newc=sum(codes[edges[i][0]]*B**j for j,i in enumerate(word));newn=sum(codes[edges[i][1]]*B**j for j,i in enumerate(word))
        actual=(edges[word[0]][0]==0 and edges[word[-1]][1]==len(TABLE)+1 and all(edges[a][1]==edges[b][0] for a,b in zip(word,word[1:])))
        assert (B*oldn-oldc-(len(TABLE)+1)*P==0)==actual
        assert (B*newn-newc-codes[len(TABLE)+1]*P==0)==actual
        counts['typed_control_words']+=1;counts['accepted_control_words']+=actual
    # Actual U21 payload histories use the unchanged packing and native ports.
    for code in (0,1,2):
      for x in (1,2,4):
        states,selected=parent.parent.parent.payload_run(TABLE,3**code,x,PRIMES,limit=60)
        if states[-1][0]!=len(TABLE)+1:continue
        values=parent.pack_path(packet,states,selected,x)
        rows=[row for row in packet['source'] if not row[0].startswith('native__') and row[0]!='sparse_all_units']
        env=parent.parent.replay(rows,values)
        assert all(at(env,a)==at(env,b) for a,b in packet['comparisons'][:4])
        counts['actual_halted_U21_outer_histories']+=1;counts['actual_chronological_rows']+=len(selected)
    return dict(counts)


def guard_audit():
    old=parent.build();bad=[]
    for key,value in (('interfaces',{**old['interfaces'],'bad':old['interfaces']['current_control']}),
                      ('comparisons',old['comparisons'][1:]),('table',TABLE[:-1]),('primes',PRIMES[::-1])):
        changed=copy.deepcopy(old);changed[key]=value;bad.append((changed,None))
    changed=copy.deepcopy(old);changed['source']=old['source'][:-1];bad.append((changed,None))
    plans=[]
    for field,value in (('halt_code',0),('halt_code',192),('increment_coefficient',4.0)):
        plan=copy.deepcopy(DEFAULT_PLAN);plan[field]=value;plans.append(plan)
    plan=copy.deepcopy(DEFAULT_PLAN);plan['target_basis']=[(1,(0,2,7))];plans.append(plan)
    plan=copy.deepcopy(DEFAULT_PLAN);plan['target_basis']=[(1,(0,0))];plans.append(plan)
    plan=copy.deepcopy(DEFAULT_PLAN);plan['corrections'][9]=0;plans.append(plan)
    for plan in plans:bad.append((old,plan))
    rejected=0
    for packet,plan in bad:
        try:rewrite(packet,plan)
        except (AssertionError,KeyError,TypeError,ValueError):rejected+=1
        else:raise AssertionError('malformed caller/plan accepted')
    return dict(rejected_callers_and_plans=rejected)


def verify():
    doubled=copy.deepcopy(DEFAULT_PLAN)
    for field in ('prime_weights','corrections'):doubled[field]={k:2*v for k,v in doubled[field].items()}
    doubled['increment_coefficient']*=2;doubled['halt_code']*=2
    doubled['target_basis']=[(2*c,ids) for c,ids in doubled['target_basis']]
    unbased=copy.deepcopy(DEFAULT_PLAN);unbased['target_basis']=[]
    shifted=copy.deepcopy(DEFAULT_PLAN)
    shifted['prime_weights']={k:v+1 for k,v in shifted['prime_weights'].items()}
    shifted['halt_code']+=1
    records=[];sharing=[]
    for index,plan in enumerate((DEFAULT_PLAN,doubled,unbased,shifted)):
      for form in ('units','coupled'):
        for shared in (False,True):
            packet=build(form,shared=shared,plan=plan)
            records.append(dict(plan=index,form=form,shared=shared,ledger=ledger(packet),
                gate_counts=packet['control_gate_counts'],checks=source_audit(packet,seed=509000+len(records))))
        sharing.append(dict(plan=index,form=form,checks=sharing_audit(form,plan)))
    packet=build();schedule,out=polynomial_source(packet);default=ledger(packet)
    assert default['product']['operations']==505 and default['product']['multiplications']==177 and default['product']['additions_subtractions']==328
    assert default['product']['degree_upper_bound']==5091 and default['certificate']['witnesses']==67
    return dict(status='PASS_SPARSE_INJECTIVE_CONTROL_CODES',default_ledger=default,
        default_plan=packet['control_code_plan'],state_codes=packet['state_codes'],
        gate_counts=packet['control_gate_counts'],paid_selectors=packet['paid_selector_discoveries'],
        target_residual_coefficients=packet['target_residual_coefficients'],
        source=schedule,output=out,source_sha256=hashlib.sha256(json.dumps(schedule).encode()).hexdigest(),
        ledgers=records,sharing=sharing,chronology=chronology_audit(packet),guards=guard_audit(),
        scope='Fixed literal U21/primes, unchanged radix and ordinary input; identical supplied positive zero sets. Finite source/control/outer fixtures do not materialize native Pell zeros.')


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--write',action='store_true');args=parser.parse_args()
    result=json.loads(json.dumps(verify()));path=Path(__file__).with_suffix('.json')
    if args.write:path.write_text(json.dumps(result,indent=2)+'\n')
    else:assert json.loads(path.read_text())==result,'receipt mismatch'
    print(result['status']);print(result['default_ledger'])
