"""Remove the terminal payload from the sparse compiler's supplied height.

Soundness derives the terminal digit bound from typed transport. The
inverse integer slack identity need not preserve positivity off zero.
"""
import argparse
from collections import Counter
import copy
import hashlib
import json
from pathlib import Path
import random

import residue_affine_sparse_scale538 as parent

TABLE,PRIMES=parent.TABLE,parent.PRIMES
units,ps=parent.units,parent.ps
execute,at=parent.execute,parent.at
polynomial_source,ledger=parent.polynomial_source,parent.ledger


def rewrite(old):
    assert old['form'] in ('units','coupled') and not old.get('terminal_bound_from_transport')
    expected=parent.build(old['table'],old['form'],old['primes'],old['shared'])
    assert old==expected,'requires the complete canonical sparse538 packet'
    nodes={n:(op,a,b) for n,op,a,b in old['source']}
    h=old['interfaces']['h'];op,middle,slack=nodes[h]
    assert op=='+' and slack=='height_slack'
    op,first,terminal=nodes[middle]
    assert op=='+' and terminal=='final_payload'
    assert nodes[first]==('+','program','input')
    assert {n for n,_,a,b in old['source'] if middle in (a,b)}=={h}
    assert {n for n,_,a,b in old['source'] if slack in (a,b)}=={h}
    assert middle not in parent.parent.leaves(old['interfaces'])
    assert middle not in parent.parent.leaves(old['comparisons'])
    source=[(n,'+',first,slack) if n==h else (n,op,a,b)
            for n,op,a,b in old['source'] if n!=middle]
    ps.checked_source(source,old['parameters'],old['auxiliaries'])
    result=ps.metadata(dict(old,source=source,terminal_bound_from_transport=True,
        terminal_height_parent=old,deleted_height_register=middle,
        height_definition='h=program+input+height_slack',
        equivalence_scope='Same represented ordinary-input relation; positive parent zeros map forward by eta_new=eta_old+F. The integer inverse can be nonpositive.'))
    assert result['operations']==old['operations']-1
    assert result['multiplications']==old['multiplications']
    assert result['additions_subtractions']==old['additions_subtractions']-1
    assert result['comparisons']==old['comparisons'] and result['auxiliaries']==old['auxiliaries']
    return result


def build(table=TABLE,form='coupled',primes=PRIMES,shared=True):
    return rewrite(parent.build(table,form,primes,shared))


def lift_to_parent(values):
    return dict(values,height_slack=values['height_slack']-values['final_payload'])


def project_from_parent(values):
    return dict(values,height_slack=values['height_slack']+values['final_payload'])


def identity_audit(packet,cases=48,seed=537001):
    old=packet['terminal_height_parent'];rng=random.Random(seed);counts=Counter()
    for case in range(cases):
        signed=case>=cases//2
        values={n:rng.randrange(-3,4) if signed else rng.randrange(1,6)
                for n in packet['parameters']+packet['auxiliaries']}
        if case==0:values.update(height_slack=1,final_payload=1)
        if case==1:values.update(height_slack=1,final_payload=2)
        before=lift_to_parent(values)
        assert project_from_parent(before)==values
        for sos in (False,True):
            ss,so=polynomial_source(packet,sum_of_squares=sos)
            bs,bo=polynomial_source(old,sum_of_squares=sos)
            a=execute(ss,values);b=parent.replay(bs,before)
            assert a[so]==b[bo]
            assert all(a[n]==b[n] for n,_,_,_ in old['source'] if n!=packet['deleted_height_register'])
            assert [at(a,l)-at(a,r) for l,r in packet['comparisons']]==[at(b,l)-at(b,r) for l,r in old['comparisons']]
            counts['complete_register_residual_finalizer_identities']+=1
        counts['signed_assignments']+=signed
        counts['nonpositive_parent_slacks_on_positive_assignments']+=not signed and before['height_slack']<=0
        original={n:rng.randrange(1,6) for n in packet['parameters']+packet['auxiliaries']}
        after=project_from_parent(original)
        assert min(after.values())>0 and lift_to_parent(after)==original
        counts['positive_parent_projections']+=1
    return dict(counts)


def shared_audit(packet,cases=24,seed=537002):
    plain=build(packet['table'],packet['form'],packet['primes'],False)
    rng=random.Random(seed);counts=Counter()
    for case in range(cases):
        signed=case>=cases//2
        values={n:rng.randrange(-3,4) if signed else rng.randrange(1,5)
                for n in packet['parameters']+packet['auxiliaries']}
        for sos in (False,True):
            ss,so=polynomial_source(packet,sum_of_squares=sos)
            bs,bo=polynomial_source(plain,sum_of_squares=sos)
            a=execute(ss,values);b=parent.replay(bs,values)
            assert a[so]==b[bo]
            assert all(at(a,n)==at(b,plain['interfaces'][key]) for key,n in packet['interfaces'].items())
            counts['complete_shared_unshared_identities']+=1
        counts['signed_assignments']+=signed
    return dict(counts)


def pack_path(packet,states,selected,input_value):
    """Pack actual outer rows with height chosen independently of the endpoint."""
    assert selected and len(states)==len(selected)+1 and states[-1][0]==len(packet['table'])+1
    W=[];R=[];S=[]
    for (q,value),(nxt,out),edge in zip(states,states[1:],selected):
        row=packet['edges'][edge];assert (q,nxt)==row[:2];p=row[3]
        if row[2]=='I':w=value-1;r=s=0;assert out==p*value
        elif row[2] in ('D','T'):
            assert value%p==0;w=value//p-1;r=s=0
            assert out==(value//p if row[2]=='D' else value)
        else:
            w,rem=divmod(value,p);assert 1<=rem<p and out==value
            r=rem-1;s=p-1-rem
        assert min(w,r,s)>=0;W.append(w);R.append(r);S.append(s)
    h=1
    while h<=max([states[0][1]+input_value]+W+R+S):h*=2
    B=packet['radix_multiplier']*h;P=B**len(selected);J=(P-1)//(B-1)
    pack=lambda seq:sum(v*B**i for i,v in enumerate(seq))
    ee=[pack([int(i==e) for e in selected]) for i in range(len(packet['edges']))]
    zz=[pack([w+1 if packet['edges'][edge][3]==p else 0 for w,edge in zip(W,selected)]) for p in packet['classes']]
    vv=[(packet['edges'][edge][3]-1)*(w+1) for w,edge in zip(W,selected)]
    actions=[pack([v if packet['edges'][edge][2]==kind else 0 for v,edge in zip(vv,selected)]) for kind in ('I','D')]
    zz+=actions;w,r,s=map(pack,(W,R,S));V=pack(vv);L=ee[0]+ee[1]
    assert V==w+J+sum((p-2)*z for p,z in zip(packet['classes'],zz))
    assert (L-input_value)%(B-1)==0 and (L-input_value)//(B-1)>=0
    values=dict(program=states[0][1],input=input_value,final_payload=states[-1][1],
        height_slack=h-states[0][1]-input_value,quotient_hat=w+1,remainder_hat=r+1,
        complement_hat=s+1,global_slack=P-V-sum(actions)-2,
        loader_quotient_hat=1+(L-input_value)//(B-1))
    values.update({f'edge{i}_hat':e+1 for i,e in enumerate(ee)})
    values.update({f'product{i}_hat':z+1 for i,z in enumerate(zz)})
    assert min(values.values())>0
    return values


def path_audit():
    rng=random.Random(537777)
    fixtures=[(TABLE,PRIMES),((('I',2,1),),(5,3,2)),((('I',0,1),),(5,3,2)),
              ((('I',3,1),),(5,3,2,23))]
    for size in range(1,7):
      for _ in range(3):
        table=[]
        for q in range(size):
            op=rng.choice(('I','D','T'));reg=rng.randrange(4)
            table.append((op,reg,*[rng.randrange(q+1,size+1) for _ in range(1 if op=='I' else 2)]))
        fixtures.append((tuple(table),PRIMES[:4]))
    counts=Counter();examples=[]
    for table,primes in fixtures:
        packet=build(table,primes=primes)
        rows=[row for row in packet['source'] if not row[0].startswith('native__') and row[0]!='sparse_all_units']
        for code in (0,1,2):
          for x in (1,2,4):
            states,selected=parent.parent.payload_run(table,3**code,x,primes,limit=60)
            if states[-1][0]!=len(table)+1:continue
            values=pack_path(packet,states,selected,x);env=parent.replay(rows,values);ports=packet['interfaces']
            B=env[ports['B']];P=env[ports['P']];h=env[ports['h']]
            assert env[packet['repunit_factor']]==1
            assert all(at(env,a)==at(env,b) for a,b in packet['comparisons'][:4])
            assert at(env,ports['joined_H']) & at(env,ports['joined_M'])==at(env,ports['joined_Z'])
            assert P==B**len(selected) and 0<env[ports['current']]<P and 0<env[ports['following']]<P
            assert values['program']<B and values['final_payload']<B
            counts['halted_outer_histories']+=1;counts['chronological_rows']+=len(selected)
            counts['terminal_at_or_above_height']+=values['final_payload']>=h
            counts['nonpositive_inverse_height_slacks']+=lift_to_parent(values)['height_slack']<=0
            if len(table)==1 and x==1 and code==0:
                examples.append(dict(table=table,primes=primes,states=states,h=h,B=B,
                                     terminal=values['final_payload'],old_slack=lift_to_parent(values)['height_slack']))
            if values['height_slack']>1:
                bad={**values,'input':x+1,'height_slack':values['height_slack']-1}
                be=parent.replay(rows,bad)
                assert be[packet['repunit_factor']]==1
                assert all(at(be,a)==at(be,b) for a,b in packet['comparisons'][:3])
                a,b=packet['comparisons'][3];assert at(be,a)-at(be,b)==-1
                counts['wrong_input_rejections']+=1
    assert counts['terminal_at_or_above_height']>0
    return dict(tables=len(fixtures),counts=dict(counts),examples=examples,
                scope='Actual typed outer histories; no complete native Pell zeros are materialized.')


def bound_audit():
    counts=Counter()
    for pmax in (2,3,5,7,19,23):
      C=1
      while C<max(4,3*pmax+1):C*=2
      for h in (3,4,5,8,13):
       B=C*h
       assert B>=24 and B-1>2*(pmax-2) and B-1>2*(h-1)
       for J in range(1,8):
        for sign in (-1,1):
            P=(B-1)*J+sign
            assert P>=3 and (pmax-2)*J<P and (h-1)*J<P
            assert (B-2*pmax*h-pmax+1)*J-pmax-2>=pmax+2
            for L in (4,9,16,48):
                a=1
                while a<L:a*=2
                M=(P+1)*(P**L-1)//(P-1)
                assert M<2*P**L<B*P**a
                counts['weak_repunit_bound_cases']+=1
                counts['minimal_height_three_cases']+=h==3
    # Exact transport including endpoints not bounded by h and extremal digits.
    for B in (4,8,16,32):
      for T in (1,2,3):
       P=B**T
       for E in range(1,B):
        for N in (0,1,P//2,P-2,P-1):
            F,C=divmod(B*N+E,P)
            if F==0:continue
            assert 0<=C<P and 0<F<B and B*N+E==C+P*F
            current=[(C//B**j)%B for j in range(T)]
            following=[(N//B**j)%B for j in range(T)]
            assert current[0]==E and following[-1]==F
            assert all(following[j]==current[j+1] for j in range(T-1))
            counts['terminal_transport_and_chronology_cases']+=1
    return dict(counts)


def guards_audit():
    old=parent.build();rejected=0
    mutations=[]
    for key,value in (('comparisons',old['comparisons'][1:]),('auxiliaries',old['auxiliaries'][:-1]),
                      ('interfaces',{**old['interfaces'],'extra':'height_slack'})):
        bad=copy.deepcopy(old);bad[key]=value;mutations.append(bad)
    for name in (old['interfaces']['h'],'height_84'):
        bad=copy.deepcopy(old)
        bad['source']=[(n,'-',a,b) if n==name else (n,op,a,b) for n,op,a,b in bad['source']]
        mutations.append(bad)
    mutations.append(build())
    for bad in mutations:
        try:rewrite(bad)
        except (AssertionError,KeyError,TypeError):rejected+=1
        else:raise AssertionError('incompatible caller accepted')
    return dict(rejected_incompatible_callers=rejected)


def verify():
    fixtures=[(TABLE,PRIMES),((('I',2,1),),(5,3,2)),((('I',0,1),),(5,3,2)),
              ((('D',0,1,1),),PRIMES[:3]),
              ((('T',1,1,2),('I',0,2)),PRIMES[:3]),
              ((('I',3,1),('D',2,2,2)),(5,3,2,23))]
    records=[]
    for f,(table,primes) in enumerate(fixtures):
      for form in ('units','coupled'):
        packet=build(table,form,primes);parent.closure(packet)
        before=ledger(packet['terminal_height_parent']);after=ledger(packet)
        for key in ('certificate','product','SOS'):
            expected=dict(before[key]);expected['operations']-=1;expected['additions_subtractions']-=1
            assert after[key]==expected
        records.append(dict(fixture=f,form=form,ledger=after,
                            identities=identity_audit(packet,seed=537000+len(records)),
                            sharing=shared_audit(packet,seed=536000+len(records))))
    packet=build();default=ledger(packet);source,out=polynomial_source(packet)
    assert default['product']['operations']==537 and default['product']['multiplications']==193
    assert default['product']['additions_subtractions']==344 and default['product']['degree_upper_bound']==5091
    return dict(status='PASS_SPARSE_TERMINAL_BOUND537',default_ledger=default,
                ledgers=records,polynomial_schedule=source,output=out,
                source_sha256=hashlib.sha256(json.dumps(source).encode()).hexdigest(),
                bounds=bound_audit(),paths=path_audit(),guards=guards_audit(),
                scope='Complete ordinary-input universality with terminal bound derived from transport. Positive forward completeness map; integer affine inverse may be nonpositive.')


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--write',action='store_true')
    args=parser.parse_args();result=verify();path=Path(__file__).with_suffix('.json')
    if args.write:path.write_text(json.dumps(result,indent=2)+'\n')
    else:assert json.loads(path.read_text())==json.loads(json.dumps(result))
    print(result['status']);print(result['default_ledger'])
