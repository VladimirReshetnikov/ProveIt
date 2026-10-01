"""Compute sparse scale from a positive bound, then recover its repunit sign.

The complete proof separates native power recovery from the later AND
theorem. No off-zero equality with the old full polynomial is asserted.
"""
import argparse
from collections import Counter
import copy
import hashlib
import json
from math import prod
from pathlib import Path
import random

import residue_affine_sparse_bound540 as parent

TABLE,PRIMES=parent.TABLE,parent.PRIMES
units,ps=parent.units,parent.ps
execute,at=parent.execute,parent.at
polynomial_source,ledger=units.polynomial_source,units.ledger


def rewrite(old):
    assert old['form'] in ('units','coupled') and not old.get('sparse_positive_bound_scale')
    expected=parent.build(old['table'],old['form'],old['primes'],old['shared'])
    assert old==expected,'requires the complete canonical sparse540 packet'
    nodes={n:(op,a,b) for n,op,a,b in old['source']}
    bound,P=old['comparisons'][0]
    assert P==old['interfaces']['P'] and nodes[P][0::2]==('+',1)
    multiple=nodes[P][1]
    assert nodes[multiple][0]=='*' and nodes[multiple][2]==old['interfaces']['J']
    B=old['interfaces']['B'];Bm=nodes[multiple][1]
    assert nodes[Bm]==('-',B,1)
    assert nodes[bound]==('+',old['bound_chain'][-2],'global_slack')
    assert not any(bound in (a,b) for _,_,a,b in old['source'])
    assert [pair for pair in old['comparisons'] if bound in pair]==[(bound,P)]
    assert bound not in parent.leaves(old['interfaces'])
    assert old['comparisons'][-1]==(old['unit_register'],1)
    factor,unit='sparse_repunit_unit','sparse_all_units'
    assert factor not in nodes and unit not in nodes
    source=[(n,*nodes[bound]) if n==P else row
            for row in old['source'] for n in [row[0]] if n!=bound]
    source += [(factor,'-',P,multiple),(unit,'*',old['unit_register'],factor)]
    source=ps.sort_source(source,old['parameters']+old['auxiliaries'])
    ps.checked_source(source,old['parameters'],old['auxiliaries'])
    result=ps.metadata(dict(old,source=source,comparisons=old['comparisons'][1:-1]+[(unit,1)],
        unit_register=unit,unit_factors=old['unit_factors']+[factor],
        sparse_positive_bound_scale=True,sparse_scale_parent=old,
        deleted_bound_register=bound,repunit_multiple=multiple,repunit_factor=factor,
        bound_definition='P=V+increment_selected_hat+decrement_selected_hat+global_slack',
        equivalence_scope='Identical positive zeros on the supplied coordinates after the repunit sign is proved; no off-zero identity.'))
    assert result['operations']==old['operations']+1
    assert result['multiplications']==old['multiplications']+1
    assert result['additions_subtractions']==old['additions_subtractions']
    assert result['equations']==old['equations']-1
    return result


def build(table=TABLE,form='coupled',primes=PRIMES,shared=True):
    return rewrite(parent.build(table,form,primes,shared))


def closure(packet):
    parent.coupled.closure(packet)
    parent.coupled.closure(packet,True)


def replay(rows,values,overrides=None):
    """Separate interpreter with explicit fixed register-value interventions."""
    env=dict(values);overrides={} if overrides is None else overrides
    for n,op,a,b in rows:
        if n in overrides:
            env[n]=overrides[n];continue
        a=a if type(a)is int else env[a]
        b=b if type(b)is int else env[b]
        env[n]=a+b if op=='+' else a-b if op=='-' else a*b
    return env


def source_audit(packet,cases=32,seed=538000):
    old=packet['sparse_scale_parent'];rng=random.Random(seed)
    source,out=polynomial_source(packet)
    sos,so=polynomial_source(packet,sum_of_squares=True)
    counts=Counter()
    for case in range(cases):
        signed=case>=cases//2
        values={n:rng.randrange(-3,4) if signed else rng.randrange(1,5)
                for n in packet['parameters']+packet['auxiliaries']}
        env=execute(source,values);P=env[packet['interfaces']['P']]
        before=replay(old['source'],values,{old['interfaces']['P']:P})
        assert all(env[n]==before[n] for n,_,_,_ in old['source'] if n!=packet['deleted_bound_register'])
        factor=P-before[packet['repunit_multiple']]
        assert env[packet['repunit_factor']]==factor
        unit=prod(before[n] for n in old['unit_factors'])*factor
        rr=[at(before,a)-at(before,b) for a,b in old['comparisons'][1:-1]]
        assert env[out]==unit*(1+sum(r*r for r in rr))-1
        assert execute(sos,values)[so]==(unit-1)**2+sum(r*r for r in rr)
        counts['complete_finalizer_and_register_identities']+=2
        counts['signed_assignments']+=signed
        # Force the exact +1 repunit locus algebraically by its private slack.
        preliminary=replay(old['source'],values)
        adjusted=dict(values)
        adjusted['global_slack']+=preliminary[old['interfaces']['P']]-preliminary[packet['deleted_bound_register']]
        aa=replay(old['source'],adjusted);bb=replay(packet['source'],adjusted)
        assert aa[old['interfaces']['P']]==bb[packet['interfaces']['P']]
        assert bb[packet['repunit_factor']]==1
        assert all(aa[n]==bb[n] for n,_,_,_ in old['source'] if n!=packet['deleted_bound_register'])
        oldsource,oldout=polynomial_source(old)
        assert replay(oldsource,adjusted)[oldout]==replay(source,adjusted)[out]
        oldss,oldso=polynomial_source(old,sum_of_squares=True)
        assert replay(oldss,adjusted)[oldso]==replay(sos,adjusted)[so]
        counts['conditional_complete_parent_identities']+=2
        counts['nonpositive_algebraic_slacks']+=adjusted['global_slack']<=0
    return dict(counts)


def shared_audit(packet,cases=24,seed=538001):
    plain=build(packet['table'],packet['form'],packet['primes'],False)
    rng=random.Random(seed);counts=Counter()
    for case in range(cases):
        signed=case>=cases//2
        values={n:rng.randrange(-3,4) if signed else rng.randrange(1,5)
                for n in packet['parameters']+packet['auxiliaries']}
        for sos in (False,True):
            ss,so=polynomial_source(packet,sum_of_squares=sos)
            bs,bo=polynomial_source(plain,sum_of_squares=sos)
            e,b=execute(ss,values),replay(bs,values)
            assert e[so]==b[bo]
            assert all(at(e,n)==at(b,plain['interfaces'][k]) for k,n in packet['interfaces'].items())
            counts['complete_shared_unshared_identities']+=1
        counts['signed_assignments']+=signed
    return dict(counts)


def weak_bound_audit():
    counts=Counter()
    # Scalar pretyping corners, including masks that reach P+1.
    for B in (32,64,128,256,1024):
      for h in (4,8):
       if B<=3*7*h:continue
       for J in range(1,8):
        for sign in (-1,1):
            P=(B-1)*J+sign
            assert P>=3 and J<P
            assert (7-2)*J<P and (h-1)*J<P
            for L in (4,8,9,16,48):
                series=(P**L-1)//(P-1)
                H=(P-1)*series;M=(P+1)*series;Z=H
                a=1
                while a<L:a*=2
                Q=B*P**a
                assert H<P**L and Z<P**L and M<2*P**L<Q
                counts['weak_repunit_packed_bound_cases']+=1
                counts['negative_repunit_cases']+=sign==-1
    for exponent in range(3,20):
      B=2**exponent
      for power in range(0,8*exponent):
        assert (pow(2,power,B-1)+1)%(B-1)!=0
        if (pow(2,power,B-1)-1)%(B-1)==0:assert power%exponent==0
        counts['dyadic_repunit_sign_and_order_cases']+=1
    # Native reconstruction before coupling its checksum to the new sign.
    for r in (4369,5000,65535,100000):
      for epsilon in (-1,1):
       for checksum in (-1,1):
        K=r+epsilon;rp=K-1;p=2*K-1
        assert rp>156 and p==2*rp+1
        assert (2*r-3)<=p<=(2*r+1)
        assert r+1>rp
        counts['independent_native_sign_reconstructions']+=1
    return dict(counts)


def path_audit():
    rng=random.Random(538777);fixtures=[(TABLE,PRIMES)]
    for size in range(1,7):
      for _ in range(3):
        table=[]
        for q in range(size):
            op=rng.choice(('I','D','T'));reg=rng.randrange(4)
            table.append((op,reg,*[rng.randrange(q+1,size+1) for _ in range(1 if op=='I' else 2)]))
        fixtures.append((tuple(table),PRIMES[:4]))
    histories=steps=wrong=0
    for table,primes in fixtures:
        packet=build(table,primes=primes)
        rows=[row for row in packet['source'] if not row[0].startswith('native__') and row[0]!='sparse_all_units']
        for code in (0,1,2):
          for x in (1,2,4):
            states,chosen=parent.parent.payload_run(table,3**code,x,primes,limit=60)
            if states[-1][0]!=len(table)+1:continue
            values=parent.pack_path(packet,states,chosen,x)
            env=replay(rows,values);ports=packet['interfaces']
            assert env[packet['repunit_factor']]==1
            assert all(at(env,a)==at(env,b) for a,b in packet['comparisons'][:4])
            assert at(env,ports['joined_H']) & at(env,ports['joined_M'])==at(env,ports['joined_Z'])
            assert at(env,ports['P'])==at(env,ports['B'])**len(chosen)
            if values['height_slack']>1:
                bad={**values,'input':x+1,'height_slack':values['height_slack']-1}
                be=replay(rows,bad)
                assert be[packet['repunit_factor']]==1
                assert all(at(be,a)==at(be,b) for a,b in packet['comparisons'][:3])
                a,b=packet['comparisons'][3];assert at(be,a)-at(be,b)==-1;wrong+=1
            histories+=1;steps+=len(chosen)
    return dict(tables=len(fixtures),halted_histories=histories,chronological_rows=steps,
                wrong_input_rejections=wrong,
                scope='Outer histories and exact repunit locus, not materialized native Pell zeros.')


def guards_audit():
    old=parent.build();rejected=0
    for key,value in (('comparisons',old['comparisons'][1:]),('auxiliaries',old['auxiliaries'][:-1]),
                      ('interfaces',{**old['interfaces'],'bad':old['comparisons'][0][0]})):
        bad=copy.deepcopy(old);bad[key]=value
        try:rewrite(bad)
        except (AssertionError,KeyError,TypeError):rejected+=1
        else:raise AssertionError('malformed canonical caller accepted')
    for name in (old['interfaces']['P'],old['comparisons'][0][0]):
        bad=copy.deepcopy(old)
        bad['source']=[(n,'-',a,b) if n==name else (n,op,a,b) for n,op,a,b in old['source']]
        try:rewrite(bad)
        except (AssertionError,KeyError,TypeError):rejected+=1
        else:raise AssertionError('modified scale source accepted')
    return dict(rejected_incompatible_callers=rejected)


def verify():
    fixtures=[(TABLE,PRIMES),((('I',2,1),),PRIMES[:3]),
              ((('D',0,1,1),),PRIMES[:3]),
              ((('T',1,1,2),('I',0,2)),PRIMES[:3]),
              ((('I',3,1),('D',2,2,2)),(5,3,2,23))]
    records=[]
    for f,(table,primes) in enumerate(fixtures):
      for form in ('units','coupled'):
        packet=build(table,form,primes);closure(packet)
        records.append(dict(fixture=f,form=form,ledger=ledger(packet),
                            source_audit=source_audit(packet,seed=538000+len(records)),
                            sharing=shared_audit(packet,seed=539000+len(records))))
    packet=build();default=ledger(packet);source,out=polynomial_source(packet)
    assert default['product']['operations']==538
    assert default['product']['multiplications']==193
    assert default['product']['additions_subtractions']==345
    return dict(status='PASS_SPARSE_POSITIVE_BOUND_SCALE538',default_ledger=default,
                ledgers=records,polynomial_schedule=source,output=out,
                source_sha256=hashlib.sha256(json.dumps(source).encode()).hexdigest(),
                weak_bounds=weak_bound_audit(),paths=path_audit(),guards=guards_audit(),
                scope='Complete ordinary-input universality inherited from sparse540; same positive zeros after recovering the new repunit sign. No arbitrary-point parent identity.')


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--write',action='store_true')
    result=verify();args=parser.parse_args();path=Path(__file__).with_suffix('.json')
    if args.write:path.write_text(json.dumps(result,indent=2)+'\n')
    else:assert json.loads(path.read_text())==json.loads(json.dumps(result))
    print(result['status']);print(result['default_ledger'])
