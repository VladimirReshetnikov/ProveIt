"""409-operation U21 tradeoff with a second fixed positive program parameter.

For valid recipes E>0, dyadic C>=4 and C>E, use h=x+eta and D=C*h.
"""
import argparse
from functools import lru_cache
import hashlib
import json
from pathlib import Path
import random

import korec_packed_positive_program410 as parent

core=parent.parent
polynomial_source=parent.polynomial_source
execute=parent.execute
ledger=parent.ledger
degree_bound=parent.degree_bound
HEIGHT='half_height_71'
D='counter_radix_72'
RADIX='radix_program'


@lru_cache(None)
def build(form='units'):
    return rewrite(parent.build(form))


def rewrite(old):
    form=old.get('form')
    assert form in parent.FORMS and old==parent.build(form),'requires the canonical positive410 U21 source'
    rows={n:(op,a,b) for n,op,a,b in old['source']}
    assert rows[parent.PARTIAL]==('+',parent.PROGRAM,'input')
    assert rows[HEIGHT]==('+',parent.PARTIAL,parent.SLACK)
    assert rows[D]==('+',HEIGHT,HEIGHT)
    assert [n for n,_,a,b in old['source'] if parent.PARTIAL in (a,b)]==[HEIGHT]
    source=[]
    for n,op,a,b in old['source']:
        if n==parent.PARTIAL:continue
        if n==HEIGHT:op,a,b='+','input',parent.SLACK
        if n==D:op,a,b='*',RADIX,HEIGHT
        source.append((n,op,a,b))
    packet=core.ps.metadata(dict(old,source=source,
        parameters=[parent.PROGRAM,RADIX,'input'],program_radix_parent=old,
        counter_program_radix=True,
        fixed_program_recipe='E>0; C dyadic, C>=4, C>E. The same E,C serve all ordinary inputs.',
        graph_identity_scope='Specialize C to a numeral in the corresponding parent radix; old eta=eta-E. No supplied-positive-zero-set equality.'))
    core.ps.checked_source(source,packet['parameters'],packet['auxiliaries']);core.closure(packet)
    assert packet['operations']==old['operations']-1
    assert packet['multiplications']==old['multiplications']+1
    assert packet['additions_subtractions']==old['additions_subtractions']-2
    return packet


def fixed_parent(packet,C):
    assert type(C) is int
    old=packet['program_radix_parent']
    return dict(old,source=[(n,'*',C,HEIGHT) if n==D else (n,op,a,b)
                           for n,op,a,b in old['source']])


def valid_recipe(E,C):
    return type(E) is int and type(C) is int and E>0 and C>=4 and C>E and C&(C-1)==0


def pack_history(packet,configs,chosen,E,x,C):
    assert valid_recipe(E,C) and type(x) is int and x>0
    assert chosen and len(configs)==len(chosen)+1 and configs[-1][0]==len(core.TABLE)
    assert configs[0]==(0,(0,E,x,0,0,0,0,0))
    h=1
    while h<=max([x+1]+[v+2 for _,rs in configs for v in rs]):h*=2
    d=C*h;B=2*d**8;P=B**len(chosen);J=(P-1)//(B-1)
    pack=lambda seq:sum(v*B**i for i,v in enumerate(seq))
    indices={(q,b):i for i,(q,b) in enumerate((q,b) for q,row in enumerate(core.TABLE) for b in range(len(row)-2))}
    selected=[indices[v] for v in chosen]
    values={f'edge{i}_hat':1+pack([int(i==e) for e in selected]) for i in range(len(packet['edges']))}
    words=[]
    for (_,rs),edge in zip(configs,selected):
        rs=list(rs);_,_,op,r=packet['edges'][edge]
        if op in ('D','P'):rs[r]-=1
        assert min(rs)>=0 and max(rs)<=h-3
        words.append(sum(v*d**i for i,v in enumerate(rs)))
    W=pack(words);Y=sum(v*d**i for i,v in enumerate(configs[-1][1]))
    rm=(h-1)*sum(d**i for i in range(8))*J
    values.update(program=E,radix_program=C,input=x,height_slack=h-x,
        counter_word_hat=W+1,final_counter_hat=Y+1,
        global_slack=rm-W-1-int(packet.get('counter_outer_units',False)))
    assert min(values.values())>0
    return values


def audit(packet,seed,cases=32):
    rng=random.Random(seed);bad=0
    for j in range(cases):
        signed=j>=cases//2
        values={n:rng.randrange(-3,4) if signed else rng.randrange(1,5)
                for n in packet['parameters']+packet['auxiliaries']}
        old=fixed_parent(packet,values[RADIX]);lifted={n:v for n,v in values.items() if n!=RADIX}
        lifted[parent.SLACK]-=values[parent.PROGRAM]
        env=execute(packet['source'],values);before=execute(old['source'],lifted)
        assert all(before[n]==env[n] for n,_,_,_ in packet['source'])
        for sos in (False,True):
            ss,out=polynomial_source(packet,sum_of_squares=sos)
            os,oo=polynomial_source(old,sum_of_squares=sos)
            assert execute(ss,values)[out]==execute(os,lifted)[oo]
        bad+=lifted[parent.SLACK]<=0
    assert degree_bound(fixed_parent(packet,8))==degree_bound(packet['program_radix_parent'])
    return dict(assignments=cases,signed=cases//2,complete_fixed_C_outputs=2*cases,
                nonpositive_formal_parent_slacks=bad)


def history_audit():
    packet=build();outer=[r for r in packet['source'] if not r[0].startswith(('native__','counter_outer_'))]
    cases=rows=0
    for E in range(1,10):
      C=1<<max(2,E.bit_length())
      for x in range(1,4):
        cs,es=core.run(core.TABLE,E,x,limit=700)
        if cs[-1][0]!=len(core.TABLE):continue
        for c in (C,2*C):
            values=pack_history(packet,cs,es,E,x,c);env=execute(outer,values)
            val=lambda v:env[v] if isinstance(v,str) else v
            for i,(a,b) in enumerate(packet['outer_pairs']):assert val(a)-val(b)==(-1 if i==0 else 0)
            z={k:val(v) for k,v in packet['interfaces'].items()}
            assert z['D']==c*(x+values[parent.SLACK])
            assert z['ah']&z['am']==z['az']
            assert z['scale']>z['ah']+z['am']-z['az']
            cases+=1;rows+=len(es)
    return dict(fixed_C_outer_packs=cases,chronological_rows=rows,
                scope='Actual U21 outer packs; no complete native Pell tuples materialized.')


def margins():
    rng=random.Random(40973);counts=0;minimum=0
    for C in (4,8,16,64):
      for h in (2,3,4,7,8):
       d=C*h;B=2*d**8
       for E in (1,C-1):
        for sign in (-1,1):
          edges=[rng.randrange(3) for _ in range(34)];J=sum(edges);P=(B-1)*J+1
          rm=(h-1)*sum(d**j for j in range(8))*J
          W=rm//2;gamma=rm-W-1-sign
          zero=sum(edges[i]*d**e[3] for i,e in enumerate(build()['edges']) if e[2]=='Z')
          zm=(d-1)*zero
          ep=sum(v*P**j for j,v in enumerate(edges));Z=ep+P**34*W
          H=Z+P**35*W;M=J*sum(P**j for j in range(34))+P**34*(rm+P*zm)
          Q=B*P**64
          assert min(gamma,J)>0 and 0<=W<rm<P and 0<=zm<P
          assert H>=Z and M>Z and Q>H+M-Z
          assert d-2>h and max(l for r,l in build()['codes'])<d-2
          assert E*d+(h-1)*d*d<B and E<d
          counts+=1;minimum+=h==2
    return dict(pretyping_and_digit_contexts=counts,height_two_contexts=minimum)


def verify():
    records=[]
    for i,form in enumerate(parent.FORMS):
        packet=build(form);ss,out=polynomial_source(packet)
        records.append(dict(form=form,ledger=ledger(packet),audit=audit(packet,409090+i),
            source=ss,output=out,parameters=packet['parameters'],auxiliaries=packet['auxiliaries'],
            source_sha256=hashlib.sha256(json.dumps(ss,separators=(',',':')).encode()).hexdigest()))
    assert records[-1]['ledger']['product']['operations']==409
    rejected=0
    for E,C in ((0,4),(1,2),(4,4),(8,4),(1,6)):
        assert not valid_recipe(E,C);rejected+=1
    for form in parent.FORMS:
        try:rewrite(dict(parent.build(form),parameters=['wrong']))
        except AssertionError:rejected+=1
        else:raise AssertionError('noncanonical parent accepted')
    return dict(status='PASS_KOREC_PACKED_PROGRAM_RADIX409',records=records,
        histories=history_audit(),margins=margins(),rejected_callers_and_recipes=rejected,
        scope='Complete U21 accepted-input relation for two fixed program parameters E,C on valid dyadic recipes. Uniform degree includes C; fixed-C output identities need not preserve positivity.')


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--write',action='store_true');args=parser.parse_args()
    result=json.loads(json.dumps(verify()));path=Path(__file__).with_suffix('.json')
    if args.write:path.write_text(json.dumps(result,indent=2)+'\n')
    else:assert json.loads(path.read_text())==result,'receipt mismatch'
    print(result['status']);print(result['records'][-1]['ledger']);print(result['histories']);print(result['margins'])
