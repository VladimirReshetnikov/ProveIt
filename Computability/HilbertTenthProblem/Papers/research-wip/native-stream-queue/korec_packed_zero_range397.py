"""One selected range mask also enforces the U21 zero branches.

397 operations with one program parameter,396 with a second radix parameter.
Narrowing the global range bound is essential before native field typing.
"""
import argparse
from collections import Counter
from functools import lru_cache
import hashlib
import json
from pathlib import Path
import random
import sympy as sp

import korec_packed_minimal_radix405 as parent

core=parent.core
execute,polynomial_source,degree_bound,ledger=parent.execute,parent.polynomial_source,parent.degree_bound,parent.ledger
FORMS=parent.FORMS
INNER='counter_factored_inner_sum'
S=parent.S
DELETED={'counter_radix_minus_one_147','zero_mask_148','zero_lane_324',
    'second_counter_pack_321','H_322','native__scaled_A',
    'counter_factored_q_plus_one','counter_factored_A_plus_one','scale_power_328'}
CHANGES={
    'counter_digit_mask_92':('*','counter_repunit_91','partition_66'),
    'counter_M_325':('-','counter_digit_mask_92','Z_sum_146'),
    'range_mask_93':('*','counter_half_minus_one_84','counter_M_325'),
    'counter_M_shift_326':('*','repeat_square_252','range_mask_93'),
    'scale_power_329':('*','repeat_square_252','scale_83'),
    'counter_factored_Z':('*','native__q','native__F3'),
    'counter_factored_B':('+','native__padded_B','counter_factored_Z'),
    'counter_factored_scaled_B':('*','native__q','counter_factored_B'),
    S:('+',INNER,5)}
ALIASES={'H_322':'Z_320','native__scaled_A':'native__scaled_Z'}


@lru_cache(None)
def build(form='units',*,program_radix=False):
    return rewrite(parent.build(form,program_radix=program_radix))


def rewrite(old):
    pr=old.get('counter_program_radix')
    assert type(pr) is bool and old.get('form') in FORMS
    assert old==parent.build(old['form'],program_radix=pr),'requires the complete canonical minimal-radix405 caller'
    assert old['table']==core.TABLE and old['registers']==8 and len(old['edges'])==34
    assert old['c']==1 and old['scale_exponent']==64
    rows={n:(op,a,b) for n,op,a,b in old['source']}
    required={
        'counter_digit_mask_92':('*','counter_half_minus_one_84','counter_repunit_91'),
        'range_mask_93':('*','counter_digit_mask_92','partition_66'),
        'counter_M_325':('+','range_mask_93','zero_lane_324'),
        'counter_M_shift_326':('*','repeat_square_252','counter_M_325'),
        'scale_power_328':('*','repeat_square_247','repeat_square_247'),
        'scale_power_329':('*','scale_power_328','scale_power_328'),
        'native_scale_330':('*','D8_79','scale_power_329'),
        'native__scaled_A':('*',16,'H_322'),
        'native__scaled_Z':('*',16,'Z_320'),
        'native__bs_X_bound':('+',S,parent.GAP)}
    assert all(rows.get(n)==v for n,v in required.items())
    for key in ('parameters','auxiliaries','comparisons','outer_pairs','unit_factors','unit_register','public_registers'):
        assert not DELETED&parent.parent.leaves(old.get(key)),key
    assert INNER not in rows
    source=[(n,*CHANGES.get(n,(op,a,b))) for n,op,a,b in old['source'] if n not in DELETED]
    source.append((INNER,'+','counter_factored_scaled_B','native__padded_B'))
    source=[(n,op,ALIASES.get(a,a),ALIASES.get(b,b)) for n,op,a,b in source]
    source=core.ps.sort_source(source,old['parameters']+old['auxiliaries'])
    interfaces={k:ALIASES.get(v,v) for k,v in old['interfaces'].items() if k!='zm'}
    interfaces['zero_selector']='Z_sum_146'
    packet=core.ps.metadata(dict(old,source=source,interfaces=interfaces,
        scale_exponent=35,counter_zero_range=True,zero_range_parent=old,
        zero_range_definition='Rstar=(h-1)*(J*sum(D^j,j=0..7)-Zword); the global range bound uses Rstar',
        factored_index_identity='A=Zport+4; S=5+Bport+q*(Bport+q*Zport), r=(q-1)*S',
        native_scale_definition='Q=B*P^35 using the already paid P^34 and P',
        identical_complete_polynomial=False,identical_positive_coordinates=False,
        positive_zero_set_scope='Same fixed-program accepted-input relation, with a new range slack and fresh private native extension; no same-tuple or triangular identity to the parent.',
        historical_zero_range_interfaces=old['interfaces'],
        historical_parent_metadata_scope='Stored parent packets describe preceding graphs; their lifts and packing helpers are not current zero-range maps.'))
    live=set(packet['parameters']+packet['auxiliaries'])|{n for n,_,_,_ in source}
    for key in ('canonical_native_registers','private_restoration_coordinates'):
        if key in packet:packet[key]=[n for n in packet[key] if n in live]
    core.ps.checked_source(source,packet['parameters'],packet['auxiliaries']);core.closure(packet)
    assert packet['operations']==old['operations']-8
    assert packet['multiplications']==old['multiplications']-5
    assert packet['additions_subtractions']==old['additions_subtractions']-3
    return packet


def oracle(packet,v):
    pr=packet['counter_program_radix'];E,x=v['program'],v['input']
    h=x+v['height_slack'] if pr else E+x+v['height_slack']
    D=(v['radix_program'] if pr else 2)*h;B=D**8
    es=[v[f'edge{i}_hat']-1 for i in range(34)];J=sum(es);P=(B-1)*J+1
    W=v['counter_word_hat']-1;Y=v['final_counter_hat']-1
    action={op:sum(e*D**row[3] for e,row in zip(es,packet['edges'])
        if row[2]==op or row[2]=='P' and op in ('I','D')) for op in ('I','D','Z')}
    rep=sum(D**i for i in range(8));Rstar=(h-1)*(J*rep-action['Z'])
    H=sum(e*P**i for i,e in enumerate(es))+P**34*W
    M=J*sum(P**i for i in range(34))+P**34*Rstar;Q=B*P**35
    code=lambda state:0 if state==len(core.TABLE) else packet['codes'][state][1]*D**packet['codes'][state][0]
    current=sum(e*code(row[0]) for e,row in zip(es,packet['edges']))
    following=sum(e*code(row[1]) for e,row in zip(es,packet['edges']))
    residuals=[W+1+v['global_slack']-Rstar,
        B*(W+action['I'])+E*D+x*D**2-W-action['D']-P*Y,
        B*following+D-current]
    return dict(D=D,B=B,J=J,P=P,W=W,Y=Y,rm=Rstar,ah=H,am=M,az=H,scale=Q,
        zero_selector=action['Z']),residuals,dict(h=h,rep=rep)


def replay_overrides(packet,v):
    o,_,extra=oracle(packet,v);q=16*o['scale'];Zp=16*o['az']+8;Bp=16*o['am']+10
    # Replaying the OLD complete source with explicit changed scalar definitions
    # is only an algebra audit of this new recipe, not a parent-polynomial identity.
    return {'counter_digit_mask_92':extra['rep']*o['J'],
        'counter_M_325':extra['rep']*o['J']-o['zero_selector'],
        'range_mask_93':o['rm'],'counter_M_shift_326':o['P']**34*o['rm'],
        'H_322':o['ah'],'scale_power_329':o['P']**35,
        'counter_factored_Z':q*Zp,'counter_factored_B':Bp+q*Zp,
        'counter_factored_scaled_B':q*(Bp+q*Zp),S:5+Bp+q*(Bp+q*Zp)}


def overridden(source,values,overrides):
    env=dict(values)
    for n,op,a,b in source:
        a=env[a] if isinstance(a,str) else a;b=env[b] if isinstance(b,str) else b
        env[n]=overrides[n] if n in overrides else a*b if op=='*' else a+b if op=='+' else a-b
    return env


def audit(packet,seed,cases=24):
    rng=random.Random(seed);old=packet['zero_range_parent'];totals=Counter()
    for case in range(cases):
        signed=case>=cases//2;draw=lambda:rng.randrange(-2,4) if signed else rng.randrange(1,4)
        v={n:draw() for n in packet['parameters']+packet['auxiliaries']}
        e=execute(packet['source'],v);o,res,_=oracle(packet,v);at=lambda n:e[n] if isinstance(n,str) else n
        assert all(at(n)==o[k] for k,n in packet['interfaces'].items())
        assert [at(a)-at(b) for a,b in packet['outer_pairs']]==res
        overrides=replay_overrides(packet,v)
        for sos in (False,True):
            ns,no=polynomial_source(packet,sum_of_squares=sos);os,oo=polynomial_source(old,sum_of_squares=sos)
            before=overridden(os,v,overrides);new=execute(ns,v)
            assert all(new[n]==before[n] for n,_,_,_ in packet['source'] if n!=INNER)
            assert new[no]==before[oo]
            totals['complete_changed_recipe_register_outputs']+=1
        totals['signed_assignments']+=signed
    return dict(totals)


def pack_history(packet,configs,chosen,E,x,C=None):
    v=parent.pack_history(packet['zero_range_parent'],configs,chosen,E,x,C)
    o,_,_=oracle(packet,v)
    v['global_slack']=o['rm']-o['W']-1-int(packet.get('counter_outer_units',False))
    assert min(v.values())>0
    return v


def histories():
    totals=Counter()
    for E in range(1,16):
     for x in range(1,4):
      cs,es=parent.interpreter(E,x,limit=700)
      if cs[-1][0]!=len(core.TABLE) or len(es)>250:continue
      C=1<<max(2,E.bit_length())
      for pr,c in ((False,None),(True,C),(True,2*C)):
       for form in FORMS:
        p=build(form,program_radix=pr);v=pack_history(p,cs,es,E,x,c)
        o,res,_=oracle(p,v);env=execute(parent.outer_source(p),v);at=lambda n:env[n] if isinstance(n,str) else n
        assert res==[-int(p.get('counter_outer_units',False)),0,0]
        assert all(at(n)==o[k] for k,n in p['interfaces'].items())
        assert o['ah']&o['am']==o['az'] and o['ah']==o['az']
        assert o['scale']>o['am'] and o['rm']-o['W']>2
        # The combined mask equals the original two typed requirements on this run.
        h=(x if pr else E+x)+v['height_slack'];oldrm=(h-1)*sum(o['D']**j for j in range(8))*o['J']
        assert o['W']&oldrm==o['W'] and o['W']&((o['D']-1)*o['zero_selector'])==0
        totals['actual_zero_range_packs']+=1;totals['chronological_rows']+=len(es)
      totals['halted_U21_histories']+=1
    return dict(totals)


def margins():
    totals=Counter();rng=random.Random(397361)
    p=build()
    for pr in (False,True):
     for h in ((3,4,7,8) if not pr else (2,3,4,8)):
      for C in ((2,) if not pr else (4,8)):
       D=C*h;B=D**8;rep=sum(D**j for j in range(8))
       for selected in range(34):
        for J in (1,2,7):
         es=[0]*34;es[selected]=J;P=(B-1)*J+1
         zero=sum(e*D**row[3] for e,row in zip(es,p['edges']) if row[2]=='Z')
         R=(h-1)*(J*rep-zero)
         assert 0<R< P and zero<=D**7*J and (h-1)*rep<B-1
         for sign in (-1,1):
          W=R-3;gamma=2-sign
          assert R-(W+1+gamma)==sign and W>=0
          H=sum(e*P**i for i,e in enumerate(es))+P**34*W
          M=J*sum(P**i for i in range(34))+P**34*R;Q=B*P**35
          assert H<Q and M<Q and M>H and Q-M>0
          q=16*Q;zp=16*H+8;bp=16*M+10;ap=zp+4
          fields=(q-ap-bp+zp-1,ap-zp,bp-zp,zp)
          assert min(fields)>0 and sum(fields)==q-1
          s=5+bp+q*(bp+q*zp);r=sum(f*q**i for i,f in enumerate(fields))
          assert r==(q-1)*s and q*(s+1)>r and r%16==1
          totals['pretyping_scalar_contexts']+=1;totals['negative_range_signs']+=sign<0
          totals['height_two_contexts']+=h==2
    # Every counter digit and addressed-zero choice in a small dyadic radix.
    for h in (2,4,8):
     D=2*h
     for zero in (None,0,1,2):
      r=(h-1)*sum(D**j for j in range(3))-(0 if zero is None else (h-1)*D**zero)
      for w in range(D**3):
       ds=[(w//D**j)%D for j in range(3)]
       expected=all(z<h for z in ds) and (zero is None or ds[zero]==0)
       assert ((w&r)==w)==expected
       totals['typed_digit_equivalences']+=1
    return dict(totals)


def symbolic():
    q,b,z=sp.symbols('q b z');a=z+4
    old=(q-1)*(a+1+(q+1)*(b+(q-1)*z))
    new=(q-1)*(5+b+q*(b+q*z))
    assert sp.expand(old-new)==0
    return str(sp.expand(new))


def guards():
    old=parent.build();bad=[dict(old,comparisons=[]),dict(old,public_registers={'leak':'H_322'}),
        dict(old,source=old['source'][:-1]),build()]
    for p in bad:
        try:rewrite(p)
        except (AssertionError,KeyError):pass
        else:raise AssertionError('noncanonical caller accepted')
    return len(bad)


def verify():
    records=[]
    for pr in (False,True):
     for form in FORMS:
      p=build(form,program_radix=pr);ss,out=polynomial_source(p)
      records.append(dict(program_radix=pr,form=form,ledger=ledger(p),audit=audit(p,397000+len(records)),
          source=ss,output=out,parameters=p['parameters'],auxiliaries=p['auxiliaries'],
          source_sha256=hashlib.sha256(json.dumps(ss,separators=(',',':')).encode()).hexdigest()))
    assert records[2]['ledger']['product']['operations']==397
    assert records[5]['ledger']['product']['operations']==396
    return dict(status='PASS_KOREC_PACKED_ZERO_RANGE397',records=records,
        symbolic_index=symbolic(),histories=histories(),margins=margins(),rejected_callers=guards(),
        scope='Canonical U21 accepted-input relation with a narrowed range bound, combined selector/range/zero lanes and prescribed scale B*P35. Rebuild private native witnesses. Both inherited program interfaces, three forms and both complete finalizers. Degree bounds only.')


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--write',action='store_true');args=parser.parse_args()
    result=json.loads(json.dumps(verify()));path=Path(__file__).with_suffix('.json')
    if args.write:path.write_text(json.dumps(result,indent=2)+'\n')
    else:assert json.loads(path.read_text())==result,'receipt mismatch'
    print(result['status'])
    for row in result['records']:print(row['program_radix'],row['form'],row['ledger']['product']['operations'],row['ledger']['product']['degree_upper_bound'])
    print(result['histories']);print(result['margins'])
