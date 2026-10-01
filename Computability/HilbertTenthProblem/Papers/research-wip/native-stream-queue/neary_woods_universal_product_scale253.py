"""One paid product types both U9 history radices and saves one multiplication.

The top history tags become2 and1. The already-paid b*P^9 becomes the
high native scale, replacing the private P^11 multiplication. This preserves
the accepted-input relation with fresh joint-native positive witnesses,
not the original polynomial values or supplied native zero tuples.
"""
import argparse
from collections import Counter
import copy
import hashlib
import json
from pathlib import Path
import random

import neary_woods_universal_native_bound254 as parent
import native_binary_positive_scale as graph

compiler,execute=parent.compiler,parent.execute
polynomial_source,degree_bound=parent.polynomial_source,parent.degree_bound
P='hist__P__10';B='hist__B__3';P9='hist__P9__86';DELETED='hist__P11__99'
HIGH_SCALE='hist__top_history__87';TOP_TWO='hist__top_mask__92'
H='hist__joined_H__89';M='hist__joined_M__95';Z='hist__joined_Z__96'
HLOW='hist__joined_H__88';MLOW='hist__joined_M__94';LOW='fusion_low_q'
CHANGES={TOP_TWO:('*',2,P9),H:('+',HLOW,TOP_TWO),M:('+',MLOW,P9),
         'and__q':('*',LOW,HIGH_SCALE)}


def guard(old):
    assert old.get('native_port_bound') and not old.get('product_history_scale')
    assert old==parent.rewrite(old['native_port_bound_parent']),'requires the complete native_bound254 caller'
    rows={n:(op,a,b) for n,op,a,b in old['source']}
    required={HIGH_SCALE:('*',B,P9),TOP_TWO:('*','hist__Bm1__8',P9),
              DELETED:('*',P9,'hist__P2__51'),H:('+',HLOW,HIGH_SCALE),
              M:('+',MLOW,TOP_TWO),'and__q':('*',LOW,DELETED),
              P9:('*','hist__P7__81','hist__P2__51'),
              'and__bs_X_bound':('+','factored_pack_inner','and__bound_beta')}
    assert all(rows.get(n)==r for n,r in required.items())
    users=lambda key:{n for n,_,a,b in old['source'] if key in(a,b)}
    assert users(DELETED)=={'and__q'} and users(HIGH_SCALE)=={H} and users(TOP_TWO)=={M}
    assert old['fusion_interfaces']['high_scale']==DELETED
    for key in ('comparisons','unit_factors','public_registers','interfaces','projected_coordinates'):
        assert not {DELETED,HIGH_SCALE,TOP_TWO}&parent.leaves(old.get(key)),key
    assert set(k for k,v in old['fusion_interfaces'].items() if v==DELETED)=={'high_scale'}


def rewrite(old):
    guard(old)
    source=[(n,*CHANGES.get(n,(op,a,b))) for n,op,a,b in old['source'] if n!=DELETED]
    source=graph.sort_source(source,old['parameters']+old['auxiliaries'])
    active=dict(old['fusion_interfaces'],high_scale=HIGH_SCALE)
    packet=graph.metadata(dict(old,source=source,fusion_interfaces=active,
        product_history_scale=True,product_history_scale_parent=old,
        product_history_scale_definition='q=fusion_low_q*B_history*P_history^9; top tags H=2,M=1,Z=0',
        product_history_scale_deleted=DELETED,
        product_history_changed_rows=CHANGES,
        historical_product_scale_fusion_interfaces=old['fusion_interfaces'],
        historical_history_packet_scope='Stored preceding source only; active high_scale is b*P^9 and top tags are2,1.',
        identical_complete_polynomial=False,affine_complete_polynomial_identity=False,
        triangular_complete_polynomial_identity=False,identical_positive_coordinates=False,
        identical_positive_zero_set=False,positive_zero_bijection=False,
        accepted_input_equivalence='The same valid shifted U9 program/input slices; rebuild private joint-native witnesses at the new prescribed scale.',
        product_history_extension_scope='All outer and geometry coordinates may be retained at zeros; no old/new supplied joint-native zero bijection asserted.'))
    compiler.check_source(packet)
    assert packet['operations']==old['operations']-1
    assert packet['multiplications']==old['multiplications']-1
    assert packet['additions_subtractions']==old['additions_subtractions']
    return packet


def build(*,normalized=('geo__','and__'),scaled=('geo__','and__'),merge_bound=True,partition=None,anchor=0):
    return rewrite(parent.build(normalized=normalized,scaled=scaled,merge_bound=merge_bound,
                                partition=partition,anchor=anchor))


def ledger(packet):
    source,out=polynomial_source(packet);old=packet['product_history_scale_parent']
    before,_=polynomial_source(old)
    parent.parent.old.inherited.loader.source_closure(source,out)
    c=Counter('M' if op=='*' else 'A' for _,op,_,_ in source)
    assert len(source)==len(before)-1
    assert packet['parameters']==old['parameters'] and packet['auxiliaries']==old['auxiliaries']
    assert packet['comparisons']==old['comparisons']
    bounds=degree_bound(packet)
    return dict(bound_is_program_E=packet['bound_is_program_E'],
        normalized_prefixes=packet['normalized_prefixes'],positive_scale_prefixes=packet['positive_scale_prefixes'],
        factor_partition=packet['factor_partition'],partition_anchor=packet['partition_anchor'],
        certificate={k:packet[k] for k in ('operations','multiplications','additions_subtractions','equations','witnesses')},
        polynomial=dict(operations=len(source),multiplications=c['M'],additions_subtractions=c['A'],
            degree_upper_bound=bounds['degree_upper_bound'],exact_degree_claimed=False),
        degree=bounds,parent_degree=degree_bound(old))


def overridden(source,values,overrides):
    env=dict(values)
    for n,op,a,b in source:
        x=env[a] if isinstance(a,str) else a;y=env[b] if isinstance(b,str) else b
        env[n]=overrides[n] if n in overrides else x+y if op=='+' else x-y if op=='-' else x*y
    return env


def audit(packet,seed,cases=8):
    rng=random.Random(seed);old=packet['product_history_scale_parent']
    source,out=polynomial_source(packet);os,oo=polynomial_source(old)
    for i in range(cases):
        draw=lambda:rng.randrange(1,5) if i<cases//2 else rng.randrange(-3,4)
        values={n:draw() for n in packet['parameters']+packet['auxiliaries']}
        fixed={n:draw() for n in compiler.NUMERALS}
        ss=compiler.materialize(source,fixed);bs=compiler.materialize(os,fixed)
        before=execute(bs,values)
        # Reconstruct four changed scalar values from the unaffected old cone.
        pp,bb,lo=before[P],before[B],before[LOW]
        substitutions={TOP_TWO:2*pp**9,H:before[HLOW]+2*pp**9,
                       M:before[MLOW]+pp**9,'and__q':lo*bb*pp**9}
        oracle=overridden(bs,values,substitutions);actual=execute(ss,values)
        assert all(actual[n]==oracle[n] for n,_,_,_ in packet['source'])
        assert actual[out]==oracle[oo]
        val=lambda v:actual[v] if isinstance(v,str) else v
        groups=[actual[n] for n in packet['group_products']]
        ordinary=[val(a)-val(b) for a,b in packet['comparisons'] if a not in packet['group_products']]
        anchor=packet['partition_anchor']
        ssq=sum(r*r for r in ordinary)+sum((v-1)**2 for j,v in enumerate(groups) if j!=anchor)
        expected=ssq if anchor is None else groups[anchor]*(1+ssq)-1
        assert actual[out]==expected
        # All non-joint-native factors and ordinary history/geometry ports remain unchanged.
        for name in packet['unit_factors']:
            if not name.startswith('and__'):assert before[name]==actual[name]
    return dict(complete_changed_port_source_outputs=cases,signed_assignments=cases//2)


def pretyping_audit():
    packet=build();roots=(H,M,Z,HLOW,MLOW,HIGH_SCALE)
    cone=parent.cone(packet,roots);rng=random.Random(2531147);tally=Counter()
    for D in (1,2,3,8):
     for c in (32,64):
      b=c*D
      for J in (1,2,3,7):
       for sign in (-1,1):
        pp=(b-1)*J+sign
        for tile in range(4):
         for corner in range(6):
          parts=[1]*6;parts[corner]+=pp-6
          vals={n:1 for n in packet['parameters']+packet['auxiliaries']}
          vals.update(hist__height_slack=D,hist__H_U=parts[0],hist__H_V=parts[1],
              hist__ZUhat0=parts[2],hist__ZVhat0=parts[3],hist__ZVhat1=parts[4],hist__global_bound=parts[5])
          vals['hist__Shat'+str(tile)]=J+1
          fixed={n:1 for n in compiler.NUMERALS};fixed['history_radix']=c
          e=execute(compiler.materialize(cone,fixed),vals);T=pp**9
          assert e[P]==pp and e[B]==b
          assert all(0<=e[n]<T for n in (HLOW,MLOW,Z))
          assert e[H]==e[HLOW]+2*T and e[M]==e[MLOW]+T and e[HIGH_SCALE]==b*T
          assert e[H]-e[Z]>=T+1 and e[M]-e[Z]>=1
          assert e[HIGH_SCALE]-e[H]-e[M]+e[Z]>=(b-5)*T+2
          # Arbitrary legitimate padded low ports, not presumed AND values.
          lo=16*rng.randrange(1,33)
          aa=12+16*rng.randrange(lo//16);bb=10+16*rng.randrange(lo//16);zz=8+16*rng.randrange(lo//16)
          A=aa+lo*e[H];Bport=bb+lo*e[M];Zp=zz+lo*e[Z];q=lo*b*T
          fs=(q-A-Bport+Zp-1,A-Zp,Bport-Zp,Zp)
          assert min(fs)>0 and sum(fs)==q-1 and tuple(v%16 for v in fs)==(1,4,2,8)
          r=sum(v*q**i for i,v in enumerate(fs));S=A+1+(q+1)*(Bport+(q-1)*Zp)
          assert r==(q-1)*S and q*(S+1)>r and r>q
          tally['pretyping_contexts']+=1;tally['height_one_contexts']+=D==1
          tally['negative_repunit_contexts']+=sign<0;tally['nondyadic_contexts']+=bool(pp&(pp-1) or b&(b-1))
    return dict(tally)


def binary_audit():
    rng=random.Random(253915);top=mersenne=0
    for b in (32,64,256):
     for pp in (2,4,8,32,64,256):
      T=pp**9
      for _ in range(24):
       h,m=(rng.randrange(T) for _ in range(2));z=h&m
       assert (h+2*T)&(m+T)==z
       assert (h+b*T)&(m+(b-1)*T)==z
       assert max(h+2*T,m+T,z)<b*T
       top+=1
    for exponent in range(5,18):
     for n in range(1,193):
      assert ((1<<n)+1)%((1<<exponent)-1)!=0;mersenne+=1
    return dict(new_old_top_AND_identities=top,negative_dyadic_repunit_exclusions=mersenne)


def outer_histories():
    import binary_tag_four_tile_history as tag
    import pcp_affine_slope_class_history as selected
    history=tag.build()['raw_packet']['history_packet'];rng=random.Random(2531611)
    count=rows=lowcases=0
    for length in range(1,7):
     for repeat in range(8):
      word=tuple(rng.randrange(4) for _ in range(length))
      vals=selected.positive_outer_fixture(history,word,rng.randrange(1,6));e=execute(history['source'],vals)
      iface=history['interfaces'];h,m,z,b,p=[e[iface[k]] for k in ('H','M','Z','B','P')]
      T=p**9;newh=h-b*T+2*T;newm=m-(b-1)*T+T;Q=b*T
      assert h&m==z and newh&newm==z and max(newh,newm,z)<Q
      assert all(e[a]==e[b] for a,b in history['comparisons'][:3])
      # Genuine recoder AND combined with this independently typed affine history.
      k=3+repeat%3;n=1<<(1+repeat%3);q0=1<<n;Qr=q0**k;Br=(1<<(k-1))*Qr
      Pr=Br**n;J=(Pr-1)//(Br-1);S=q0*Pr;K=(S-1)//(2*Br-1)
      assert (2*Br-1)*K+1==S
      x=rng.randrange(1,q0);a=(x*J)&K
      lowq=16*Br*S;la=16*(Br*x*J+n)+12;lm=16*(Br*K+n-1)+10;lz=16*Br*a+8
      assert la&lm==lz and max(la,lm,lz)<lowq
      A=la+lowq*newh;Mport=lm+lowq*newm;Zport=lz+lowq*z
      assert A&Mport==Zport and max(A,Mport,Zport)<lowq*Q
      count+=1;rows+=length;lowcases+=1
    return dict(genuine_affine_histories=count,chronological_rows=rows,genuine_recoder_history_concatenations=lowcases,
        scope='Actual affine histories and recoder outputs; not complete fixed-program U9 or native Pell zeros.')


def guard_audit():
    old=parent.build();bad=[]
    for name in (HIGH_SCALE,TOP_TWO,DELETED):
        p=copy.deepcopy(old);p['source'].append(('private_leak','+',name,1));bad.append(p)
    for key in ('fusion_interfaces','public_registers'):
        p=copy.deepcopy(old);p[key]=dict(nested=[None,dict(leak=DELETED)]);bad.append(p)
    bad.append(rewrite(old))
    for p in bad:
        try:rewrite(p)
        except (AssertionError,KeyError,TypeError):pass
        else:raise AssertionError('invalid caller accepted')
    return len(bad)


def verify():
    records=[];sources=[];totals=Counter()
    for interface in (False,True):
     for n in parent.parent.old.NORMALIZATIONS:
      for s in parent.parent.old.SCALE_OPTIONS:
       if 'and__' not in s:continue
       old=parent.build(normalized=n,scaled=s,merge_bound=interface);count=len(old['unit_factors'])
       variants=[old]
       groups=[list(range(j,count,3)) for j in range(3)]
       variants += [parent.build(normalized=n,scaled=s,merge_bound=interface,partition=groups,anchor=a) for a in (None,0)]
       for previous in variants:
        p=rewrite(previous);rec=ledger(p);rec['audit']=audit(p,253000+len(records));records.append(rec);totals.update(rec['audit'])
        if len(p['group_products'])==1:
         source,out=polynomial_source(p);encoded=compiler.encode_source(source)
         sources.append(dict(ledger=rec,source=encoded,output=out,parameters=p['parameters'],auxiliaries=p['auxiliaries'],
            source_sha256=hashlib.sha256(json.dumps(encoded,sort_keys=True).encode()).hexdigest()))
    default=ledger(build())
    assert default['polynomial']==dict(operations=253,multiplications=132,additions_subtractions=121,degree_upper_bound=1147,exact_degree_claimed=False)
    return dict(status='PASS_NEARY_WOODS_UNIVERSAL_PRODUCT_SCALE253',default=default,
        records=records,canonical_sources=sources,audit_totals=dict(totals),
        pretyping=pretyping_audit(),binary=binary_audit(),outer=outer_histories(),rejected_callers=guard_audit(),
        scope='Complete unchanged valid shifted U9 program/input slices with fresh joint-native extensions. Eight inherited bases and both duration interfaces; illustrative grouped schedules, no new exhaustive optimization.')


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--write',action='store_true');args=parser.parse_args()
    result=json.loads(json.dumps(verify()));path=Path(__file__).with_suffix('.json')
    if args.write:path.write_text(json.dumps(result,indent=2)+'\n')
    else:assert json.loads(path.read_text())==result,'receipt mismatch'
    print(result['status']);print(result['default']['polynomial']);print(result['audit_totals']);print(result['pretyping']);print(result['outer'])
