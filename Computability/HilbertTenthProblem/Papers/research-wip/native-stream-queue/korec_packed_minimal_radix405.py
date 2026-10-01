"""Minimal time radix and a paid native port bound for the canonical U21.

One-program interface405; two-program radix interface404. Changing B from
2D^8 toD^8 requires a new chronology proof and fresh native extensions.
The triangular native-bound identity applies only at the new time radix.
"""
import argparse
from collections import Counter
from functools import lru_cache
import hashlib
import json
from pathlib import Path
import random

import korec_packed_factored_ports406 as parent

core=parent.core
execute,polynomial_source,degree_bound,ledger=parent.execute,parent.polynomial_source,parent.degree_bound,parent.ledger
FORMS=parent.FORMS
OLD_B='time_radix_80';B='D8_79';BOUND='native__bs_X_bound';GAP='native__bound_beta'
S=parent.S;INDEX=parent.INDEX


def alias_tree(value):
    if isinstance(value,str):return B if value==OLD_B else value
    if isinstance(value,dict):return {k:alias_tree(v) for k,v in value.items()}
    if isinstance(value,list):return [alias_tree(v) for v in value]
    if isinstance(value,tuple):return tuple(alias_tree(v) for v in value)
    return value


def cone(packet,roots):
    rows={n:(op,a,b) for n,op,a,b in packet['source']};seen=set();todo=list(roots)
    while todo:
        n=todo.pop()
        if isinstance(n,str) and n in rows and n not in seen:
            seen.add(n);todo.extend(rows[n][1:])
    return [row for row in packet['source'] if row[0] in seen]


def minimal_time_only(old):
    pr=bool(old.get('counter_program_radix'))
    assert old.get('form') in FORMS and old==parent.build(old['form'],program_radix=pr),'requires canonical factored U21 caller'
    rows={n:(op,a,b) for n,op,a,b in old['source']}
    assert rows[OLD_B]==('*',2,B) and rows[B]==('*','D4_75','D4_75')
    assert old['interfaces']['B']==OLD_B and old['c']==2 and old['registers']==8
    source=[(n,op,*alias_tree((a,b))) for n,op,a,b in old['source'] if n!=OLD_B]
    packet=dict(old,source=source,c=1,counter_program_radix=pr,counter_minimal_time_radix=True,
        counter_minimal_time_parent=old,time_radix_definition='B=D^8, with no outer coefficient',
        historical_time_radix_register=OLD_B,
        identical_complete_polynomial=False,identical_positive_coordinates=False,
        accepted_input_equivalence='Canonical U21 and the corresponding one- or two-program valid recipe, with fresh chronological packing/native extension.')
    for key in ('interfaces','comparisons','outer_pairs','unit_factors','unit_register','public_registers'):
        if key in packet:packet[key]=alias_tree(packet[key])
    live=set(packet['parameters']+packet['auxiliaries'])|{n for n,_,_,_ in source}
    for key in ('canonical_native_registers','private_restoration_coordinates'):
        if key in packet:packet[key]=[n for n in packet[key] if n in live]
    packet=core.ps.metadata(packet)
    core.ps.checked_source(source,packet['parameters'],packet['auxiliaries']);core.closure(packet)
    assert packet['operations']==old['operations']-1 and packet['multiplications']==old['multiplications']-1
    return packet


def rewrite(old):
    stage=minimal_time_only(old);rows={n:(op,a,b) for n,op,a,b in stage['source']}
    assert rows[BOUND]==('+',INDEX,GAP) and rows['native__wn2']==('*',BOUND,'native__q')
    assert rows[INDEX]==('*',parent.QMINUS,S)
    assert [n for n,_,a,b in stage['source'] if GAP in(a,b)]==[BOUND]
    assert GAP not in parent.leaves(cone(stage,(INDEX,S)))
    for key in ('interfaces','outer_pairs','comparisons','unit_factors','public_registers'):
        assert GAP not in parent.leaves(stage.get(key)),key
    source=[(n,op,S if n==BOUND else a,b) for n,op,a,b in stage['source']]
    packet=dict(stage,source=source,counter_paid_native_bound=True,counter_native_bound_parent=stage,
        native_bound_definition='X=q*(counter_factored_inner+native_bound_beta), r=(q-1)*counter_factored_inner',
        native_bound_map='beta_stage=beta_new+S-r; this identity uses the B=D^8 stage only',
        positive_zero_set_scope='Accepted-input equivalence to the original B=2D^8 source, not identical supplied zeros.')
    core.ps.checked_source(source,packet['parameters'],packet['auxiliaries']);core.closure(packet)
    return packet


@lru_cache(None)
def build(form='units',*,program_radix=False):
    assert type(program_radix) is bool
    return rewrite(parent.build(form,program_radix=program_radix))


def lift_bound(packet,values):
    env=execute(cone(packet,(INDEX,S)),values);result=dict(values)
    result[GAP]+=env[S]-env[INDEX]
    return result


def interpreter(E,x,limit=1000):
    assert type(E) is int and E>0 and type(x) is int and x>0
    table=core.TABLE;q=0;v=[0,E,x,0,0,0,0,0];configs=[(q,tuple(v))];chosen=[]
    for _ in range(limit):
        if q==len(table):break
        op,r,*targets=table[q];b=int(op!='I' and v[r]==0)
        chosen.append((q,b))
        if op=='I':v[r]+=1
        elif op=='D' and not b:v[r]-=1
        q=targets[b];configs.append((q,tuple(v)))
    return configs,chosen


def pack_history(packet,configs,chosen,E,x,C=None):
    assert packet.get('counter_minimal_time_radix') and packet['c']==1
    assert type(E) is int and E>0 and type(x) is int and x>0
    pr=packet['counter_program_radix']
    assert parent.radix.valid_recipe(E,C) if pr else C is None
    assert chosen and len(configs)==len(chosen)+1
    assert configs[0]==(0,(0,E,x,0,0,0,0,0)) and configs[-1][0]==len(core.TABLE)
    lookup={(q,b):i for i,(q,b) in enumerate((q,b) for q,row in enumerate(core.TABLE) for b in range(len(row)-2))}
    selected=[]
    for i,(q,b) in enumerate(chosen):
        assert configs[i][0]==q and q<len(core.TABLE)
        op,r,*targets=core.TABLE[q];v=list(configs[i][1]);assert b==int(op!='I' and v[r]==0)
        if op=='I':v[r]+=1
        elif op=='D' and not b:v[r]-=1
        assert configs[i+1]==(targets[b],tuple(v));selected.append(lookup[q,b])
    h=1;floor=x if pr else E+x
    while h<=max([floor]+[v+2 for _,rs in configs for v in rs]):h*=2
    D=(C if pr else 2)*h;radix=D**8;P=radix**len(chosen);J=(P-1)//(radix-1)
    pack=lambda seq:sum(v*radix**i for i,v in enumerate(seq))
    values={f'edge{i}_hat':1+pack([int(i==e) for e in selected]) for i in range(len(packet['edges']))}
    vectors=[]
    for (_,rs),i in zip(configs,selected):
        rs=list(rs);_,_,op,r=packet['edges'][i]
        if op in ('D','P'):rs[r]-=1
        assert min(rs)>=0 and max(rs)<=h-3
        vectors.append(sum(v*D**j for j,v in enumerate(rs)))
    W=pack(vectors);Y=sum(v*D**j for j,v in enumerate(configs[-1][1]));RM=(h-1)*sum(D**j for j in range(8))*J
    values.update(program=E,input=x,height_slack=h-floor,counter_word_hat=W+1,final_counter_hat=Y+1,
                  global_slack=RM-W-1-int(packet.get('counter_outer_units',False)))
    if pr:values['radix_program']=C
    assert min(values.values())>0
    return values


def outer_oracle(packet,values):
    E,x,eta=values['program'],values['input'],values['height_slack'];pr=packet['counter_program_radix']
    h=x+eta if pr else E+x+eta;D=(values['radix_program'] if pr else 2)*h;radix=D**8
    es=[values[f'edge{i}_hat']-1 for i in range(len(packet['edges']))];J=sum(es);P=(radix-1)*J+1
    W=values['counter_word_hat']-1;Y=values['final_counter_hat']-1
    action={op:sum(e*D**row[3] for e,row in zip(es,packet['edges']) if row[2]==op or row[2]=='P' and op in ('I','D')) for op in ('I','D','Z')}
    RM=(h-1)*sum(D**j for j in range(8))*J;ZM=(D-1)*action['Z'];K=len(es)
    ep=sum(e*P**i for i,e in enumerate(es));Z=ep+P**K*W;H=Z+P**(K+1)*W
    M=J*sum(P**i for i in range(K))+P**K*RM+P**(K+1)*ZM;Q=radix*P**64
    code=lambda q:0 if q==len(core.TABLE) else packet['codes'][q][1]*D**packet['codes'][q][0]
    current=sum(e*code(row[0]) for e,row in zip(es,packet['edges']));following=sum(e*code(row[1]) for e,row in zip(es,packet['edges']))
    residuals=[W+1+values['global_slack']-RM,radix*(W+action['I'])+E*D+x*D**2-W-action['D']-P*Y,radix*following+D-current]
    return dict(D=D,B=radix,J=J,P=P,W=W,Y=Y,rm=RM,zm=ZM,ah=H,am=M,az=Z,scale=Q),residuals


def outer_source(packet):
    return cone(packet,list(packet['interfaces'].values())+[v for pair in packet['outer_pairs'] for v in pair])


def audit(packet,seed,cases=32):
    rng=random.Random(seed);stage=packet['counter_native_bound_parent'];old=packet['counter_minimal_time_parent'];tally=Counter()
    for i in range(cases):
        signed=i>=cases//2;draw=lambda:rng.randrange(-3,4) if signed else rng.randrange(1,6)
        values={n:draw() for n in packet['parameters']+packet['auxiliaries']};lift=lift_bound(packet,values)
        e=execute(packet['source'],values);before=execute(stage['source'],lift)
        assert all(e[n]==before[n] for n,_,_,_ in packet['source'])
        assert e['native__wn2']==e['native__q']*(e[S]+values[GAP])
        # The old source becomes an oracle only after its time-radix definition is explicitly overridden.
        patched=[(n,'+',B,0) if n==OLD_B else row for row in old['source'] for n in [row[0]]]
        oracle=execute(patched,lift)
        assert all(e[n]==oracle[n] for n,_,_,_ in packet['source'])
        outer,res=outer_oracle(packet,values);at=lambda v:e[v] if isinstance(v,str) else v
        assert all(at(v)==outer[k] for k,v in packet['interfaces'].items())
        assert [at(a)-at(b) for a,b in packet['outer_pairs']]==res
        for sos in (False,True):
            ns,no=polynomial_source(packet,sum_of_squares=sos);bs,bo=polynomial_source(stage,sum_of_squares=sos)
            assert execute(ns,values)[no]==execute(bs,lift)[bo]
            tally['complete_stage_output_identities']+=1
        tally['complete_register_and_outer_maps']+=1;tally['signed_assignments']+=signed
        tally['positive_nonpositive_formal_stage_slacks']+=not signed and lift[GAP]<=0
    if packet['counter_program_radix']:
        fixed=dict(packet,parameters=[n for n in packet['parameters'] if n!='radix_program'],
            source=[(n,op,8 if a=='radix_program' else a,8 if b=='radix_program' else b) for n,op,a,b in packet['source']])
        assert degree_bound(fixed)==degree_bound(build(packet['form'],program_radix=False))
    return dict(tally)


def history_audit():
    histories=[];tally=Counter()
    for E in range(1,20):
     for x in range(1,5):
      configs,chosen=interpreter(E,x)
      if configs[-1][0]==len(core.TABLE) and len(chosen)<=350:histories.append((E,x,configs,chosen))
    for E,x,configs,chosen in histories:
      C=1<<max(2,E.bit_length())
      for pr,c in ((False,None),(True,C),(True,2*C)):
       for form in FORMS:
        packet=build(form,program_radix=pr);values=pack_history(packet,configs,chosen,E,x,c)
        env=execute(outer_source(packet),values);oracle,res=outer_oracle(packet,values)
        val=lambda n:env[n] if isinstance(n,str) else n
        assert res==[-int(packet.get('counter_outer_units',False)),0,0]
        assert [val(a)-val(b) for a,b in packet['outer_pairs']]==res
        assert all(val(n)==oracle[k] for k,n in packet['interfaces'].items())
        assert oracle['ah']&oracle['am']==oracle['az'] and oracle['scale']>oracle['ah']+oracle['am']-oracle['az']
        assert oracle['B']==oracle['D']**8
        bad=dict(values,final_counter_hat=values['final_counter_hat']+1)
        assert outer_oracle(packet,bad)[1][1]!=0
        tally['new_radix_outer_packs']+=1;tally['packed_chronological_rows']+=len(chosen)
      tally['halted_U21_histories']+=1
      for q,b in chosen:tally['branch_'+core.TABLE[q][0]+str(b)]+=1
    return dict(tally)


def margins():
    rng=random.Random(4051147);tally=Counter()
    for pr in (False,True):
     packet=build(program_radix=pr);os=outer_source(packet)
     for h in ((3,4,5,8) if not pr else (2,3,4,8)):
      for C in ((2,) if not pr else (4,16)):
       D=C*h;radix=D**8
       for E in ((1,h-2) if not pr else (1,C-1)):
        for sign in (-1,1):
         for endpoint in (False,True):
          es=[rng.randrange(4) for _ in packet['edges']];J=sum(es);RM=(h-1)*sum(D**r for r in range(8))*J
          W=RM-3 if endpoint else 0;gamma=RM-W-1-sign
          vals={f'edge{i}_hat':e+1 for i,e in enumerate(es)}
          vals.update(program=E,input=1,height_slack=h-(1 if pr else E+1),counter_word_hat=W+1,final_counter_hat=1,global_slack=gamma)
          if pr:vals['radix_program']=C
          assert min(vals.values())>0
          e=execute(os,vals);z,res=outer_oracle(packet,vals);at=lambda n:e[n] if isinstance(n,str) else n
          assert all(at(n)==z[k] for k,n in packet['interfaces'].items()) and res[0]==-sign
          assert (h-1)*sum(D**r for r in range(8))<radix-1 and (D-1)*D**7<radix-1
          assert 0<=W<RM<z['P'] and z['zm']<z['P']
          assert z['ah']>=z['az'] and z['am']>z['az'] and z['scale']>z['ah']+z['am']-z['az']
          assert E*D+D**2<radix and D-2>h
          # At odd untyped h the label margin need only follow after dyadic typing.
          if D&(D-1)==0:assert max(lam for _,lam in packet['codes'])<D-2
          q=16*z['scale'];A=16*z['ah']+12;M=16*z['am']+10;Z=16*z['az']+8
          S0=A+1+(q+1)*(M+(q-1)*Z);r=(q-1)*S0
          assert q*(S0+1)>r and min(q-A-M+Z-1,A-Z,M-Z,Z)>0
          tally['weak_range_corners']+=1;tally['height_two_corners']+=h==2;tally['negative_range_corners']+=sign<0
    return dict(tally)


def guards():
    old=parent.build();bad=[dict(old,c=1),dict(old,interfaces={'B':'wrong'}),dict(old,source=old['source'][:-1]),
        dict(old,table=core.TABLE[:-1]),dict(old,form='raw'),build()]
    for p in bad:
        try:rewrite(p)
        except (AssertionError,KeyError,TypeError):pass
        else:raise AssertionError('unsupported caller accepted')
    return len(bad)


def verify():
    records=[];total=Counter()
    for pr in (False,True):
     for form in FORMS:
      packet=build(form,program_radix=pr);source,out=polynomial_source(packet);core.closure(packet)
      checks=audit(packet,405000+len(records));total.update(checks)
      records.append(dict(program_radix=pr,form=form,ledger=ledger(packet),audit=checks,source=source,output=out,
         parameters=packet['parameters'],auxiliaries=packet['auxiliaries'],source_sha256=hashlib.sha256(json.dumps(source,separators=(',',':')).encode()).hexdigest()))
    assert ledger(build())['product']['operations']==405
    assert ledger(build(program_radix=True))['product']['operations']==404
    return dict(status='PASS_KOREC_PACKED_MINIMAL_RADIX405',records=records,audit_totals=dict(total),
        histories=history_audit(),margins=margins(),rejected_callers=guards(),
        scope='Canonical U21 only, one-program405 or fixed-dyadic-program-radix404. B=D^8 has a direct chronology proof and fresh native extensions. Triangular source identity is only to the new-B intermediate.')


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--write',action='store_true');args=parser.parse_args()
    result=json.loads(json.dumps(verify()));path=Path(__file__).with_suffix('.json')
    if args.write:path.write_text(json.dumps(result,indent=2)+'\n')
    else:assert json.loads(path.read_text())==result,'receipt mismatch'
    print(result['status']);print(result['audit_totals']);print(result['histories']);print(result['margins'])
