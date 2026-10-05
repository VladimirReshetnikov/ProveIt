#!/usr/bin/env python3
"""Fresh static current-U9 selector emitter; no source-array execution.

Parent and child arrays are inert data: only literal replacement, stable
ordering, topology/consumer/liveness/ledger checks occur. Handwritten scalar
lemmas below never interpret an array. No repository program is imported.
"""
import argparse
import hashlib
import itertools
import json
from pathlib import Path

ROOT=Path('/home/codex/.codex/worktrees/2a71/Proofs')
WIP=Path('Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue')
PINS={
 'neary_woods_universal_tail_quotient253.json':'48d604caf52af6cc6e37f77614787b1a02a549b03c1f5acdb53a5a7277c7504f',
 'neary_woods_universal_tail_quotient253.md':'328b9a3d62a989f78cd3c7b388eba01800a9d92e7cb8df6ac58184df9982653b',
 'neary_woods_universal_product_scale253.md':'9b3b0566dd1365d9acf4b97b6b290b951d56eb51392e85e48f06f83b1604434f',
 'neary_woods_universal_initial_bound254.md':'9e1a0fd5559dc72420a5123eb4f67753576f7b06d93aff6b7b650cd40dba1f90',
 'neary_woods_universal_history_units260.md':'73d3787dcc10acc037f80699ec3f8bde1fb721613abac5ce489762aab339057c',
 'neary_woods_universal_u9_tag_chain.md':'7159fbae99ca020c2f9a10eb8560c13f56e53b6f81cd2f17f045097480f8ff03',
 'pcp_affine_slope_class_history.md':'33250339420da4a3e27b5e2e584f93dcb88ca5f62a630a195bad95d43cd579f8',
 'binary_tag_four_tile_history.md':'2cb8d1736852d525d4668f40eacdc8fa090c426f100110421521c85910e1e4b2',
 'neary_woods_universal_offset258.md':'84b3f17c3a0162bb6a0c7edcb5c5dd4e3cfe1451fcb9e498805ee7e9acaf5fc0',
 'residue_affine_binary_lane128_tesla.md':'b5d93830a38426f5ac4129d04888efa94b0086932277b969dd810bff0ad1120c',
}
DELETE=[
 ['hist__pack_product__44','*','hist__P__10','hist__Shat3'],
 ['hist__pack_sum__45','+','hist__Shat2','hist__pack_product__44'],
 ['hist__repunit_product__53','+','hist__P3__78','hist__repunit_tail__64'],
 ['shared_history_selector_high','*','hist__P2__51','hist__pack_sum__45'],
 ['hist__pack_sum__49','+','hist__pack_sum__61','shared_history_selector_high'],
 ['hist__unhat_pack__54','-','hist__pack_sum__49','hist__repunit_product__53'],
 ['hist__controller_mask__55','*','hist__J__7','hist__repunit_product__53'],
 ['hist__P7__81','*','hist__P6__80','hist__P__10'],
]
NEW=[
 ['tree_group12','-','hist__group_sum__58',2],
 ['tree_mask_product','*','hist__P_product__9','tree_group12'],
 ['tree_mask_sum','+','hist__J__7','tree_mask_product'],
 ['tree_mask_shift','*','hist__P__10','tree_mask_sum'],
 ['hist__controller_mask__55','+','hist__J__7','tree_mask_shift'],
]
EDIT={
 'hist__range_region__82':['hist__range_region__82','*','hist__P6__80','hist__range_histories__57'],
 'hist__P9__86':['tree_P8','*','hist__P6__80','hist__P2__51'],
 'hist__top_history__87':['hist__top_history__87','*','hist__B__3','tree_P8'],
 'hist__range_mask_region__91':['hist__range_mask_region__91','*','hist__P6__80','hist__range_mask__77'],
 'hist__top_mask__92':['hist__top_mask__92','*',2,'tree_P8'],
 'hist__controller_region__79':['hist__controller_region__79','*','hist__P3__78','hist__unhat_pack__65'],
 'hist__joined_M__95':['hist__joined_M__95','+','hist__joined_M__94','tree_P8'],
}

def need(value,message):
    if not value: raise RuntimeError(message)

def sha(data): return hashlib.sha256(data).hexdigest()

def canonical(data): return json.dumps(data,sort_keys=True,separators=(',',':')).encode()

def structural(rows,packet):
    free=set(packet['parameters']+packet['auxiliaries'])
    known=set(free); prod={}; roles=set()
    for r in rows:
        need(len(r)==4 and r[1] in ['+','-','*'] and r[0] not in known,'row/op/unique')
        for t in r[2:]:
            if isinstance(t,str): need(t in known,'topology '+t)
            elif type(t) is int: pass
            else:
                need(isinstance(t,dict) and set(t)=={'fixed_numeral'},'literal format')
                need(t['fixed_numeral'] in packet['fixed_numeral_recipes'],'fixed recipe')
                roles.add(t['fixed_numeral'])
        prod[r[0]]=r;known.add(r[0])
    live=set();pending=[packet['output']]
    while pending:
        x=pending.pop()
        if x in live:continue
        live.add(x)
        if x in prod:pending.extend(t for t in prod[x][2:] if isinstance(t,str))
    need(set(prod)<=live and free<=live,'liveness')
    need(len(roles)==11,'all fixed roles')
    M=sum(r[1]=='*' for r in rows)
    return {'operations':len(rows),'M':M,'A':len(rows)-M,'all_gates_live':True,
            'all_supplied_ports_live':True,'fixed_numeral_roles':len(roles),
            'witnesses':len(packet['auxiliaries']),'supplied_parameters':len(packet['parameters']),
            'canonical_source_sha256':sha(canonical(rows))}

def emit(packet):
    parent=packet['source'];old={r[0]:r for r in parent}
    need(len(parent)==253 and len(old)==253,'parent size')
    for r in DELETE:need(old.get(r[0])==r,'deleted literal')
    # Complete parent bytes are pinned. These are additional interface guards.
    need(old['hist__P__10']==['hist__P__10','+','hist__global_bound','hist__global_sum__14'],'positive P')
    need(old['hist__P_product__9']==['hist__P_product__9','*','hist__Bm1__8','hist__J__7'],'signed repunit cut')
    need(old['and__bs_X_bound']==['and__bs_X_bound','+','factored_pack_Z','and__bound_beta'],'tail bound')
    gone={r[0] for r in DELETE}; rows=[]
    for r in parent:
        if r[0] in gone:continue
        if r[0]=='hist__controller_region__79':rows.extend(NEW)
        rows.append(list(EDIT.get(r[0],r)))
    ledger=structural(rows,packet)
    need(ledger['operations']==250 and ledger['M']==130 and ledger['A']==120,'250 ledger')
    child={r[0]:r for r in rows}
    untouched=[r for r in parent if r[0] not in gone and r[0] not in EDIT]
    need(all(child[r[0]]==r for r in untouched),'retained literal rows')
    need(all(child[n]==old[n] for n in packet['unit_factors']),'factor definitions')
    # No new dependency is introduced into loader, geometry, or native equations.
    changed={r[0] for r in NEW}|{r[0] for r in EDIT.values()}
    need(all(n.startswith('hist__') or n.startswith('tree_') for n in changed),'changed namespace')
    need(rows[-18:]==parent[-18:],'complete finalizer/factor tail retained')
    private=[v for v in packet['auxiliaries'] if v.startswith('and__')]
    need(len(private)==12,'private joint witness count')
    for r in rows:
        if any(isinstance(t,str) and t in private for t in r[2:]):
            need(r[0].startswith('and__'),'private witness leak')
    return {'source':rows,'output':packet['output'],'ledger':ledger,
      'certificate':{'operations':249,'M':130,'A':119,'comparisons':1,'witnesses':43},
      'parameters':packet['parameters'],'auxiliaries':packet['auxiliaries'],
      'rebuilt_joint_witnesses':private,'preserved_witnesses':[v for v in packet['auxiliaries'] if v not in private],
      'domains':packet['domains'],'comparisons':packet['comparisons'],
      'unit_factors':packet['unit_factors'],'merged':packet['merged'],
      'fixed_numeral_recipes':packet['fixed_numeral_recipes'],'fixed_u9_recipe':packet['fixed_u9_recipe'],
      'delta':{'deleted':DELETE,'added':NEW,'edited':[{'before':old[n],'after':r} for n,r in EDIT.items()],
               'literal_retained_rows':len(untouched),'native_and_loader_rows_literal':True},
      'manual_degree':{'joint_factors':{'and__R15':129,'and__P17':322,'and__first_unit':73,
                  'and__f_square_minus_one':178,'and__index_unit':57,'and__linear_unit':57},
                  'unchanged_factor_sum':110,'total_upper_bound':926,'exact_degree_claimed':False,
                  'scope':'Hand-derived cut/factor ledger; no array propagation.'}}

def compositions(n,k):
    if k==1:yield (n,);return
    for x in range(n+1):
        for tail in compositions(n-x,k-1):yield (x,)+tail

def tree_checks():
    total=accepted=0
    for J in range(25):
        for s in compositions(J,4):
            a=s[1]+s[2];b=s[0]+s[3]
            tree=(a&J)==a and (s[0]&b)==s[0] and (s[1]&a)==s[1]
            flat=all((v&J)==v for v in s) and all((s[i]&s[j])==0 for i in range(4) for j in range(i))
            need(tree==flat,'hierarchical partition')
            total+=1;accepted+=tree
    need((1&5)==1 and (3&5)!=3,'unstructured deletion boundary')
    return {'J_inclusive':[0,24],'nonnegative_compositions':total,'partitions':accepted}

def pretyping_checks():
    total=minus=height1=0
    for mult in [32,64]:
      for height in range(1,5):
       b=mult*height
       for J in range(1,7):
        for eps in [-1,1]:
         P=(b-1)*J+eps
         R=(height-1)*J
         for selectors in compositions(J,4):
          a=selectors[1]+selectors[2];g03=selectors[0]+selectors[3]
          S=a+P*selectors[0]+P*P*selectors[1]
          MC=J+P*(J+(b-1)*J*a)
          need(MC==J+P*(g03+(1-eps)*a)+P*P*a,'signed mask identity')
          need(MC+2<P**3 and S<P**3,'controller margins')
          Mb=(b-1)*S
          need(Mb<2*P**3,'physical mask margin')
          for large in range(6):
           v=[1]*6;v[large]+=P-6
           HU,HV,zu,zv0,zv1,beta=v
           Hb=HU+P*HV+P*P*HV
           Zb=(zu-1)+P*(zv0-1)+P*P*(zv1-1)
           Hr=HU+P*HV;Mr=R*(1+P)
           T=P**8
           H0=Hb+P**3*S+P**6*Hr
           M0=Mb+P**3*MC+P**6*Mr
           Z=Zb+P**3*S+P**6*Hr
           H=H0+2*T;M=M0+T;Q=b*T
           need(0<=H0<T and 0<=M0<T and 0<=Z<T,'lower block margins')
           need(H-Z>=T+1 and M-Z>=1 and Q-H-M+Z>=(b-5)*T+2,'truth field margins')
           total+=1;minus+=eps==-1;height1+=height==1
    return {'cases':total,'negative_repunit_cases':minus,'height_one_cases':height1,
            'scope':'Fresh scalar extrema satisfying only signed repunit/global sum; not native zeros.'}

def typed_checks():
    total=0
    # Handwritten genuine affine paths on a small illustrative tag table;
    # not the enormous U9 coefficient recipe and not full Pell witnesses.
    table=[(2,1,32,18),(16,9,8,6),(16,9,2,0),(2,1,2,0)]
    for length in range(1,5):
      for word in itertools.product(range(4),repeat=length):
       us=[1];vs=[3]
       for idx in word:
        a,c,b,d=table[idx];us.append(a*us[-1]+c);vs.append(b*vs[-1]+d)
       D=1
       while D<=max(us[-1],vs[-1]):D*=2
       radix=64*D;P=radix**length;J=(P-1)//(radix-1)
       sel=[sum((i==idx)*radix**j for j,idx in enumerate(word)) for i in range(4)]
       HU=sum(us[j]*radix**j for j in range(length));HV=sum(vs[j]*radix**j for j in range(length))
       zu=sum((word[j] in [1,2])*us[j]*radix**j for j in range(length))
       zv0=sum((word[j]==0)*vs[j]*radix**j for j in range(length))
       zv1=sum((word[j]==1)*vs[j]*radix**j for j in range(length))
       beta=P-HU-HV-zu-zv0-zv1-3
       need(beta>0,'genuine global slack')
       G=sel[1]+sel[2];S=G+P*sel[0]+P*P*sel[1]
       Mc=J+P*(J+(radix-1)*J*G)
       need(Mc==J+P*(sel[0]+sel[3])+P*P*G,'typed mask')
       hb=HU+P*HV+P*P*HV;mb=(radix-1)*S;zb=zu+P*zv0+P*P*zv1
       hr=HU+P*HV;mr=(D-1)*J*(P+1);T=P**8
       hn=hb+P**3*S+P**6*hr+2*T;mn=mb+P**3*Mc+P**6*mr+T;zn=zb+P**3*S+P**6*hr
       cold=sum(sel[j]*P**j for j in range(4));mold=J*sum(P**j for j in range(4));told=P**9
       ho=hb+P**3*cold+P**7*hr+2*told;mo=mb+P**3*mold+P**7*mr+told;zo=zb+P**3*cold+P**7*hr
       need((hn&mn)==zn and (ho&mo)==zo,'old and new high AND')
       nu=2*HU+14*zu+J+8*G
       nv=2*HV+30*zv0+18*sel[0]+6*zv1+6*sel[1]
       need(radix*nu+1==HU+P*us[-1] and radix*nv+3==HV+P*vs[-1],'chronology')
       total+=1
    return {'genuine_affine_histories':total,'maximum_length':4,'illustrative_table':table,
            'scope':'Scalar outer identities only; no saved source-array values or U9/Pell tuples.'}

def build():
    deps=[]
    for name,pin in PINS.items():
        data=(ROOT/WIP/name).read_bytes();need(sha(data)==pin,'dependency '+name)
        deps.append({'path':str(WIP/name),'sha256':pin,'bytes':len(data),'lines':len(data.splitlines())})
    parent=json.loads((ROOT/WIP/'neary_woods_universal_tail_quotient253.json').read_text())
    forms=[]
    for f in parent['forms']:
        p=f['packet'];need(structural(p['source'],p)['operations']==253,'parent topology')
        forms.append(emit(p))
    need([f['merged'] for f in forms]==[False,True],'both interfaces')
    return {'status':'PASS','author_helper_sha256':sha(Path(__file__).read_bytes()),'dependencies':deps,
       'scope':'Only static source metadata and fresh handwritten scalar diagnostics; no array evaluation.',
       'forms':forms,'tree_checks':tree_checks(),'pretyping_checks':pretyping_checks(),
       'typed_checks':typed_checks(),
       'numbered_boundary':{'J':1,'b':32,'P':30,'epsilon':-1,'G12':1,
                           'emitted_mask':961,'typed_mask':901,'difference':60}}

def main():
    p=argparse.ArgumentParser();p.add_argument('--write',action='store_true');a=p.parse_args()
    target=Path(__file__).with_suffix('.json')
    encoded=json.dumps(build(),sort_keys=True,indent=2)+'\n'
    if a.write:target.write_text(encoded)
    else:need(target.read_text()==encoded,'receipt difference')
    print('PASS: two complete static 250-row sources; 130M+120A,43 witnesses; no array evaluation')

if __name__=='__main__':main()
