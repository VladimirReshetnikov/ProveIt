#!/usr/bin/env python3
"""Fresh static scaled-strong transfer plus handwritten polynomial cuts.
No saved source array is evaluated, imported, or symbolically propagated.
"""
import argparse
import hashlib
import json
from pathlib import Path

ROOT=Path('/home/codex/.codex/worktrees/2a71/Proofs')
WIP=Path('Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue')
PINS={
 'neary_woods_hierarchical_history250_tesla.json':'d2f1ae7870cb8ec295d4401a8e9c951047f0e92cf2b6e6f4bb723c6b483f1ebf',
 'neary_woods_hierarchical_history250_tesla.md':'1bb41ed9eae9e77b2a9236c49508a55538f2ff84d1cd245f3bccec4dee39a330',
 'complete84_scaled_strong_output.md':'01eb7df6688c08c6788a3c7a1cc272ca5ffc1a87734fd622dbec8a64ae974ade',
}

def need(value,message):
    if not value:raise RuntimeError(message)

def sha(data):return hashlib.sha256(data).hexdigest()

def canonical(data):return json.dumps(data,sort_keys=True,separators=(',',':')).encode()

def names(row):return [x for x in row[2:] if isinstance(x,str)]

def structural(rows,p):
    free=set(p['parameters']+p['auxiliaries']);known=set(free);prod={};roles=set()
    for r in rows:
        need(len(r)==4 and r[1] in ['+','-','*'] and r[0] not in known,'literal row')
        for t in r[2:]:
            if isinstance(t,str):need(t in known,'topology')
            elif type(t) is int:pass
            else:
                need(isinstance(t,dict) and set(t)=={'fixed_numeral'},'numeral format')
                roles.add(t['fixed_numeral'])
        prod[r[0]]=r;known.add(r[0])
    live=set();pending=[p['output']]
    while pending:
        n=pending.pop()
        if n in live:continue
        live.add(n)
        if n in prod:pending.extend(names(prod[n]))
    need(set(prod)<=live and free<=live,'full liveness')
    need(roles==set(p['fixed_numeral_recipes']),'fixed numeral roles')
    M=sum(r[1]=='*' for r in rows)
    return {'operations':len(rows),'M':M,'A':len(rows)-M,'witnesses':len(p['auxiliaries']),
            'supplied_parameters':len(p['parameters']),'all_rows_and_ports_live':True,
            'fixed_numeral_roles':len(roles),'canonical_source_sha256':sha(canonical(rows))}

def stable_sort(rows,free):
    remaining=list(rows);out=[];known=set(free)
    while remaining:
        for j,r in enumerate(remaining):
            if all(n in known for n in names(r)):
                out.append(r);known.add(r[0]);remaining.pop(j);break
        else:raise RuntimeError('cycle or missing port')
    return out

def rewrite(parent,cores):
    old=parent['source'];by={r[0]:r for r in old};delete=set();replacements={};new=[];guards=[]
    for prefix in cores:
        expected=[
          [prefix+'c2','*',prefix+'R10a',prefix+'R10a'],
          [prefix+'Ac2','*',prefix+'A',prefix+'c2'],
          [prefix+'L16','*',prefix+'f',prefix+'f'],
          [prefix+'ic2','*',prefix+'i',prefix+'c2'],
          [prefix+'ic22','*',prefix+'ic2',prefix+'ic2'],
          [prefix+'normalized_strong_Q','*',prefix+'A',prefix+'ic22'],
          [prefix+'f_square_minus_one','-',prefix+'L16',prefix+'normalized_strong_Q'],
          [prefix+'R16','*',prefix+'A',prefix+'normalized_strong_Q'],
        ]
        for r in expected:need(by.get(r[0])==r,'paid coefficient binding')
        consumer_expected={
          prefix+'ic2':[prefix+'ic22'],
          prefix+'ic22':[prefix+'normalized_strong_Q'],
          prefix+'normalized_strong_Q':[prefix+'f_square_minus_one',prefix+'R16'],
          prefix+'f_square_minus_one':['partition_product_0_6' if prefix=='geo__' else 'partition_product_0_7'],
        }
        for name,wanted in consumer_expected.items():
            need([r[0] for r in old if name in names(r)]==wanted,'private consumer guard')
        delete.update(prefix+n for n in ['ic2','ic22','normalized_strong_Q'])
        new.extend([[prefix+'scaled_aux_root','*',prefix+'i',prefix+'Ac2'],
                    [prefix+'scaled_f_square','*',prefix+'A',prefix+'L16']])
        replacements[prefix+'R16']=[prefix+'R16','*',prefix+'scaled_aux_root',prefix+'scaled_aux_root']
        replacements[prefix+'f_square_minus_one']=[prefix+'f_square_minus_one','-',prefix+'scaled_f_square',prefix+'R16']
        guards.append({'core':prefix,'paid_rows':expected,'consumer_sets':consumer_expected})
    output=parent['output'];need(by[output]==[output,'-','lower_history_product',1],'complete output binding')
    if len(cores)==1:multiplier=cores[0]+'A'
    else:
        multiplier='scaled_discriminant_product'
        new.append([multiplier,'*','geo__A','and__A'])
    replacements[output]=[output,'-','lower_history_product',multiplier]
    rows=[list(replacements.get(r[0],r)) for r in old if r[0] not in delete]+new
    rows=stable_sort(rows,parent['parameters']+parent['auxiliaries'])
    ledger=structural(rows,parent)
    need(ledger['operations']==249 and ledger['M']==129 and ledger['A']==120,'249 ledger')
    unchanged=[r for r in old if r[0] not in delete and r[0] not in replacements]
    child={r[0]:r for r in rows}
    need(all(child[r[0]]==r for r in unchanged),'retained producer rows')
    degree_add=sum(8 if c=='geo__' else 112 for c in cores)
    return {'source':rows,'output':output,'ledger':ledger,'cores_scaled':cores,'multiplier_port':multiplier,
       'parameters':parent['parameters'],'auxiliaries':parent['auxiliaries'],'domains':parent['domains'],
       'fixed_numeral_recipes':parent['fixed_numeral_recipes'],'fixed_u9_recipe':parent['fixed_u9_recipe'],
       'merged':parent['merged'],'comparisons':[['lower_history_product',multiplier]],
       'certificate':{'operations':248,'M':129,'A':119,'comparisons':1,'witnesses':43},
       'parent_factors_historical':parent['unit_factors'],
       'active_factor_note':'Scaled strong factors equal their discriminants at positive zeros; not all factors are units.',
       'manual_degree_upper_bound':926+degree_add,'exact_degree_claimed':False,
       'delta':{'removed':[by[n] for n in sorted(delete)],'new_rows':new,
                'edits':[{'before':by[n],'after':r} for n,r in replacements.items()],
                'literal_retained_rows':len(unchanged),'stable_topological_sort':True,'guards':guards}}

# Original sparse polynomial arithmetic on independently chosen cut variables.
# It never receives rows or variable names from a saved source.
N=8
ONE={(0,)*N:1}

def atom(k):
    e=[0]*N;e[k]=1;return {tuple(e):1}

def add(a,b,sign=1):
    r=dict(a)
    for m,c in b.items():r[m]=r.get(m,0)+sign*c
    return {m:c for m,c in r.items() if c}

def mul(a,b):
    r={}
    for m,c in a.items():
        for n,d in b.items():
            e=tuple(x+y for x,y in zip(m,n));r[e]=r.get(e,0)+c*d
    return {m:c for m,c in r.items() if c}

def square(a):return mul(a,a)

def cuts():
    D,i,c,f,V,y,U,E=[atom(k) for k in range(N)]
    c2=square(c);old_t=mul(i,c2);old_Q=mul(D,square(old_t));old_K=mul(D,old_Q)
    new_t=mul(i,mul(D,c2));new_K=square(new_t)
    old_N=add(square(f),old_Q,-1);new_N=add(mul(D,square(f)),new_K,-1)
    old_A=add(mul(old_K,add(square(V),square(y),-1)),square(y))
    new_A=add(mul(new_K,add(square(V),square(y),-1)),square(y))
    need(old_K==new_K,'auxiliary coefficient identity')
    need(new_N==mul(D,old_N),'strong scaling identity')
    need(old_A==new_A,'complete auxiliary norm identity')
    old_F=add(mul(mul(U,old_N),old_A),ONE,-1)
    new_F=add(mul(mul(U,new_N),new_A),D,-1)
    need(new_F==mul(D,old_F),'whole one-core cut identity')
    # Independent whole factor ports for the two-core identity.
    Dg,Dj,Sg,Sj,rest=[atom(k) for k in range(5)]
    base=add(mul(mul(rest,Sg),Sj),ONE,-1)
    dg_dj=mul(Dg,Dj)
    both=add(mul(mul(rest,mul(Dg,Sg)),mul(Dj,Sj)),dg_dj,-1)
    need(both==mul(dg_dj,base),'two-core finalizer identity')
    return {'coefficient_identity_terms':len(old_K),'scaled_strong_terms':len(new_N),
            'auxiliary_terms':len(old_A),'one_core_finalizer_terms':len(new_F),
            'two_core_factor_finalizer_terms':len(both),'all_ring_identities':5,
            'scope':'Handwritten sparse cut formulas, not a source-array execution or propagation.'}

def positive_prefix():
    cases=zero_selectors=0
    for seed in range(1,65):
        # Include numeral1 and height1; no native equation or valid-program assertion.
        x=seed%4+1;E=seed%3+1;gap=seed%5+1;slack=seed%7+1
        z=seed%6+1;pgap=seed%8+1;divisor=seed%5+1;recoder=seed%3+1
        duration=E+gap;ib=x+duration+slack;loadr=ib+z+pgap
        modulus=divisor*loadr;Q=modulus+1;B=recoder*Q
        dj=(B-1)*(seed%4+1)+duration;Pr=(B-1)*dj+1
        q0=16*B*(ib*Pr)
        h=seed%4+1;ch=1 if seed%2 else 32;b=ch*h
        HU=seed%3+1;HV=seed%5+1
        zh=[seed%2+1,seed%3+1,seed%4+1]
        P=HU+HV+sum(zh)+(seed%6+1)
        s=[0,0,0,0] if seed%2 else [1,2,0,1]
        ct=(s[1]+s[2])+P*s[0]+P*P*s[1]
        hb=HU+P*HV
        Z=(zh[0]-1)+P*(zh[1]-1)+P*P*(zh[2]-1)+P**3*ct+P**6*hb
        lowF=16*B*(modulus*((seed%3+1)-1)+z)+8
        F3=lowF+q0*Z;q=q0*b*P**8
        X=q*((q-1)*F3+(seed%4+1));Y=(2*(seed%5+1)+1)*q
        a=Y*(X+1);delta=a*a+4*a+3
        Xg=Q*(divisor*dj+(seed%4+1));Yg=(2*(seed%5+1)+1)*Q
        ag=Yg*(Xg+1);dg=ag*ag+4*ag+3
        need(q>=16 and F3>0 and X>0 and Y>0 and delta>0,'joint unconditional positive prefix')
        need(Xg>0 and Yg>0 and dg>0,'geometry unconditional positive prefix')
        cases+=1;zero_selectors+=not any(s)
    return {'cases':cases,'all_zero_selector_cases':zero_selectors,
            'scope':'Independent positive prefix formulas only; no equations imposed and no source arrays evaluated.'}

def build():
    deps=[]
    for name,pin in PINS.items():
        data=(ROOT/WIP/name).read_bytes();need(sha(data)==pin,'dependency '+name)
        deps.append({'path':str(WIP/name),'sha256':pin,'bytes':len(data),'lines':len(data.splitlines())})
    parent=json.loads((ROOT/WIP/'neary_woods_hierarchical_history250_tesla.json').read_text())
    forms=[]
    for p in parent['forms']:
        need(structural(p['source'],p)['operations']==250,'parent ledger')
        for cores in [['geo__'],['and__'],['geo__','and__']]:forms.append(rewrite(p,cores))
    return {'status':'PASS','author_helper_sha256':sha(Path(__file__).read_bytes()),'dependencies':deps,
            'forms':forms,'cut_checks':cuts(),'positive_prefix_checks':positive_prefix(),
            'scope':'Static source editing only. No parent/child array values, imports, or predecessor replay.',
            'zero_discriminant_boundary':{'kind':'independent factor ports only','Delta':0,'other_product':0,
                                         'strong':1,'old_output':-1,'scaled_output':0}}

def main():
    p=argparse.ArgumentParser();p.add_argument('--write',action='store_true');a=p.parse_args()
    target=Path(__file__).with_suffix('.json');text=json.dumps(build(),sort_keys=True,indent=2)+'\n'
    if a.write:target.write_text(text)
    else:need(target.read_text()==text,'receipt differs')
    print('PASS: six static249-row sources /1494 rows; five handwritten identities; no array evaluation')

if __name__=='__main__':main()
