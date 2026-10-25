#!/usr/bin/env python3
"""Replace eleven exact binomial numerators by one common modular root.

The mutation certificate records literal source changes.  Semantic equivalence
is a theorem in MODULAR_PROOF.md, not an outcome of the finite algebra audit.
"""
from pathlib import Path
import argparse, copy, hashlib, json, sys

HERE=Path(__file__).resolve().parent
ROOT=HERE.parent
PARENT=ROOT/'upstream/factorial_free/direct'
SOURCE=ROOT/'stages/fixed_base/raw_source.json'
MODULAR_CALLS=(3,5,7,8,9,10,12,13,15,16,17)
PAIRS={3:'index2',5:'index3',7:'index5',8:'index6',9:'index7',10:'index8',12:'index10',13:'index11',15:'index13',16:'index14',17:'index15'}

def build(source, out, parent=PARENT, support=16):
    sys.path.insert(0,str(parent/'parent/code'))
    import terminal_elimination as E
    import factor_horn as F
    import translate_coordinates as T
    old=json.loads(source.read_text()); new=copy.deepcopy(old)
    names={v['name']:i for i,v in enumerate(old['variables'])}
    V=F.V; C=lambda n:{():n} if n else {}; add=F.add
    scale=lambda p,c:{m:c*a for m,a in p.items() if c*a}
    mul=E.multiply; sq=lambda p:mul(p,p)
    def fresh(name, kind='witness'):
        i=len(new['variables']);new['variables'].append({'kind':kind,'name':name});return i
    L=fresh('frame.L'); u=fresh('free_A.u'); v=fresh('free_A.v'); w=fresh('free_A.w')
    H=fresh('self_radix.H','gate'); bhalf=fresh('choose0.odd_half'); common=fresh('modular_root.quotient')
    A=names['shared.A']; W=names['shared.W']; q=names['pow2.output']; B=names['choose0.output']; R=names['radius.R']; BH=names['self_radix.BH']
    t=add(V(names['t0']),C(16)); reps=[add(V(i),C(1)) for i in range(16,25)]
    Hpoly=add(C(2),scale(add(V(R),t),2),*[sq(a) for a in reps])
    edits=[]; rows=[]
    for ri,row in enumerate(old['residuals']):
        p=E.normalize(row['terms']);label=row['label']
        if label=='shared.last_norm':
            if p.get((A,A))!=1:raise ValueError('frame has changed')
            p=add(p,scale(sq(V(A)),-1),sq(V(L)))
        elif label=='self_radix.base_definition':
            p=add(V(BH),scale(mul(V(B),V(H)),-1))
        elif label=='shared.frame_definition':
            for call in MODULAR_CALLS:
                oid=names[f'pow{call}.output']
                if p.get((oid,oid))!=-1:raise ValueError(('missing frame square',call))
                p=add(p,sq(V(oid)))
        elif label=='pow6.power_congruence':
            p=add(V(names['pow6.output']),scale(mul(V(q),V(names['pow4.output'])),-1))
            label='radix.successor_power'
        elif label.startswith('pow') and label.endswith('.power_congruence'):
            call=int(label[3:label.index('.')])
            if call in MODULAR_CALLS:
                pair=PAIRS[call];XX=names[pair+'.X'];YY=names[pair+'.Y']
                p=add(V(XX),mul(add(V(q),C(1),scale(V(A),-1)),V(YY)),scale(V(names[f'pow{call}.output']),-1))
                label=f'modular_numerator{call}.definition'
        if E.degree(p)>2:raise ValueError(('raised degree',ri,label))
        rr={'label':label,'terms':E.as_terms(p)}; rows.append(rr)
        if rr!=row:edits.append({'original_row':ri,'old':row,'new':rr})
    # The existing gate is exactly N*M, shared by every range remainder.
    N=names['pow1.output']; M=names['pow14.output']
    candidates=[]
    for rr in old['residuals']:
        p=E.normalize(rr['terms'])
        if len(p)==2 and p.get(tuple(sorted((N,M))))==-1:
            candidates.extend(m[0] for m,c in p.items() if len(m)==1 and c==1)
    if len(candidates)!=1:raise ValueError(('ambiguous common modulus',candidates))
    NM=candidates[0]
    added=[
      {'label':'free_A.cofinal_constructor','terms':E.as_terms(add(V(A),scale(sq(V(L)),-1),scale(sq(V(u)),-1),scale(sq(V(v)),-1),scale(sq(V(w)),-1),scale(V(w),-1)))},
      {'label':'self_radix.signed_majorant','terms':E.as_terms(add(V(H),scale(Hpoly,-1)))},
      {'label':'choose0.odd_constructor','terms':E.as_terms(add(V(B),scale(V(bhalf),-2),C(-1)))},
      {'label':'modular_root.common_congruence','terms':E.as_terms(add(V(names['base3.T']),scale(mul(V(NM),V(common)),-1)))},
    ]
    rows.extend(added);new['residuals']=rows
    new['variant']='fixed_base16_common_modular_binomial_numerators'
    new.pop('metrics',None)
    mutation={'schema':'common_modular_numerators_v1','source_sha256':hashlib.sha256(E.canonical_bytes(old)).hexdigest(),
      'source_variant':old.get('variant'),'edits':edits,'added_rows':added,'removed_rows':[],
      'added_variables':[{'id':i,**new['variables'][i]} for i in range(len(old['variables']),len(new['variables']))],
      'modular_calls':list(MODULAR_CALLS),'remaining_exact_calls':[0,1,2,4,11,14],
      'successor_call':6,'interface':{'L':L,'A':A,'W':W,'H':H,'B':B,'R':R,'q':q,'N':N,'M':M,'NM':NM,'T':names['base3.T'],'common_quotient':common,
      'A_slack':[u,v,w],'B_odd_half':bhalf,'H_polynomial':E.as_terms(Hpoly),'pairs':PAIRS},
      'semantic_claim':'Eleven exact (q+1)^e requests replaced by signed Pell evaluations modulo N*q^x; frame moved to L and A has cofinal ternary slack.'}
    out.mkdir(parents=True,exist_ok=True)
    for name,obj in [('raw_source.json',new),('mutation.json',mutation)]: (out/name).write_bytes(E.canonical_bytes(obj))
    fac,fc=F.transform(new); pr,pc,pm=E.optimize(fac,max_support=support); check=E.verify(fac,pr,pc)
    op=json.loads((parent/'parent/data/projected.json').read_text());ot=json.loads((parent/'parent/equation/translation_certificate.json').read_text())
    byname={op['variables'][i]['name']:s for i,s in ot['shifts']}
    shifts={i:byname[vv['name']] for i,vv in enumerate(pr['variables']) if vv['name'] in byname}
    eq=T.translate(pr,shifts);poly=E.expand(eq)
    metrics={'variables':len(eq['variables']),'rows':len(eq['residuals']),'degree':max(len(m) for _,m in poly['terms']),
      'monomials':len(poly['terms']),'height':max(abs(c) for c,_ in poly['terms']),
      'row_height':max(abs(c) for rr in eq['residuals'] for c,_ in rr['terms'])}
    for name,obj in [('factored_source.json',fac),('factorization_certificate.json',fc),('projected.json',pr),('projection_certificate.json',pc),('projection_check.json',check),
      ('translation_certificate.json',{'convention':'old=new+shift','shifts':sorted(shifts.items())}),('equation.json',eq),('expanded_polynomial.json',poly),('METRICS.json',metrics)]:
        (out/name).write_bytes(E.canonical_bytes(obj))
    print(json.dumps(metrics,indent=2))

if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('--source',type=Path,default=SOURCE);ap.add_argument('--output',type=Path,default=ROOT/'stages/modular');ap.add_argument('--parent',type=Path,default=PARENT);ap.add_argument('--support',type=int,default=16)
    a=ap.parse_args();build(a.source,a.output,a.parent,a.support)
