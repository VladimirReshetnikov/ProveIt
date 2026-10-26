#!/usr/bin/env python3
"""Independent exact replay. This verifier does not import producer code.

It checks the finite transformations and literal coefficients. The semantic
horizon change and inherited logical calibration are mathematical proofs,
not consequences of this finite computation.
"""
from collections import Counter
from pathlib import Path
from itertools import product
import argparse,hashlib,json

ROOT=Path(__file__).resolve().parent
SOURCE_HASH='20a2108353a3756ed7d1ddfdc71695131dcf0b6d94039988d9565ac48e6e1f0a'

def require(test,message):
    if not test:raise ValueError(message)
def load(p):return json.loads(p.read_text())
def pack(o):return (json.dumps(o,sort_keys=True,separators=(',',':'))+'\n').encode()
def digest(o):return hashlib.sha256(pack(o)).hexdigest()
def clean(p):return {m:c for m,c in p.items() if c}
def asdict(ts):
    p=Counter()
    for c,m in ts:
        require(type(c) is int,'Noninteger coefficient')
        require(all(type(i) is int and i>=0 for i in m),'Invalid monomial')
        p[tuple(sorted(m))]+=c
    return clean(p)
def ts(p):return [[c,list(m)] for m,c in sorted(p.items()) if c]
def expand_rows(rows):
    p=Counter()
    for r in rows:
        d=asdict(r['terms'])
        for m,c in d.items():
            for n,e in d.items():p[tuple(sorted(m+n))]+=c*e
    return clean(p)
def transform(row,fscale):
    # Independent term-by-term cartesian expansion: oldt=2+4z, oldF=s*f.
    p=Counter()
    for c,monomial in row['terms']:
        factors=[]
        for i in monomial:
            require(i!=178,'Removed horizon coordinate occurs outside horizon row')
            if i==0:factors.append([(2,()),(4,(0,))])
            elif i==2:factors.append([(fscale,(2,))])
            else:factors.append([(1,(i-(i>178),))])
        for choice in product(*factors):
            cf=c;mm=[]
            for coef,mon in choice:cf*=coef;mm.extend(mon)
            p[tuple(sorted(mm))]+=cf
    return clean(p)
def check_literal(folder,eq):
    pp=expand_rows(eq['residuals'])
    got=load(folder/'expanded_polynomial.json')
    require(got['variables']==209,'Expanded variable count')
    require(asdict(got['terms'])==pp,'Expanded polynomial differs')
    used={i for r in eq['residuals'] for _,m in r['terms'] for i in m}
    require(used==set(range(209)),'Not all209 coordinates occur')
    measured={'variables':209,'residuals':149,'degree':max(map(len,pp)),
       'monomials':len(pp),'coefficient_height':max(abs(c) for c in pp.values()),
       'residual_height':max(abs(c) for r in eq['residuals'] for c,_ in r['terms']),
       'residual_terms':sum(len(r['terms']) for r in eq['residuals'])}
    require(measured==load(folder/'metrics.json'),'Metric discrepancy')
    require(measured['degree']==4,'Degree is not exactly four')
    # This displays an actual nonzero quartic coefficient, independently of metadata.
    attained=next((m,c) for m,c in sorted(pp.items()) if len(m)==4 and abs(c)==measured['coefficient_height'])
    return {'metrics':measured,'equation_sha256':digest(eq),'height_attaining_term':[attained[1],list(attained[0])]}

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--receipt',type=Path);a=ap.parse_args()
    raw=(ROOT/'source210/equation.json').read_bytes()
    require(hashlib.sha256(raw).hexdigest()==SOURCE_HASH,'Frozen source hash')
    old=json.loads(raw)
    require(len(old['variables'])==210 and len(old['residuals'])==150,'Source shape')
    require(asdict(old['residuals'][149]['terms'])=={(0,):-(1<<19),(0,209):-(1<<20),(2,):1},'Growth divisibility binding')
    affine=load(ROOT/'source210/affine_horizon_equation.json')
    require(asdict(affine['residuals'][125]['terms'])=={():-2,(0,):1,(178,):-4},'Affine horizon binding')
    for j in range(150):
        if j!=125:require(old['residuals'][j]==affine['residuals'][j],f'Unstated semantic edit row{j}')
    receipt={'source_sha256':SOURCE_HASH,'profiles':{},'checked':'All sparse identities, row transformations, live variables, degrees, collected coefficients and heights. No consistency or root search.'}
    raw128=None
    for fscale in [64,128]:
        folder=ROOT/'equations'/f'affine209_F{fscale}';eq=load(folder/'equation.json');cert=load(folder/'certificate.json')
        require(len(eq['variables'])==209 and len(eq['residuals'])==149,'Output shape')
        require(cert['old_source_sha256']==SOURCE_HASH,'Source certificate hash')
        require(cert['affine_source_sha256']==digest(affine),'Affine certificate hash')
        require(cert['output_sha256']==digest(eq),'Output certificate hash')
        require((1<<20)%fscale==0,'Scale not justified by source divisibility')
        for j,r in enumerate(old['residuals']):
            if j==125:continue
            want=transform(r,fscale)
            if j==149:
                require(all(c%fscale==0 for c in want.values()),'Row normalization not integral')
                want={m:c//fscale for m,c in want.items()}
            k=j-(j>125)
            require(asdict(eq['residuals'][k]['terms'])==want,f'Substitution mismatch row{j} scale{fscale}')
            require(max(map(len,want),default=0)<=2,'Nonquadratic row')
        receipt['profiles'][folder.name]=check_literal(folder,eq)
        if fscale==128:raw128=eq
    folder=ROOT/'equations/affine209_F128_basis';eq=load(folder/'equation.json');cert=load(folder/'certificate.json')
    require(cert['input_sha256']==digest(raw128),'Row basis input hash')
    require(cert['output_sha256']==digest(eq),'Row basis output hash')
    source=cert['source_row_unchanged'];require(eq['residuals'][source]==raw128['residuals'][source],'Carrier was modified')
    edits={e['target_row']:e for e in cert['edits']}
    cp=asdict(raw128['residuals'][source]['terms'])
    for j,r in enumerate(raw128['residuals']):
        want=Counter(asdict(r['terms']))
        if j in edits:
            e=edits[j];require(e['source_row']==source,'Different carrier')
            require(type(e['source_multiplier']) is int,'Nonintegral row multiplier')
            for m,c in cp.items():want[m]+=e['source_multiplier']*c
        require(clean(want)==asdict(eq['residuals'][j]['terms']),f'Row basis mismatch row{j}')
    receipt['profiles'][folder.name]=check_literal(folder,eq)
    if a.receipt:a.receipt.write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps(receipt,indent=2))

if __name__=='__main__':main()
