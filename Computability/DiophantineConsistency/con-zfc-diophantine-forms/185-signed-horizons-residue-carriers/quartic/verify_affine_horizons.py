#!/usr/bin/env python3
"""Independent finite audit: binomial substitution and triangular SOS expansion.

Does not import the constructor.  These checks authenticate the literal
polynomials and exact coordinate algebra, not the unbounded Pell theorem.
"""
from pathlib import Path
from collections import Counter
from math import comb
import hashlib,json

ROOT=Path(__file__).resolve().parent
SOURCES={'p213':'9a16fcdcea6310c01236ce500f753034f4095c1956b488f9fd8325b1ceeb89c6',
         'p215':'8d919a1e5d6a802765b6d010c0140fb1d83c3d36d211b209b7a8d2fb3f3fb6f6'}
PROFILES={
    'p212_minimum8':('p213',8,None,1,False),
    'p214_scaled_square':('p215',8,512,2,True),
}

def fail(message):raise RuntimeError(message)
def read(path):return json.loads(path.read_text())
def poly(terms):
    result={}
    for c,mon in terms:
        if not isinstance(c,int) or not c or mon!=sorted(mon):fail('noncanonical term')
        key=tuple(mon)
        if key in result:fail('duplicate term')
        result[key]=c
    return result

def normalize(counter):return {m:c for m,c in counter.items() if c}

def check_inherited_commutation(source):
    """Changed source rows remain isolated through the inherited reductions."""
    chain=read(ROOT/'OPTIMIZATION_CHAIN.json')
    name='P213' if source=='p213' else 'P215'
    profile=next(p for p in chain['profiles'] if p['name']==name)
    protected_coordinates={0,184} if source=='p213' else {0,93,185,214}
    protected_rows={130} if source=='p213' else {130,152,153}
    count=0
    for s in profile['stages']:
        c=read(ROOT/'inherited_certificates'/s['certificate'])
        if s['kind']=='basis':
            for target,origin,_ in c:
                if target in protected_rows or origin in protected_rows:fail('mixed changed row')
                count+=1
        elif s['kind']=='translations':
            for coordinate,_ in c['operations']:
                if coordinate in protected_coordinates:fail('translated protected coordinate')
                count+=1
        else:
            for op in c['operations']:
                if op.get('type')=='row':
                    if op['source'] in protected_rows or op['target'] in protected_rows:fail('mixed changed row')
                elif op['coordinate'] in protected_coordinates:fail('changed protected coordinate')
                count+=1
    adir='affine213' if source=='p213' else 'affine215'
    c=read(ROOT/'inherited_certificates/stages'/adir/'projection_certificate.json')
    p=c['eliminated_coordinate'];r=c['omitted_residual']
    protected_coordinates={i+(i>=p) for i in protected_coordinates}
    protected_rows={i+(i>=r) for i in protected_rows}
    if p in protected_coordinates or any(i in protected_rows for _,i in c['affine_consequence']['row_combination']):
        fail('affine projection touches changed data')
    rdir='projection214_affine' if source=='p213' else 'projection216'
    c=read(ROOT/'inherited_certificates/stages'/rdir/'projection_certificate.json')
    for step in reversed(c['steps']):
        protected_coordinates={step['retained_old_indices'][i] for i in protected_coordinates}
        deleted=step['deleted_row'];protected_rows={i+(i>=deleted) for i in protected_rows}
        if any(i in protected_coordinates and v for i,v in step['direction']):
            fail('radical direction changes protected coordinate')
        if deleted in protected_rows:fail('radical deleted changed row')
    return {'optimization_operations_inspected':count,'radical_steps':len(c['steps']),
        'protected_source_rows':sorted(protected_rows),'protected_source_coordinates':sorted(protected_coordinates),
        'conclusion':'Horizon and growth-row replacements commute with the inherited certified reductions.'}

def expand_substitution(terms,parameter,minimum):
    answer=Counter()
    for coefficient,monomial in terms:
        order=monomial.count(0)
        rest=tuple(i-1 for i in monomial if i)
        for power in range(order+1):
            key=tuple(sorted(rest+(parameter-1,)*power))
            answer[key]+=coefficient*comb(order,power)*minimum**order*2**power
    return normalize(answer)

def check_profile(name,profile):
    source,minimum,multiplier,square,reduce=profile
    raw=(ROOT/source/'equation.json').read_bytes()
    if hashlib.sha256(raw).hexdigest()!=SOURCES[source]:fail('source hash')
    old=json.loads(raw);new=read(ROOT/'affine_horizons'/name/'equation.json')
    cert=read(ROOT/'affine_horizons'/name/'certificate.json')
    expected_horizon=16 if source=='p213' else 128
    parameter=next(i for i,v in enumerate(old['variables']) if v['name']=='cofinal.horizon_root')
    hi=next(i for i,r in enumerate(old['residuals']) if r['label']=='cofinal.horizon')
    if poly(old['residuals'][hi]['terms'])!={():-expected_horizon,(0,):1,(parameter,parameter):-4}:
        fail('source horizon binding')
    if minimum%4 or minimum<8:fail('unproved minimum')
    if source=='p215' and multiplier*square*square*minimum**3 < 1048576:
        fail('growth majorant')
    computed=[];mapping=[]
    for i,r in enumerate(old['residuals']):
        if i==hi:continue
        terms=r['terms']
        if r['label']=='growth.t_squared':
            ti=next(i for i,v in enumerate(old['variables']) if v['name']=='growth.t_squared')
            if poly(terms)!={(0,0):-1,(ti,):1}:fail('source square binding')
            terms=[[-square,[0,0]],[1,[ti]]]
        if r['label']=='growth.index':
            ki=next(i for i,v in enumerate(old['variables']) if v['name']=='growth.index')
            if poly(terms)!={(ki,):1,(ti,ti):-1}:fail('source index binding')
            terms=[[1,[ki]],[-multiplier,[ti,ti]]]
        computed.append(expand_substitution(terms,parameter,minimum))
        mapping.append([i,len(computed)-1])
    operations=[]
    if reduce:
        labels=[r['label'] for i,r in enumerate(old['residuals']) if i!=hi]
        si=labels.index('growth.t_squared')
        for label,c in [('shared.frame_definition',-4),('cap.pooled_index_residue',2)]:
            if c%square:fail('noninteger elementary row move')
            target=labels.index(label);q=dict(computed[target])
            for mon,coef in computed[si].items():q[mon]=q.get(mon,0)+(c//square)*coef
            computed[target]=normalize(q)
            operations.append({'target':target,'source':si,'multiplier':c//square})
    if cert['row_operations']!=operations or cert['old_to_new_rows']!=mapping:fail('certificate binding')
    if len(computed)!=len(new['residuals']):fail('row count')
    for i,(q,r) in enumerate(zip(computed,new['residuals'])):
        if q!=poly(r['terms']):fail('row identity '+str(i))
        if max(map(len,q),default=0)>2:fail('row degree')
    if new['domain']!='unrestricted integers':fail('domain')
    if len(new['variables'])!=len(old['variables'])-1:fail('dimension')
    live={i for p in computed for mon in p for i in mon}
    if live!=set(range(len(new['variables']))):fail('liveness')
    # Each unordered pair is multiplied once, with2 on the off-diagonal.
    sos=Counter()
    for p in computed:
        items=list(p.items())
        for i,(m,c) in enumerate(items):
            for j in range(i,len(items)):
                n,d=items[j]
                sos[tuple(sorted(m+n))]+=(1 if i==j else 2)*c*d
    sos=normalize(sos)
    supplied=read(ROOT/'affine_horizons'/name/'expanded_polynomial.json')
    if poly(supplied['terms'])!=sos:fail('expanded polynomial')
    metrics={'variables':len(new['variables']),'residuals':len(computed),
        'degree':max(map(len,sos)),'monomials':len(sos),
        'coefficient_height':max(map(abs,sos.values())),
        'residual_coefficient_height':max(abs(c) for p in computed for c in p.values()),
        'residual_monomials':sum(map(len,computed))}
    if metrics!=read(ROOT/'affine_horizons'/name/'metrics.json'):fail('metrics')
    if metrics['degree']!=4:fail('exact quartic degree')
    return dict(metrics,equation_sha256=hashlib.sha256((ROOT/'affine_horizons'/name/'equation.json').read_bytes()).hexdigest(),
        status='PASS',identities_checked=len(computed),elementary_row_moves=len(operations),
        inherited_reduction_commutation=check_inherited_commutation(source))

if __name__=='__main__':
    print(json.dumps({'status':'PASS','profiles':{n:check_profile(n,p) for n,p in PROFILES.items()},
        'scope':'Exact source binding, integral substitution and elementary residual operations, liveness, all collected quartic coefficients, and attained degree. The semantic equivalence is proved separately.'},indent=2))
