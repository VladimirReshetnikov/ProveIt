#!/usr/bin/env python3
"""Independent source-interface and theorem-premise audit.

No producer, optimizer, or producer checker is imported. Projection/coefficient
verification is a separate checker. All integer arithmetic is exact.
"""
import argparse, collections, hashlib, json, sys, zipfile
from pathlib import Path

OMITTED={548,575,584,592,600,609,618,627,636}
OUTPUTS={546,573,583,591,599,607,617,625,635}
SELECTED=[7,10,12,13,14,15,17,18,20]

def require(p, why):
    if not p: raise ValueError(why)

def read(p): return json.loads(p.read_text())
def poly(terms):
    d=collections.defaultdict(int)
    for c,m in terms: d[tuple(sorted(m))]+=c
    return {m:c for m,c in d.items() if c}
def plus(a,b,k=1):
    d=collections.defaultdict(int,a)
    for m,c in b.items(): d[m]+=k*c
    return {m:c for m,c in d.items() if c}
def times(a,b):
    d=collections.defaultdict(int)
    for ma,ca in a.items():
        for mb,cb in b.items(): d[tuple(sorted(ma+mb))]+=ca*cb
    return {m:c for m,c in d.items() if c}
def var(v):return {(v,):1}
def constant(c):return {():c} if c else {}
def subst(p,values):
    d={}
    for m,c in p.items():
        term=constant(c)
        for v in m:term=times(term,values.get(v,var(v)))
        d=plus(d,term)
    return d

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--package',type=Path,required=True)
    ap.add_argument('--archive',type=Path,required=True);ap.add_argument('--output',type=Path,required=True)
    a=ap.parse_args();p=a.package;s=p/'source'
    original=read(s/'parent75.json');raw=read(s/'raw_builder.json');source=read(p/'parent.json')
    cert=read(s/'sign_certificate.json');old_domain=read(s/'domain75.json');domain=read(p/'domain.json')
    rows=[poly(q['terms']) for q in source['residuals']]
    require(source['variables'][:1259]==raw['variables']==original['variables'][:1259], 'Original raw coordinate metadata')
    require(len(source['variables'])==1457 and len(rows)==1243,'66-predicate raw dimensions')
    require(source['residuals'][:1176]==original['residuals'][:1176], 'Exactly one changed body row')
    require(all(source['residuals'][i]['terms']==raw['rows'][i]['terms'] for i in range(1176)), 'Original raw source row binding')
    expected=[g['predicate'] for g in old_domain['guards'] if not(g['predicate']['kind']=='retained_scalar' and g['predicate']['raw_variables'][0] in OMITTED)]
    require([g['predicate'] for g in domain['guards']]==expected and len(expected)==66,'Exact retained predicate inventory')
    for j,g in enumerate(domain['guards']):
        x,y,z=range(1259+3*j,1262+3*j)
        require(g['auxiliary']==[x,y,z], 'Fresh disjoint guard slots')
        require(rows[1177+j]==poly(g['predicate']['terms']+[[-1,[x,x]],[-1,[y,y]],[-1,[z,z]],[-1,[z]]]),'Literal three-square guard')
    atoms=sorted({u[1] for c in raw['powers'] for u in [c['base'],c['exponent'],c['output']]})
    require(atoms==cert['frame_arguments'] and len(atoms)==43, 'Actual distinct power atoms')
    expected_frame=plus(var(643),constant(-2))
    for v in atoms:expected_frame=plus(expected_frame,times(var(v),var(v)) if v in OUTPUTS else var(v),-1)
    if rows[1176]==expected_frame:
        frame_mode='squared_outputs'
    else:
        expected_frame=plus(var(643),constant(-5))
        for v in atoms:
            if v not in OUTPUTS:expected_frame=plus(expected_frame,var(v),-1)
        for v in sorted(OMITTED):expected_frame=plus(expected_frame,times(var(v),var(v)),-1)
        require(rows[1176]==expected_frame,'Exact squared-quotient frame')
        frame_mode='squared_quotients'
    checked_ideals=0
    def ideal(rec,target=None):
        nonlocal checked_ideals
        acc={}
        for t in rec['row_combination']:
            require(t['row']!=1176, 'An inherited ideal must not assume the old frame')
            acc=plus(acc,times(poly(t['multiplier']),rows[t['row']]))
        if target is None:target=poly(rec.get('polynomial',rec.get('expanded_polynomial')))
        require(acc==target,'Exact entire original-row ideal');checked_ideals+=1
    ideal(cert['positive_prefix']['canonical_modulus_cut'])
    pp=cert['prefix_proof']
    steps=sum((x['preceding_sign_steps'] for x in pp['five_stages']),[])+pp['final_sign_steps']
    bound_rules=pp['preliminary_t_n_bounds']+pp['five_stages']
    for r in bound_rules:ideal(r,plus(times(poly(r['factor']),var(r['variable'])),poly(r['rhs']),-1))
    for r in steps:
        target=plus({(r['variable'],):r['coefficient']},poly(r['rhs']),-1)
        require(r['coefficient']>0 and rows[r['row']] in (target,{m:-c for m,c in target.items()}),'Actual sign-deduction row')
        if r['kind']=='affine_square':require(times(poly(r['square_root']),poly(r['square_root']))==poly(r['rhs']),'Entire affine square')
        else:
            require(r['kind']=='positive_monomials' and all(c>0 for c,_ in r['rhs']),'Nonnegative monomial rule')
            odd={v for m in poly(r['rhs']) for v,e in collections.Counter(m).items() if e%2}
            require(odd==set(r['dependencies']),'Exact odd-power dependencies')
    # Independently rederive the early N>=2 premise by local monic substitution.
    values={}
    for j in [78,79,80,81,83,84]:
        v=raw['rows'][j]['gate'];require(v is not None and rows[j].get((v,))==1,'Early unit gate')
        values[v]=subst({m:-c for m,c in rows[j].items() if m!=(v,)},values)
    R=poly([[1,[91]],[-1,[94]],[-1,[95]],[-1,[]]])
    E=poly([[1,[87,91]],[-1,[93]],[-1,[95]]])
    require(subst(rows[85],values)==R and subst(rows[82],values)==plus(R,E,-1),'Early ceiling and remainder cuts')
    require(plus(times(var(87),R),E,-1)==poly([[1,[93]],[-1,[87,94]],[-1,[87,95]],[1,[95]],[-1,[87]]]),'Early recovered output identity')
    initial={g['predicate']['raw_variables'][0]:0 for g in domain['guards'] if g['predicate']['kind']=='retained_scalar'}
    initial.update({87:2,93:2})
    lower=dict(initial)
    def simple_low(ts):
        total=0
        for c,m in ts:
            if c<0:return None
            val=1
            for v,e in collections.Counter(m).items():
                if v not in lower:
                    if e%2:return None
                    val=0
                else:val=min(3,val*lower[v]**e)
            total=min(3,total+c*val)
        return total
    def strictly_positive(q):
        used={v for m in q for v in m}
        if not used<=lower.keys():return False
        shifted=subst(q,{v:plus(var(v),constant(lower[v])) for v in used})
        return shifted.get((),0)>0 and all(c>=0 for c in shifted.values())
    # Saturate a finite library of sound deductions, rather than trust the producer's order.
    for iteration in range(100):
        before=dict(lower)
        for r in steps:
            v=r['variable'];val=0 if r['kind']=='affine_square' else simple_low(r['rhs'])
            if val is not None:lower[v]=max(lower.get(v,0),min(3,val//r['coefficient']))
        for r in bound_rules:
            F,R0,L=poly(r['factor']),poly(r['rhs']),r['lower']
            if strictly_positive(F) and strictly_positive(plus(R0,F,1-L)):
                lower[r['variable']]=max(lower.get(r['variable'],0),L)
        # Literal canonical-modulus cut gives M=1+f*(raw59+1)>=1.
        if {87,59}<=lower.keys():lower[129]=max(lower.get(129,0),1)
        if lower==before:break
    else:raise ValueError('Sign saturation did not terminate')
    for r in cert['initial_A_D_bounds']:
        F,R0,L=poly(r['factor']),poly(r['rhs']),r['lower']
        ideal(r,plus(times(F,var(r['variable'])),R0,-1))
        require(strictly_positive(F) and strictly_positive(plus(R0,F,1-L)), 'Independent initial modulus bootstrap sign')
        lower[r['variable']]=max(lower.get(r['variable'],0),L)
    require(set(atoms)-OUTPUTS<=lower.keys(),'All unsigned frame atoms have independent signs')
    require(not (OUTPUTS|OMITTED)&lower.keys(),'No omitted sign assumed in the early closure')
    require(lower[531]>=2 and all(lower.get(c['exponent'][1],0)>=1 for c in raw['powers']),'All bases/indices needed before arithmetic interpretation')
    retained={g['predicate']['raw_variables'][0] for g in domain['guards'] if g['predicate']['kind']=='retained_scalar'}
    selected=[]
    for j in SELECTED:
        c=cert['power_calls'][j];seed=next(s0 for s0 in cert['seeds'] if s0['aliases']['k']==c['exponent'])
        require(c['base']==531 and c['output'] in OUTPUTS and seed['aliases']['YminusK'] in retained,'Independent signed-power applicability')
        selected.append([j,c['output'],c['exponent'],seed['aliases']['YminusK']])
    for k in ['bootstrap_norm','unit_norm_cut','comparison_base_constructor','comparison_base_congruence','positive_V_product']:ideal(cert[k])
    for m in cert['moduli']:ideal(m['cut'])
    for seed in cert['seeds']:
        for c in seed['cuts'].values():ideal(c)
    for call in cert['power_calls']:ideal(call['cut'])
    # Check the binomial/range cuts by a separate local elimination using actual gate metadata.
    def local(lo,hi):
        submap={};out={}
        for j in range(lo,hi+1):
            v=raw['rows'][j]['gate']
            if v is None:out[raw['rows'][j]['label']]=subst(rows[j],submap)
            else:
                require(rows[j].get((v,))==1,'Local unit pivot')
                submap[v]=subst({m:-c for m,c in rows[j].items() if m!=(v,)},submap)
        return out
    if frame_mode=='squared_quotients':
        local_radix={}
        for j in range(506,509):
            v=raw['rows'][j]['gate']
            require(rows[j].get((v,))==1,'Radix unit gate')
            local_radix[v]=subst({m:-c for m,c in rows[j].items() if m!=(v,)},local_radix)
        require(local_radix[530]==poly([[1,[129]],[1,[93,129]],[1,[113,129]]]),'Radix b=M*(1+N+raw113) bound')
        require(lower[129]>=1 and lower[93]>=2 and lower[113]>=0,'M<=b before arithmetic meanings')
    cuts=local(543,593)
    range_records=[('a',575,573,574,576,577),('b',584,583,574,585,586),('c',592,591,574,593,594),('d',600,599,574,601,602),('S',609,607,608,610,611),('Sp',618,617,608,619,620),('u',627,625,626,628,629),('vq',636,635,626,637,638)]
    for name,q,m,L,r,s0 in range_records:
        require(cuts['crt.range.'+name+'.quotient_multiple']==poly([[1,[m]],[-1,[129,L,q]],[-1,[r]]]),'Range quotient identity')
        require(cuts['crt.range.'+name+'.remainder_bound']==poly([[1,[L]],[-1,[r]],[-1,[s0]],[-1,[]]]),'Range remainder identity')
        require(r in retained and s0 in retained and lower[L]>=1 and lower[129]>=1,'Range sign recovery premises')
    cuts=local(521,531)
    require(cuts['choose1.digit']==poly([[1,[546]],[-1,[547,111]],[-1,[547,530,548]],[-1,[549]]]),'Ninth quotient identity')
    require(cuts['choose1.remainder_bound']==poly([[1,[547]],[-1,[549]],[-1,[550]],[-1,[]]]),'Ninth remainder bound')
    require(cuts['choose1.digit_bound']==poly([[1,[530]],[-1,[111]],[-1,[551]],[-1,[]]]),'Ninth digit bound')
    require({549,550,551}<=retained and 111 in lower and lower[547]>=1,'Ninth sign recovery premises')
    # Exact local numerical diagnostics for both sign cases; the unbounded lemma is in REVIEW.md.
    count=0
    for W in range(4,13):
        A=W**W+1
        for n in range(2,W):
            T=2*A*n-n*n-1
            x,y=1,0
            for k in range(1,W):
                x,y=A*x+(A*A-1)*y,x+A*y
                nk=n**k
                require((x-(A-n)*y-nk)%T==0,'Pell power congruence')
                for m in range(1-W,W):
                    require(abs(m*nk+1)<T and m*nk+1!=0,'Signed negative-branch contradiction')
                    require(((-x-(A-n)*y-m)%T)!=0,'No negative-X signed-output zero')
                    require(((x-(A-n)*y-m)%T==0)==(m==nk),'Positive branch exactness')
                    count+=1
    A=20;n=1;k=1;m=-1;T=2*A*n-n*n-1
    require((-A-(A-n)-m)%T==0,'Essential n>=2 counterexample retained')
    quotient_diagnostics=0
    if frame_mode=='squared_quotients':
        for W in range(7,15):
            A=W**W+1
            for n in range(2,W-4):
                T=2*A*n-n*n-1
                x,y=1,0
                for k in range(1,W-4):
                    x,y=A*x+(A*A-1)*y,x+A*y
                    nk=n**k
                    for m in [-W**4+1,-1,0,1,W**4-1]:
                        require(abs(m*nk+1)<T and m*nk+1!=0,'Quotient-radius negative branch')
                        require((-x-(A-n)*y-m)%T!=0,'Quotient-radius negative-X exclusion')
                        require(((x-(A-n)*y-m)%T==0)==(m==nk),'Quotient-radius exact positive branch')
                        quotient_diagnostics+=1
    # Pinned immediate calibration sources and the unconditional named endpoints.
    z=zipfile.ZipFile(a.archive);root='ConZFC_407_888_Quartics/upstream/provenance/upstream/calibration/'
    pins=json.loads(z.read(root+'CALIBRATION_PINS.json'));cal=[]
    for f in pins['files']:
        names=[n for n in z.namelist() if n.endswith('/'+f['local_file'])]
        require(len(names)==1,'Unique pinned source member')
        data=z.read(names[0]);digest=hashlib.sha256(data).hexdigest()
        require(len(data)==f['bytes'] and digest==f['sha256'],'Actual calibration file bytes/hash')
        cal.append({'file':f['local_file'],'sha256':digest,'bytes':len(data),'repository_path':f['repository_path']})
    ke=z.read(root+'KEndpoint.lean').decode();cc=z.read(root+'ConstructibleChoice.lean').decode()
    require('theorem c222_iff_zf_refutation' in ke.split('\nsection\n')[0],'Unconditional C222 endpoint before machine-parameter section')
    require('theorem zf_refutation_iff_zfc_refutation' in cc,'Named constructible-choice endpoint')
    files=['parent.json','domain.json','source/raw_builder.json','source/parent75.json','source/domain75.json','source/sign_certificate.json','source/arithmetic_interfaces.json']
    result={'status':'PASS','optimized_python':bool(sys.flags.optimize),'source_guards':66,'frame_mode':frame_mode,'quotient_radius_diagnostics':quotient_diagnostics,'body_variables':1259,'body_residuals':1177,'changed_body_rows':[1176],'selected_calls':selected,'unsigned_frame_atoms_verified':34,'prefix_coordinates_certified':sum(v<643 for v in lower),'sign_saturation_passes':iteration+1,'prefix_row_steps_checked':len(steps),'complete_original_row_ideals_checked':checked_ideals,'range_cuts_verified':16,'exact_binomial_cuts_verified':3,'local_signed_power_diagnostics':count,'essential_base_one_counterexample':True,'calibration_commit':pins['commit'],'calibration_archive_sha256':hashlib.sha256(a.archive.read_bytes()).hexdigest(),'calibration_files':cal,'input_sha256':{f:hashlib.sha256((p/f).read_bytes()).hexdigest() for f in files},'scope':'Independent exact source-interface/row/prefix/calibration-byte audit. Unbounded ordinary proof is separate. No new Lean or object-language ZFC proof is claimed.'}
    a.output.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n');print(json.dumps({k:v for k,v in result.items() if k not in ['input_sha256','calibration_files','selected_calls']},indent=2))

if __name__=='__main__':main()
