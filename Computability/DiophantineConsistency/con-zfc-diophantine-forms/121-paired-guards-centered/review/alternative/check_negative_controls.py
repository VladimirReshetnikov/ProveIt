#!/usr/bin/env python3
"""Run independently specified corruption controls and scalar mathematical fixtures."""
import argparse,copy,json,math,tempfile,shutil,hashlib
from pathlib import Path
import audit_paired_independent as A

def mutation(cand,base,squared,name,edit):
    with tempfile.TemporaryDirectory(prefix='paired-audit-') as temp:
        target=Path(temp)
        for p in cand.glob('*.json'): shutil.copy2(p,target/p.name)
        edit(target)
        try: A.run(base,target,squared)
        except ValueError as e:return {'mutation':name,'status':'REJECTED','reason':str(e)}
        raise ValueError('negative control was accepted: '+name)
def change(p,name,fn):
    x=A.load(p/name);fn(x);(p/name).write_bytes(A.canon(x))
    if name=='projection_certificate.json' and (p/'terminal_elimination_certificate.json').exists():(p/'terminal_elimination_certificate.json').write_bytes(A.canon(x))
def main():
    ap=argparse.ArgumentParser();ap.add_argument('--baseline',required=True,type=Path);ap.add_argument('--candidate',required=True,type=Path);ap.add_argument('--output',required=True,type=Path);ap.add_argument('--squared-radius',action='store_true');z=ap.parse_args();controls=[]
    controls.append(mutation(z.candidate,z.baseline,z.squared_radius,'pairguard_product_sign_flip',lambda p:change(p,'paired_source.json',lambda e:e['residuals'][-1]['terms'].__setitem__(0,[-e['residuals'][-1]['terms'][0][0],e['residuals'][-1]['terms'][0][1]]))))
    controls.append(mutation(z.candidate,z.baseline,z.squared_radius,'pair_sum_endpoint_swap',lambda p:change(p,'pair_certificate.json',lambda e:e['pairs'][0].__setitem__('positive_power_output',e['pairs'][1]['right']))))
    controls.append(mutation(z.candidate,z.baseline,z.squared_radius,'delete_retained_bootstrap_guard',lambda p:change(p,'pair_certificate.json',lambda e:e['retained_single_guards'].remove(9))))
    controls.append(mutation(z.candidate,z.baseline,z.squared_radius,'wrong_monic_restoration',lambda p:change(p,'projection_certificate.json',lambda e:e['steps'][0]['restoration'][0].__setitem__(0,e['steps'][0]['restoration'][0][0]+1))))
    controls.append(mutation(z.candidate,z.baseline,z.squared_radius,'expanded_coefficient_off_by_one',lambda p:change(p,'expanded_polynomial.json',lambda e:e['terms'][0].__setitem__(0,e['terms'][0][0]+1))))
    controls.append(mutation(z.candidate,z.baseline,z.squared_radius,'declared_square_root_corruption',lambda p:change(p,'factorization_certificate.json',lambda e:next(iter(e['square_roots'].values()))[0].__setitem__(0,next(iter(e['square_roots'].values()))[0][0]+1))))
    # Removing a required bootstrap sign makes the pre-power lower-bound certificate unavailable.
    original=A.load(A.source_dir(z.baseline)/'mixed_source.json');dom=A.load(A.source_dir(z.baseline)/'domain_certificate.json');names={v['name']:i for i,v in enumerate(original['variables'])};pc=A.load(z.candidate/'pair_certificate.json');initial=dict.fromkeys(pc['retained_single_guards'],0);W=dom['square_budget']['frame_variable'];initial[W]=2
    pre=A.load(z.candidate/'paired_source.json');rows=[A.poly(r['terms']) for r in pre['residuals'][:len(original['residuals'])]]
    for name in ('fact0.remainder','fact0.slack','choose0.oslack'):
        seed=dict(initial);seed.pop(names[name]);bounds,_=A.closure(rows,seed)
        A.need(bounds.get(names['mul.400'],-1)<2,'bootstrap should fail without '+name)
        controls.append({'mutation':'remove_presemantic_seed_'+name,'status':'REJECTED','reason':'q>=2 not derivable from remaining pre-power sign seeds'})
    # Deleting F's guard without the three radius-anchor edits is not the proved transform.
    rawrows=[A.poly(r['terms']) for r in original['residuals']]
    seed=dict(initial);seed.pop(names['fact0.output'],None)
    badbounds,_=A.closure(rawrows,seed)
    A.need(names['mul.2'] not in badbounds,'old unsigned radius unexpectedly certified')
    controls.append({'mutation':'delete_F_guard_without_square_anchor_edits','status':'REJECTED','reason':'old rho=F*t² has no proved nonnegative lower bound before power recovery'})
    # Wide-radius factorial characterization: exact integer arithmetic,
    # all proposed F in finite signed range plus the true factorial each n.
    cases=0;genuine=[]
    for n in range(1,10):
        G=math.factorial(n)
        for F in sorted(set(range(-12,513))|{G-1,G,G+1}):
            rho=F*F*n*n;V=(rho+1)**n;D=math.comb(rho+n,n)
            possible=D*(F-1)<V<=D*F
            A.need(possible==(F==G),'squared radius factorial counterexample')
            if possible:
                u=V+D-D*F-1;v=D*F-V
                A.need(u>=0 and v>=0 and D==u+v+1,'factorial constructive witnesses')
                genuine.append({'n':n,'F':F,'rho':rho,'u':u,'v':v})
            cases+=1
    out={'status':'PASS','corruption_controls':controls,'wide_radius_factorial_cases':cases,'constructive_factorial_cases':len(genuine),
         'scope':'Finite negative controls and regression fixtures; unbounded correctness is proved in REVIEW.md.'}
    z.output.write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
if __name__=='__main__':main()
