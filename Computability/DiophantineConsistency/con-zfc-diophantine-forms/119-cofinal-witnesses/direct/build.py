#!/usr/bin/env python3
"""A cofinal 512-integer specialization of the exact incoming 517 quartic.

No source builder or optimizer is imported.  The only inputs are the frozen
literal residuals.  Zero-set soundness uses the certificate in PROOF.md;
the cofinal completeness argument is mathematical, not a finite test.
"""
from pathlib import Path
from collections import defaultdict, Counter
import hashlib, json, argparse, copy

BASE = Path(__file__).resolve().parent
SOURCE = BASE / 'source517.json'

def encoded(value):
    return (json.dumps(value, sort_keys=True, separators=(',', ':'))+'\n').encode()

def digest(data): return hashlib.sha256(data).hexdigest()

def collect(terms):
    out=defaultdict(int)
    for c,m in terms: out[tuple(sorted(m))]+=c
    return {m:c for m,c in out.items() if c}

def terms(poly): return [[c,list(m)] for m,c in sorted(poly.items())]

def expand(equation):
    out=defaultdict(int)
    for row in equation['residuals']:
        p=collect(row['terms'])
        for m,c in p.items():
            for n,d in p.items(): out[tuple(sorted(m+n))]+=c*d
    return {'schema':'sparse_integer_polynomial_v1','domain':'unrestricted integers',
            'variables':len(equation['variables']),
            'terms':terms({m:c for m,c in out.items() if c})}

def build(source):
    if source['domain']!='unrestricted integers' or len(source['variables'])!=517 or len(source['residuals'])!=310:
        raise ValueError('Wrong frozen 517-variable source')
    names={v['name']:i for i,v in enumerate(source['variables'])}
    ports={k:names[k] for k in ('t0','y','fact0.output','pow0.output')}
    if ports!={'t0':0,'y':2,'fact0.output':3,'pow0.output':6}:
        raise ValueError('Unexpected centered coordinate binding')
    labels={row['label']:i for i,row in enumerate(source['residuals'])}
    rid_h=labels['nonnegative.0']; rid_F=labels['nonnegative.3']; rid_y=labels['nonnegative.12']
    if (rid_h,rid_F,rid_y)!=(247,249,252): raise ValueError('Unexpected guard row indices')
    removed=[names[x] for x in ('nonnegative.0.b','nonnegative.0.c','nonnegative.12.a','nonnegative.12.b','nonnegative.12.c')]
    old_h=collect(source['residuals'][rid_h]['terms']); old_F=collect(source['residuals'][rid_F]['terms']); old_y=collect(source['residuals'][rid_y]['terms'])
    expected_h={():-1,(0,):1,(328,328):-1,(329,329):-1,(330,):-1,(330,330):-1}
    expected_F={(3,):1,(334,334):-1,(335,335):-1,(336,):-1,(336,336):-1}
    expected_y={():-1,(2,):1,(3,):-1,(343,343):-1,(344,344):-1,(345,):-1,(345,345):-1}
    if (old_h,old_F,old_y)!=(expected_h,expected_F,expected_y): raise ValueError('Source guards changed')
    for i,row in enumerate(source['residuals']):
        if i not in (rid_h,rid_y) and any(v in removed for _,m in row['terms'] for v in m):
            raise ValueError('Guard auxiliary occurs outside its private row')
    # Centered t0 coordinate is h=t0_old+1.  Hence t=h+15 and h=1+s^2.
    new_h={():-1,(0,):1,(328,328):-1}
    # F>=1 at the same three-square/triangular cost.
    new_F=dict(old_F); new_F[()]=-1
    # y = V^2 + 3F - 1.  Old r0 = y-F-1 = V^2+2F-2 >= 0.
    # This has the same support as the F>=2/coefficient-2 choice and a
    # three-unit smaller maximum coefficient after collecting the quartic.
    new_y={():1,(2,):1,(3,):-3,(6,6):-1}
    changes={rid_h:new_h,rid_F:new_F,rid_y:new_y}
    retained=[i for i in range(517) if i not in removed]
    remap={v:i for i,v in enumerate(retained)}
    out=copy.deepcopy(source)
    for key in ('metrics','elimination'): out.pop(key,None)
    out['schema']='finite_quadratic_residuals_v1'
    out['variant']='cofinal_horizon_and_deterministic_beta_modulus_integer512'
    out['variables']=[source['variables'][i] for i in retained]
    out['residuals']=[{'label':('cofinal.horizon_square' if i==rid_h else 'cofinal.factorial_positive' if i==rid_F else 'cofinal.beta_modulus' if i==rid_y else row['label']),
                       'terms':[[c,[remap[v] for v in m]] for m,c in sorted(changes.get(i,collect(row['terms'])).items())]}
                       for i,row in enumerate(source['residuals'])]
    polynomial=expand(out)
    metrics={'variables':512,'quadratic_rows':310,'exact_degree':max(len(m) for c,m in polynomial['terms']),
             'expanded_monomials':len(polynomial['terms']),
             'max_abs_expanded_coefficient':max(abs(c) for c,m in polynomial['terms']),
             'max_abs_row_coefficient':max(abs(c) for r in out['residuals'] for c,m in r['terms']),
             'variable_kinds':dict(Counter(v['kind'] for v in out['variables']))}
    out['metrics']=metrics
    certificate={'schema':'cofinal_specialization_integer512_v1',
      'source_sha256':digest(encoded(source)),'output_sha256':digest(encoded(out)),
      'source_variables':517,'output_variables':512,'source_rows':310,'output_rows':310,
      'removed_old_coordinates':removed,'retained_old_coordinates':retained,
      'ports_before_remapping':ports,
      'changes':[{'row':i,'old':source['residuals'][i],'new_terms_before_remapping':terms(p)} for i,p in sorted(changes.items())],
      'soundness':'New source forces F>=1, old t0=s^2>=0, and old r0=V^2+2F-2>=0. Restore the private Legendre auxiliaries existentially.',
      'completeness':'Choose a cofinal padded proof horizon t=16+s^2; F=t!; V=(Ft^2+1)^t; choose y=V^2+3F-1 before beta CRT. Every accumulator is <=V^2<y and F divides y.',
      'pointwise_bijection_claimed':False,'finite_checks_prove_consistency':False}
    return out,polynomial,certificate,metrics

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--source',type=Path,default=SOURCE);ap.add_argument('--output',type=Path,default=BASE/'regenerated');args=ap.parse_args()
    source=json.loads(args.source.read_text()); out,polynomial,certificate,metrics=build(source)
    args.output.mkdir(parents=True,exist_ok=True)
    for name,obj in [('source517.json',source),('equation512.json',out),('polynomial512.json',polynomial),('specialization_certificate.json',certificate),('metrics512.json',metrics)]:
        (args.output/name).write_bytes(encoded(obj))
    print(json.dumps(metrics,sort_keys=True))

if __name__=='__main__':main()
