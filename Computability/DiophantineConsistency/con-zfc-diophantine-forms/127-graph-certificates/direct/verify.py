#!/usr/bin/env python3
"""Independent finite checks for the combined C222 arithmetic source.

No equation producer or optimizer is imported. A successful result verifies
literal bindings and finite algebra, not consistency or the inherited logic.
"""
from pathlib import Path
from copy import deepcopy
from hashlib import sha256
import argparse, json
import check_capped_modular as semantic
from check_affine_export import verify as affine_verify
from check_contraction import verify as contraction_verify, canonical

HERE=Path(__file__).resolve().parent

def need(ok,msg):
    if not ok:raise ValueError(msg)

def load(p):return json.loads(p.read_text())

def run():
    src=HERE/'equation240/raw'
    meta=load(src/'raw_audit_input.json'); raw=load(src/'equation.json')
    parent=load(HERE/'inherited/modular_parent_metadata.json')
    label='modular.common_root'
    cut=next(i for i,r in enumerate(meta['rows']) if r['label']==label)+1
    oldcut=next(i for i,r in enumerate(parent['rows']) if r['label']==label)+1
    need(meta['rows'][:cut]==parent['rows'][:oldcut],'inherited source prefix changed')
    live={v for r in meta['rows'][:cut] for c,m in r['terms'] for v in m}
    count=max(live)+1
    need(meta['variables'][:count]==parent['variables'][:count],'inherited prefix variables changed')
    for key in ('powers','factorials','binomials','ranges','radix','product','amplification',
                'scale','lower_A','denominator_derivations','local_majorant','syntax','local_names',
                'wire_eliminated_source_sha256'):
        need(meta[key]==parent[key],'inherited semantic metadata changed: '+key)
    need(meta['factorials'][0]['binomial']==meta['product']['product'],
         'factorial and reciprocal product are not the same output')
    need(len(meta['powers'])==6 and len(meta['seeds'])==15 and len(meta['modular_requests'])==11,
         'wrong arithmetic call counts')
    sem=semantic.check(src/'raw_audit_input.json')
    sem['corruptions']=semantic.corruption_controls(src/'raw_audit_input.json')
    affine,certificate=affine_verify(meta,raw)
    endpoints={}
    for name in ('equation240','equation239'):
        p=HERE/name/'natural'
        target=load(p/'equation.json'); cert=load(p/'elimination_certificate.json')
        expected=load(p/'VERIFICATION.json'); full=load(p/'expanded_polynomial.json')
        receipt,terms=contraction_verify(raw,target,cert)
        need(receipt==expected,'contraction receipt differs: '+name)
        need(terms==full['terms'],'complete polynomial coefficients differ: '+name)
        n=len(target['variables'])
        used={v for r in target['residuals'] for c,m in r['terms'] for v in m}
        need(used==set(range(n)),'unused endpoint variable')
        need(all(type(c) is int and c and len(m)<=2 and m==sorted(m)
                 and all(type(v) is int and 0<=v<n for v in m)
                 for r in target['residuals'] for c,m in r['terms']),
             'malformed endpoint monomial')
        bad=deepcopy(target);bad['residuals'][0]['terms'][0][0]+=1
        badcert=deepcopy(cert);badcert['target_equation_sha256']=sha256(canonical(bad)).hexdigest()
        try:contraction_verify(raw,bad,badcert)
        except ValueError:pass
        else:raise ValueError('changed target coefficient accepted')
        badcert=deepcopy(cert);badcert['steps'][0]['restoration'][0][0]+=1
        try:contraction_verify(raw,target,badcert)
        except ValueError:pass
        else:raise ValueError('changed restoration accepted')
        endpoints[name]={'metrics':receipt,'all_variables_live':True,
            'equation_sha256':sha256((p/'equation.json').read_bytes()).hexdigest(),
            'polynomial_sha256':sha256((p/'expanded_polynomial.json').read_bytes()).hexdigest(),
            'algebraic_corruptions_rejected':2}
    return {'status':'PASS','inherited_prefix_rows':cut,'inherited_prefix_variables':count,
        'source_prefix_exactly_preserved':True,'semantic':sem,'affine':affine,
        'endpoints':endpoints,'scope':'Finite source bindings, full natural restoration, every quartic coefficient; no test of consistency.'}

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--output',type=Path);a=p.parse_args()
    result=run();body=json.dumps(result,indent=2,sort_keys=True)+'\n'
    if a.output:a.output.write_text(body)
    print(body,end='')
