#!/usr/bin/env python3
"""Minimize explicit domain guards by certified nonnegative inference.

The frozen synchronized natural522 equation is unchanged. The optional
second stage applies the received integer monic projection algorithm.
"""
from pathlib import Path
from collections import defaultdict,Counter
from hashlib import sha256
import argparse,copy,json
import terminal_elimination as projection

HERE=Path(__file__).resolve().parent

def need(ok,why):
    if not ok:raise ValueError(why)

def implications(parent):
    rules=[]
    for ri,row in enumerate(parent['residuals']):
        for c,m in row['terms']:
            if len(m)!=1 or not c:continue
            x=m[0];other=[(a,n)for a,n in row['terms']if n!=[x]]
            if any(x in n or -a*c<0 for a,n in other):continue
            odd={i for a,n in other for i,multiplicity in Counter(n).items()if multiplicity%2}
            rules.append(dict(target=x,row=ri,dependencies=sorted(odd),positive_multiplier=c*c,
                              scaled_definition=[[-a*c,n]for a,n in other]))
    return rules

def build_guarded(parent):
    rules=implications(parent);targets={r['target']for r in rules}
    # Metadata guides optimization only. The independent certificate proves
    # every coordinate natural, without trusting its alleged kind.
    semantic={i for i,v in enumerate(parent['variables'])if v['kind']!='gate'}
    guards=semantic-targets;known=set(guards);proof=[];n=len(parent['variables'])
    while len(known)<n:
        changed=True
        while changed:
            changed=False
            for r in rules:
                if r['target']not in known and set(r['dependencies'])<=known:
                    known.add(r['target']);proof.append(r);changed=True
        if len(known)==n:break
        candidates=sorted(semantic-known)
        need(candidates,'nonnegative inference has an ungrounded gate')
        guards.add(candidates[0]);known.add(candidates[0])
    eq=copy.deepcopy(parent);eq['domain']='unrestricted integers';eq['variant']='synchronized-inferred-guards'
    eq.pop('metrics',None);bindings=[]
    for x in sorted(guards):
        a,b,c=range(len(eq['variables']),len(eq['variables'])+3)
        for suffix in ['a','b','c']:eq['variables'].append(dict(name=f'nonnegativity.{x}.{suffix}',kind='integer_guard'))
        row=dict(label=f'nonnegativity.{x}',terms=[[1,[x]],[-1,[a,a]],[-1,[b,b]],[-1,[c]],[-1,[c,c]]])
        bindings.append(dict(input=x,auxiliaries=[a,b,c],row=len(eq['residuals'])));eq['residuals'].append(row)
    eq['metrics']=measure(eq)
    cert=dict(schema='nonnegative_inference_domain_conversion_v1',natural_parent_sha256=sha256(projection.canonical_bytes(parent)).hexdigest(),
              original_variables=n,original_rows=len(parent['residuals']),guards=bindings,inference=proof,
              integer_equation_sha256=sha256(projection.canonical_bytes(eq)).hexdigest())
    return eq,cert

def measure(eq):
    p=projection.expand(eq)
    return dict(variables=len(eq['variables']),quadratic_rows=len(eq['residuals']),exact_degree=max(len(m)for c,m in p['terms']),
                expanded_monomials=len(p['terms']),max_abs_expanded_coefficient=max(abs(c)for c,m in p['terms']),
                max_abs_row_coefficient=max(abs(c)for r in eq['residuals']for c,m in r['terms']))

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--max-support',type=int,default=16);ap.add_argument('--check',action='store_true');args=ap.parse_args()
    pins=json.loads((HERE/'SOURCE_PINS.json').read_text())['files']
    for f,h in pins.items():need(sha256((HERE/f).read_bytes()).hexdigest()==h,'pinned input '+f)
    parent=json.loads((HERE/'source/parent_natural.json').read_text());eq,cert=build_guarded(parent)
    final,projection_cert,metrics=projection.optimize(eq,max_support=args.max_support)
    projection.verify(eq,final,projection_cert)
    files={
      'input/equation.json':eq,'input/domain_conversion_certificate.json':cert,
      'input/expanded_polynomial.json':projection.expand(eq),
      'output/equation.json':final,'output/terminal_elimination_certificate.json':projection_cert,
      'output/expanded_polynomial.json':projection.expand(final),
      'BUILD.json':dict(status='PASS',guarded=eq['metrics'],projected=metrics,natural_guards=len(cert['guards']),natural_inferences=len(cert['inference']))}
    for name,data in files.items():
        path=HERE/name;raw=projection.canonical_bytes(data)
        if args.check:need(path.read_bytes()==raw,'deterministic rebuild '+name)
        else:path.parent.mkdir(parents=True,exist_ok=True);path.write_bytes(raw)
    print(json.dumps(files['BUILD.json'],indent=2,sort_keys=True))

if __name__=='__main__':main()
