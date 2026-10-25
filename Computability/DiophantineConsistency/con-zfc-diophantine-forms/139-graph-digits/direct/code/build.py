#!/usr/bin/env python3
"""Build literal quartics by pooled digit budgets and a semantic Pell cap."""
from pathlib import Path
from copy import deepcopy
import importlib.util
import json
import hashlib
import argparse

ROOT=Path(__file__).resolve().parents[1]
def module(name,path):
    spec=importlib.util.spec_from_file_location(name,path)
    m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m);return m
pc=module('inherited_contractor',ROOT/'upstream/100-quartics407-888/code/psd_contract/contract.py')
check=module('inherited_contraction_checker',ROOT/'upstream/100-quartics407-888/code/psd_contract/check.py')
def read(p):return json.loads(p.read_text())
def write(p,o):p.parent.mkdir(parents=True,exist_ok=True);p.write_text(json.dumps(o,sort_keys=True,separators=(',',':'))+'\n')
def digest(o):return hashlib.sha256(json.dumps(o,sort_keys=True,separators=(',',':')).encode()).hexdigest()

def source_transform(fuse=True,strategy='three_with_digit'):
    original=read(ROOT/'upstream/129-semantic-pell-anchor/equations/source/equation.json')
    source=deepcopy(original)
    names={x['name']:i for i,x in enumerate(source['variables'])}
    def v(n):return names[n]
    def row(label,terms):return {'label':label,'terms':pc.dump(pc.loadpoly(terms))}
    def rem(n):return v(n+'.modular_remainder')
    qt=v('pow2.output');dt=v('pow3.output');dt1=v('mul.426');dy=v('pow4.output');dx=v('pow5.output')
    os=v('choose0.modular_oslack')
    small=['choose0','crt.range.index']
    large=['crt.range.'+s for s in ('a','b','c','d','derived_label_sum')]
    groups=[('t',small+large,v('choose0.modular_rslack')),
            ('y',['crt.range.S','crt.range.Sp'],v('crt.range.S.modular_rslack')),
            ('x',['crt.range.u','crt.range.vq'],v('crt.range.u.modular_rslack'))]
    if strategy.startswith('four'):groups=[('t0',small,v('choose0.modular_rslack')),('t',large,v('crt.range.a.modular_rslack'))]+groups[1:]
    replacement={}
    for label,requests,slack in groups:
        terms=[(1,[{'t0':dt,'t':dt1,'y':dy,'x':dx}[label]]),(-1,[slack]),(-1,[])]
        for name in requests:
            terms.append((-1,[qt,rem(name)]) if name in small and not strategy.startswith('four') else (-1,[rem(name)]))
        if label=='t' and strategy.endswith('with_digit'):terms.extend([(-1,[v('reciprocal.Bminus2'),dt]),(-2,[dt])])
        replacement[requests[0]+'.remainder_bound']=row('pooled_digits.'+label,terms)
        source['variables'][slack]['name']='pooled_digits.'+label+'.slack'
    deleted=[];newrows=[]
    labels={name+'.remainder_bound' for _,g,_ in groups for name in g}
    if strategy.endswith('with_digit'):labels.add('choose0.digit_bound')
    for i,r in enumerate(source['residuals']):
        if r['label'] in labels:
            if r['label'] in replacement:newrows.append(replacement[r['label']])
            else:deleted.append(i)
        else:newrows.append(r)
    source['residuals']=newrows
    fusion=None
    if fuse:
        # These five rows are the private nonnegative sum gate chain and final
        # aggregate inequality in the pinned source. No other row uses its slack.
        removed_indices=set(range(331,336))
        expected=[r for r in original['residuals'] if any(i in removed_indices for _,m in r['terms'] for i in m)]
        if len(expected)!=5:raise ValueError('unexpected aggregate gate closure')
        newrows=[]
        for r in source['residuals']:
            if r in expected:continue
            if r['label']=='index_cap.squared_index_errors':
                quotient=v('index_cap.error_square_quotient')
                terms=[((-c if quotient in m else c),m) for c,m in r['terms']]
                H=[(7,[]),(4,[v('crt.encoded.b')]),(2,[v('mul.42')]),(1,[v('add.409')])]
                terms+=H+[(-1,[v('index_cap.Y')])]
                r=row('index_cap.fused_bound_errors',terms)
                fusion={'H':pc.dump(pc.loadpoly(H)),'Y':v('index_cap.Y'),'quotient':quotient,'removed_rows':expected}
                source['variables'][quotient]['name']='index_cap.fused_quotient'
            newrows.append(r)
        source['residuals']=newrows
    used=sorted({i for r in source['residuals'] for _,m in r['terms'] for i in m})
    rename={v:i for i,v in enumerate(used)}
    source['variables']=[source['variables'][i] for i in used]
    for r in source['residuals']:r['terms']=[[c,[rename[i] for i in m]] for c,m in r['terms']]
    source['variant']=strategy+'_pooled_digit_budgets'+('_semantic_fused_cap' if fuse else '')
    source['metrics'],expanded=pc.metrics_and_polynomial(source)
    cert={'schema':'pooled_digit_and_semantic_cap_transformation_v1','parent_canonical_sha256':digest(original),
          'source_canonical_sha256':digest(source),'groups':groups,'digit_bound_deleted':strategy.endswith('with_digit'),
          'cap_fusion':fusion,'retained_parent_coordinates':used,'deleted_parent_rows':deleted,
          'parent_file':'upstream/129-semantic-pell-anchor/equations/source/equation.json'}
    return source,expanded,cert

def build(output,cap=64,fuse=True,strategy='three_with_digit'):
    source,expanded,transform=source_transform(fuse,strategy)
    target,certificate,polynomial=pc.contract(source,support_cap=cap)
    receipt,independent=check.verify(source,target,certificate)
    if polynomial['terms']!=independent:raise ValueError('independent polynomial mismatch')
    for p,o in [('source/equation.json',source),('source/expanded_polynomial.json',expanded),
                ('source/transform.json',transform),('natural/equation.json',target),
                ('natural/expanded_polynomial.json',polynomial),('natural/elimination_certificate.json',certificate),
                ('VERIFICATION.json',receipt)]:write(output/p,o)
    summary={'cap':cap,'fusion':fuse,'strategy':strategy,'source':source['metrics'],'target':target['metrics']}
    write(output/'SUMMARY.json',summary);return summary

def build_all(output):
    source,expanded,transform=source_transform(True,'four')
    for p,o in [('equations/source/equation.json',source),('equations/source/expanded_polynomial.json',expanded),('equations/source/transform.json',transform)]:write(output/p,o)
    summary={}
    for n,cap in [(226,64),(227,32)]:
        target,certificate,polynomial=pc.contract(source,support_cap=cap)
        receipt,independent=check.verify(source,target,certificate)
        if polynomial['terms']!=independent:raise ValueError('independent coefficient mismatch')
        if len(target['variables'])!=n:raise ValueError('wrong dimension')
        folder=output/'equations'/('natural'+str(n))
        for p,o in [('equation.json',target),('elimination_certificate.json',certificate),('expanded_polynomial.json',polynomial),('VERIFICATION.json',receipt)]:write(folder/p,o)
        summary[str(n)]=target['metrics']
    write(output/'RESULTS.json',summary)
    write(output/'equations/integer678.json',{'schema':'literal_polynomial_substitution_v1','domain':'unrestricted integers','variables':678,'exact_degree':8,'source_equation':'natural226/equation.json','substitutions':[[[1,[3*i,3*i]],[1,[3*i+1,3*i+1]],[1,[3*i+2,3*i+2]],[1,[3*i+2]]] for i in range(226)],'polynomial':'substitute listed g_i into every residual of source; sum their squares'})
    return summary

if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('--output',type=Path,default=ROOT);a=ap.parse_args()
    print(json.dumps(build_all(a.output),indent=2))
