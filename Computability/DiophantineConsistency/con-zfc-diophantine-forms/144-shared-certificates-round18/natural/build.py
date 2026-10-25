#!/usr/bin/env python3
"""Pool low-digit budgets in the fixed Round17 natural source, then contract."""
from pathlib import Path
from copy import deepcopy
import argparse, hashlib, json, sys
sys.dont_write_bytecode=True
HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE/'code'))
import contract as pc
import check

def read(p): return json.loads(p.read_text())
def write(p,o):
    p.parent.mkdir(parents=True,exist_ok=True)
    p.write_text(json.dumps(o,sort_keys=True,separators=(',',':'))+'\n')
def digest(o):return hashlib.sha256(pc.canonical(o)).hexdigest()

def transform(strategy='three_with_digit'):
    old=read(HERE/'source/equation.json'); source=deepcopy(old)
    names={v['name']:i for i,v in enumerate(old['variables'])}
    def v(s):return names[s]
    small=['choose0','crt.range.index']
    big=['crt.range.'+s for s in ['a','b','c','d','derived_label_sum']]
    den={'t0':v('pow3.output'),'t':v('mul.422'),'y':v('pow4.output'),'x':v('pow5.output')}
    groups=[('t',small+big),('y',['crt.range.S','crt.range.Sp']),('x',['crt.range.u','crt.range.vq'])]
    if strategy=='four':groups=[('t0',small),('t',big)]+groups[1:]
    keep={}; removed=set(); records=[]
    for label,req in groups:
        slack=v(req[0]+'.modular_rslack')
        source['variables'][slack]['name']='pooled_digits.'+label+'.slack'
        terms=[(1,[den[label]]),(-1,[slack]),(-1,[])]
        for name in req:
            r=v(name+'.modular_remainder')
            terms.append((-1,[v('pow2.output'),r]) if label=='t' and name in small else (-1,[r]))
            removed.add(name+'.remainder_bound')
        if strategy=='three_with_digit' and label=='t':
            terms.append((-1,[v('choose0.output'),den['t0']]))
            removed.add('choose0.digit_bound')
        row={'label':'pooled_digits.'+label,'terms':pc.dump(pc.loadpoly(terms))}
        keep[req[0]+'.remainder_bound']=row
        records.append({'label':label,'requests':req,'slack_original_index':slack,'denominator_original_index':den[label]})
    source['residuals']=[keep.get(r['label'],r) for r in source['residuals'] if r['label'] not in removed or r['label'] in keep]
    used=sorted({i for r in source['residuals'] for c,m in r['terms'] for i in m}); rename={j:i for i,j in enumerate(used)}
    source['variables']=[source['variables'][i] for i in used]
    for r in source['residuals']:r['terms']=[[c,[rename[i] for i in m]] for c,m in r['terms']]
    source['variant']='round18_self_radix_'+strategy
    source['metrics'],poly=pc.metrics_and_polynomial(source)
    cert={'schema':'self_radix_pooled_digits_v1','parent_sha256':digest(old),'source_sha256':digest(source),'strategy':strategy,'groups':records,'retained_parent_indices':used,'removed_row_labels':sorted(removed),'replacement_rows':keep}
    return source,poly,cert

def build(out,strategy,cap):
    source,poly,cert=transform(strategy)
    target,elim,expanded=pc.contract(source,support_cap=cap)
    result,independent=check.verify(source,target,elim)
    if expanded['terms']!=independent:raise ValueError('Expansion disagreement')
    for name,o in [('source/equation.json',source),('source/expanded_polynomial.json',poly),('source/transformation.json',cert),('natural/equation.json',target),('natural/elimination_certificate.json',elim),('natural/expanded_polynomial.json',expanded),('VERIFICATION.json',result)]:write(out/name,o)
    return result

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--output',type=Path,required=True);p.add_argument('--strategy',choices=['four','three','three_with_digit'],default='three_with_digit');p.add_argument('--cap',type=int,default=48)
    a=p.parse_args();print(json.dumps(build(a.output,a.strategy,a.cap),indent=2))
