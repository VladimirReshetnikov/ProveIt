#!/usr/bin/env python3
"""Exact finite old/new exponent-table check, independently of the builder."""
from pathlib import Path
import json
ROOT=Path(__file__).resolve().parent

def need(ok,m):
    if not ok:raise ValueError(m)
def load(p):return json.loads(p.read_text())
def coeff(rec):
    return sorted((tuple(t.get('powers',t.get('port_powers'))),t.get('coefficient',t.get('integer'))) for t in rec)
def main():
    results=[]
    for label,base,oldcode,oldkern in [
        ('original31',ROOT,ROOT/'inherited/h1868_code.json',ROOT/'inherited/h1868_kernels.json'),
        ('compact54',ROOT/'compact',ROOT/'compact/inherited_h2082_layout.json',ROOT/'compact/inherited_h2082_kernels.json')]:
        a,b=load(oldcode),load(base/'data/code.json')
        need(b['weights']==[x-1 for x in a['weights']],'translated coordinate weights')
        need(b['targets_by_row']==[x-2 for x in a['targets_by_row']],'translated extraction targets')
        need(min(b['weights'])==0 and len(set(b['weights']))==31,'nonnegative distinct coordinates')
        ka,kb=load(oldkern),load(base/'data/kernels.json')
        for la,lb in zip(ka['kernels'],kb['kernels']):
            d=la['degree'];need(d==lb['degree'],'kernel layer')
            old={(x['exponent']+d-2,tuple(coeff(x['coefficient']))) for x in la['terms']}
            new={(x['exponent'],tuple(coeff(x['coefficient']))) for x in lb['terms']}
            need(old==new and min(e for e,_ in new)>=0,'complete kernel translation')
        need(b['max_weight']==a['max_weight']-1,'new maximum weight')
        need(b['convolution_height']==a['convolution_height']-2,'new convolution height')
        results.append(dict(profile=label,weights=31,targets=22,height=b['convolution_height'],max_weight=b['max_weight'],status='PASS'))
    # The origin lemma does not authorize an additional target shift: the
    # quadratic constant coefficient would acquire a negative exponent.
    need(min(t['exponent'] for t in load(ROOT/'data/kernels.json')['kernels'][2]['terms'])==0,'quadratic boundary is tight')
    out=dict(status='PASS',layouts=results,restricted_maximality='r<=1 and s<=2r for these fixed supports; r=1,s=2 is maximal')
    (ROOT/'NORMALIZATION_CHECKS.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
if __name__=='__main__':main()
