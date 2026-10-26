#!/usr/bin/env python3
"""Rebuild frozen positive10 graphs and bind the entire new Start-only tuple."""
from pathlib import Path
from collections import Counter
import argparse, hashlib, json
ROOT=Path(__file__).resolve().parent
SPECS={
 'free_plain':('inherited/strict/equation_83_degree312.json',82,240),
 'scaled_inverse':('inherited/inverse_bV.json',85,232),
 'free_inverse':('inherited/strict/equation_89_degree278.json',87,214),
}
def construct(mode):
    rel,ops,degree=SPECS[mode]; path=ROOT/rel
    g=json.loads(path.read_text()); rows=[]
    for name,op,a,b in g['source']:
        if name=='Tshift':continue
        if b=='Tshift':b='T'
        if name=='Fsqr':name,op,a,b='trace_f','+','DpI2','Df'
        if a=='Fsqr':a='trace_f'
        if b=='Fsqr':b='trace_f'
        if mode=='free_inverse':
            if name in ['Rp1sq','Rp1sqm4','rank_cubic','v_rank_cubic']:continue
            if name=='q4s':
                rows.extend([['ksq','*','k','k'],['ksqm4','-','ksq',4],['inverse_cubic','*','V0k','ksqm4']])
            if name=='eclear':b='inverse_cubic'
        rows.append([name,op,a,b])
    if len(rows)!=ops:raise ValueError((mode,len(rows),ops))
    name=f'positive10_degree{degree}_ops{ops}'
    g.update(name=name,mode=mode,source=rows,operations=ops,
      operation_breakdown=dict(sorted(Counter(r[1] for r in rows).items())),
      exact_degree=degree,proof='PROOF.md',
      parent={'path':rel,'sha256':hashlib.sha256(path.read_bytes()).hexdigest()},
      generation='Explicit strong trace; no auxiliary positive shift; free quotient or inverse-Lucas correction as stated.',
      status='Ordinary proof at the retained native/refutation calibration; not a new formal-kernel object.')
    certificate=json.loads((ROOT/'native4127/start_only_certificate.json').read_text())
    g['coefficient_binding']={
      'path':'native4127/start_only_ports/',
      'tuple':'WHOLE Start-only complemented943/radix47 native cell4127; MF source shifted exactly once',
      'byte_order':'big',
      'certificate':'native4127/start_only_certificate.json',
      'certificate_sha256':hashlib.sha256((ROOT/'native4127/start_only_certificate.json').read_bytes()).hexdigest(),
      'ports':{n:{**v,'file':n+'.bin'} for n,v in certificate['ports'].items()},
      'raw_bytes':certificate['raw_bytes']}
    g['generation']='Unchanged round21 free-port graph; all four coefficients coherently replaced by Start-only4127. See PROOF.md for complete native bridge.'
    g['name']='start4127_'+g['name']
    return g

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--check',action='store_true');a=ap.parse_args();metrics=[]
    for mode in SPECS:
        g=construct(mode);fn=g['name']+'.json';s=json.dumps(g,indent=2)+'\n'
        if a.check:
            if (ROOT/fn).read_text()!=s:raise ValueError('rebuild mismatch '+fn)
        else:(ROOT/fn).write_text(s)
        metrics.append({k:g[k] for k in ['name','mode','domain','operations','operation_breakdown','exact_degree']}|{'variables':len(g['witnesses'])})
    s=json.dumps(metrics,indent=2)+'\n'
    if a.check:
        if (ROOT/'METRICS.json').read_text()!=s:raise ValueError('metrics mismatch')
    else:(ROOT/'METRICS.json').write_text(s)
    print(s,end='')
if __name__=='__main__':main()
