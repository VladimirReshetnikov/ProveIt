#!/usr/bin/env python3
"""Independently reconstruct every changed fixed-growth raw polynomial row."""
import argparse,hashlib,json
from pathlib import Path
from collections import defaultdict
from independent_polynomials import norm,mul,sub,need

HERE=Path(__file__).resolve().parent
PACKAGED=(HERE.parent/'stages').is_dir()
PARENT=(HERE.parent/'upstream/factorial_free/direct/factorial_free_affine/raw_source.json' if PACKAGED else HERE.parents[1]/'sources/incoming/ConZFC_Factorial_Free_Binomial_CRT_2026-10-25/ConZFC_Factorial_Free_Binomial_CRT_2026-10-25/direct/factorial_free_affine/raw_source.json')
NEW=HERE.parent/'stages/fixed_base/raw_source.json' if PACKAGED else HERE.parent/'alternative_encoding/fixed_base16_linear_B/raw_source.json'

def add(*ps):
    q=defaultdict(int)
    for p in ps:
        for m,c in p.items():q[m]+=c
    return {m:c for m,c in q.items() if c}
def scale(p,c):return {m:c*a for m,a in p.items() if c*a}
def var(i):return {(i,):1}
def const(c):return {():c} if c else {}

def main(parent=PARENT,source=NEW,output=None):
    old=json.loads(parent.read_text());new=json.loads(source.read_text())
    n={v['name']:i for i,v in enumerate(old['variables'])};v=lambda s:var(n[s])
    F=n['crt.growth_majorant_F'];R=n['mul.1'];B=n['choose0.output'];d=n['growth.power_base'];q=n['pow2.output'];z=n['radix.odd_square_root_half']
    t=add(v('t0'),const(16));x=v('x');y=v('y');s=v('beta.odd_square_multiplier')
    reps=[add(var(i),const(1)) for i in range(16,25)]
    req=[(const(16),t,var(R)),(var(B),x,v('pow1.output')),
         (v('self_radix.BH'),x,var(q)),(add(var(q),const(1)),add(var(R),t),v('pow3.output')),
         (var(q),t,v('pow4.output')),(add(var(q),const(1)),reps[0],v('pow5.output')),
         (var(q),add(t,const(1)),v('pow6.output'))]
    for k,j in [(7,1),(8,2),(9,3),(10,4)]:req.append((add(var(q),const(1)),reps[j],v(f'pow{k}.output')))
    req.append((var(q),add(y,const(1)),v('pow11.output')))
    for k,j in [(12,5),(13,6)]:req.append((add(var(q),const(1)),reps[j],v(f'pow{k}.output')))
    req.append((var(q),x,v('pow14.output')))
    for k,j in [(15,7),(16,8)]:req.append((add(var(q),const(1)),reps[j],v(f'pow{k}.output')))
    req.append((add(var(q),const(1)),add(v('add.380'),const(1)),v('pow17.output')))
    manifest=json.loads(source.with_name('mutation.json').read_text())
    need(len(manifest['requests'])==len(req),'power request manifest census')
    need(all(tuple(norm(item[key]) for key in ['base','exponent','output'])==triple for item,triple in zip(manifest['requests'],req)),'every power request port independently reconstructed')
    need(manifest['source_sha256']==hashlib.sha256(parent.read_bytes()).hexdigest(),'power request parent binding')
    atoms={tuple(sorted(p.items())):p for r in req for p in r}
    frame=add(v('shared.W'),const(-2),*(scale(mul(p,p),-1) for p in atoms.values()))
    actual=[];changed=[]
    for i,row in enumerate(old['residuals']):
        lab=row['label'];p=norm(row['terms'])
        if lab=='growth.base_definition':continue
        if i==0:
            need(p=={(F,F):-1,(R,):1},'old radius graph')
            p=add(var(F),scale(mul(var(R),var(B)),-1));lab='beta.RB'
        else:
            p=sub(p,F,var(R if lab=='pow0.power_congruence' else B));p=sub(p,d,const(16))
            if lab=='shared.frame_definition':p=frame
            elif lab=='self_radix.base_definition':p=add(p,scale(mul(var(B),t),-2),scale(var(F),-2))
            elif lab=='radix.odd_square':p=add(var(q),scale(var(z),-6),const(-3));lab='radix.progression'
            elif lab=='bootstrap.beta_base_square_product':p=add(y,scale(mul(var(F),s),-1));lab='bootstrap.beta_base_fixed_radius'
        target={'label':lab,'terms':[[c,list(m)] for m,c in sorted(p.items())]}
        if target!=row:changed.append(i)
        actual.append(target)
    need(actual==new['residuals'],'all raw residuals equal independent specification')
    need(all(len(m)<=2 for r in actual for c,m in r['terms']),'raw degree')
    expected_vars=[dict(v) for v in old['variables']]
    expected_vars[F].update(name='beta.RB',kind='gate');expected_vars[R].update(name='radius.R',kind='witness');expected_vars[z]['name']='radix.progression_parameter'
    need(expected_vars==new['variables'],'exact variable metadata')
    result={'status':'PASS','raw_rows':len(actual),'changed_rows':changed,'requests':len(req),'distinct_frame_atoms':len(atoms),
        'parent_sha256':hashlib.sha256(parent.read_bytes()).hexdigest(),'new_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),
        'scope':'Exact raw polynomial source, every request-manifest port and complete frame; new unbounded proof separately read and assessed.'}
    report=json.dumps(result,indent=2,sort_keys=True)+'\n'
    if output:output.parent.mkdir(parents=True,exist_ok=True);output.write_text(report)
    print(report,end='')

if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('--parent',type=Path,default=PARENT);ap.add_argument('--source',type=Path,default=NEW);ap.add_argument('--output',type=Path)
    a=ap.parse_args();main(a.parent,a.source,a.output)
