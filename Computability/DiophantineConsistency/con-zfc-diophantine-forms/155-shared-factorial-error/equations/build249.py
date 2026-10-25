#!/usr/bin/env python3
"""Compose normalized remainders, odd-square q, and deterministic Pell center.
The entire squared orientation pool is preserved, so the q bootstrap proof
does not acquire the selected-orientation dependency of the sibling archive.
"""
from pathlib import Path
import copy,hashlib,json,sys
ROOT=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT/'parent252/code'))
import terminal_elimination as E
import translate_coordinates as T
def add(*ps):
    d={}
    for p in ps:
        for m,c in p.items():d[m]=d.get(m,0)+c
    return {m:c for m,c in d.items() if c}
def neg(p):return {m:-c for m,c in p.items()}
def V(i):return {(i,):1}
def main():
    old=json.loads((ROOT/'parent252/data/factored_source.json').read_text());s=copy.deepcopy(old)
    meta=json.loads((ROOT/'parent252/upstream/parent/transform_certificate.json').read_text())
    n={v['name']:i for i,v in enumerate(s['variables'])};A=n['shared.A'];H=n['cap.H'];f=n['cap.f'];R=n['cap.R'];C=meta['cap_variables']['Y'];h=n['cap.h']
    replace={
      'cap.comparison_constructor':('cap.deterministic_factor',add(V(f),neg(V(H)),E.multiply(V(A),V(H)))),
      'cap.index_residue':('cap.index_residue',add(V(R),neg(E.normalize(meta['anchor_index'])),neg(E.multiply(V(C),V(h)))))
    }
    removed=['choose0.digit_bound','domain_guard.2'];changes=[];rows=[]
    for i,r in enumerate(s['residuals']):
        if r['label'] in removed:
            changes.append({'row':i,'before':r,'after':None});continue
        if r['label'] in replace:
            label,p=replace[r['label']];nr={'label':label,'terms':E.as_terms(p)};changes.append({'row':i,'before':r,'after':nr});rows.append(nr)
        else:rows.append(r)
    if len(changes)!=4:raise ValueError('Unexpected row delta')
    z=len(s['variables']);s['variables'].append({'name':'radix.odd_square_root_half','kind':'signed_witness'})
    rows.append({'label':'radix.odd_square','terms':E.as_terms({(n['pow2.output'],):1,(z,z):-4,(z,):-4,():-1})})
    s['residuals']=rows;s['variant']+=':odd_square_deterministic_center'
    p,pc,metrics=E.optimize(s,max_support=16);checked=E.verify(s,p,pc)
    oldp=json.loads((ROOT/'parent252/data/projected.json').read_text())
    oldt=json.loads((ROOT/'parent252/equation/translation_certificate.json').read_text())
    byname={oldp['variables'][i]['name']:v for i,v in oldt['shifts']}
    shifts={i:byname[v['name']] for i,v in enumerate(p['variables']) if v['name'] in byname}
    out=T.translate(p,shifts);poly=E.expand(out)
    m={'variables':len(out['variables']),'rows':len(out['residuals']),'degree':max(len(mm) for c,mm in poly['terms']),'monomials':len(poly['terms']),'height':max(abs(c) for c,mm in poly['terms']),'row_height':max(abs(c) for r in out['residuals'] for c,mm in r['terms'])}
    target=ROOT/'equation249';target.mkdir(exist_ok=True)
    data={'source.json':s,'source_delta.json':{'changes':changes,'appended_row':rows[-1],'appended_variable':z,'preserved_full_squared_orientation':True},'projected.json':p,'projection_certificate.json':pc,'PROJECTION_CHECK.json':checked,'translation_certificate.json':{'shifts':[[i,v] for i,v in shifts.items()],'convention':'old=new+shift'},'equation.json':out,'expanded_polynomial.json':poly,'METRICS.json':m}
    for fn,obj in data.items():(target/fn).write_bytes(E.canonical_bytes(obj))
    print(json.dumps(m,sort_keys=True))
if __name__=='__main__':main()
