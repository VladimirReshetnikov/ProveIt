#!/usr/bin/env python3
"""Independently bind semantic raw metadata to the exported quadratic system.

No constructor/exporter module is imported. Every removed coordinate is
restored by a nonnegative affine integer polynomial. The exact substitution
is replayed in every remaining row and compared with the actual raw artifact.
"""
import argparse,hashlib,json
from pathlib import Path

def require(ok,msg):
    if not ok:raise ValueError(msg)

def canonical(x):return json.dumps(x,sort_keys=True,separators=(',',':')).encode()

def load(terms):
    p={}
    for c,m in terms:
        require(type(c) is int,'coefficient type')
        m=tuple(sorted(m));p[m]=p.get(m,0)+c
    return {m:c for m,c in p.items() if c}

def dump(p):return [[c,list(m)] for m,c in sorted(p.items()) if c]

def multiply(p,q):
    d={}
    for m,c in p.items():
        for n,a in q.items():
            v=tuple(sorted(m+n));d[v]=d.get(v,0)+c*a
    return {m:c for m,c in d.items() if c}

def substitute(p,var,definition):
    out={}
    for m,c in p.items():
        term={():c}
        for v in m:term=multiply(term,definition if v==var else {(v,):1})
        for n,a in term.items():out[n]=out.get(n,0)+a
    return {m:c for m,c in out.items() if c}

def verify(meta,raw):
    require(raw['domain']=='nonnegative integers','wrong target domain')
    variables=meta['variables'];original=meta['rows'];gates={int(i):j for i,j in meta['gates'].items()}
    require(all(original[j].get('gate')==i for i,j in gates.items()),'gate map disagrees with rows')
    rows={i:load(r['terms']) for i,r in enumerate(original)}
    require(all(len(m)<=2 for p in rows.values() for m in p),'nonquadratic metadata')
    active=set(range(len(variables)));steps=[]
    for v in range(len(variables)):
        j=gates.get(v)
        if j is None or j not in rows:continue
        p=rows[j]
        if any(len(m)>1 for m in p):continue
        require(p.get((v,))==1,'nonmonic affine definition')
        definition={m:-c for m,c in p.items() if m!=(v,)}
        require(all(v not in m and all(u<v for u in m) for m in definition),'nontriangular affine definition')
        require(all(c>=0 for c in definition.values()),'negative affine restoration')
        if len(definition)>4:continue
        steps.append({'row_original_index':j,'variable_original_index':v,
                      'variable_name':variables[v]['name'],'restoration':dump(definition)})
        del rows[j];active.remove(v)
        for rid,q in list(rows.items()):
            if any(v in m for m in q):rows[rid]=substitute(q,v,definition)
        require(all(len(m)<=2 for p in rows.values() for m in p),'affine substitution raised degree')
    rows={i:p for i,p in rows.items() if p}
    used={v for p in rows.values() for m in p for v in m}
    # The selected capped construction has no unreachable retained gates.
    # Reject instead of silently making a more general restoration claim.
    require(used==active,'unreviewed unused coordinate or gate')
    ordered=sorted(used);renaming={v:i for i,v in enumerate(ordered)}
    require([variables[i] for i in ordered]==raw['variables'],'exported variable list differs')
    expected=[]
    for j,p in sorted(rows.items()):
        q={tuple(renaming[v] for v in m):c for m,c in p.items()}
        expected.append({'label':original[j]['label'],'terms':dump(q)})
    require(expected==raw['residuals'],'exported residuals differ from replayed substitutions')
    require(len(steps)==raw['metrics']['affine_gate_variables_eliminated'],'elimination count')
    certificate={'schema':'nonnegative_affine_export_replay_v1','metadata_sha256':hashlib.sha256(canonical(meta)).hexdigest(),
                 'raw_equation_sha256':hashlib.sha256(canonical(raw)).hexdigest(),'steps':steps,
                 'retained_original_indices_in_target_order':ordered,
                 'surviving_source_rows_in_target_order':list(sorted(rows)),
                 'inverse':'Restore eliminated variables in reverse step order by their nonnegative affine integer polynomials.'}
    receipt={'verified':True,'original_variables':len(variables),'original_rows':len(original),
             'nonnegative_affine_restorations':len(steps),'retained_variables':len(ordered),
             'retained_rows':len(expected),'all_rows_compared':True,'unused_coordinates':0,
             'independence':'No producer, optimizer, or exporter imported.'}
    return receipt,certificate

def main():
    p=argparse.ArgumentParser();p.add_argument('metadata',type=Path);p.add_argument('raw_equation',type=Path)
    p.add_argument('--output',type=Path);p.add_argument('--certificate',type=Path)
    a=p.parse_args();meta=json.loads(a.metadata.read_text());raw=json.loads(a.raw_equation.read_text())
    result,certificate=verify(meta,raw)
    mutated=json.loads(json.dumps(raw));mutated['residuals'][0]['terms'][0][0]+=1
    try:verify(meta,mutated)
    except ValueError:result['changed_raw_coefficient_rejected']=True
    else:raise ValueError('changed exported coefficient accepted')
    mutated=json.loads(json.dumps(meta))
    affine=certificate['steps'][0]['row_original_index']
    mutated['rows'][affine]['terms'][0][0]-=1
    try:verify(mutated,raw)
    except ValueError:result['changed_affine_definition_rejected']=True
    else:raise ValueError('changed metadata definition accepted')
    if a.output:a.output.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
    if a.certificate:a.certificate.write_text(json.dumps(certificate,sort_keys=True,separators=(',',':'))+'\n')
    print(json.dumps(result,indent=2,sort_keys=True))

if __name__=='__main__':main()
