#!/usr/bin/env python3
"""Build the signed-front Diophantine quartics from a retained literal source.

This is a finite producer. The unbounded arithmetic proof is separate.
Only the Python standard library and the included predecessor are required.
"""
from pathlib import Path
import argparse,copy,hashlib,json,sys

ROOT=Path(__file__).resolve().parent.parent
VARIANTS=('original_horizon','horizon16','horizon8','horizon8_small_frame','horizon8_linear_frame','horizon8_difference_frame')
DEFAULT_VARIANTS=('original_horizon','horizon8_difference_frame')

def read(p):return json.loads(p.read_text())
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def need(ok,message):
    if not ok:raise ValueError(message)

def load_modules(parent):
    direct=parent/'direct'
    sys.path.insert(0,str(direct));sys.path.insert(0,str(direct/'parent/code'))
    import terminal_elimination as E, factor_horn as F, translate_coordinates as T, build_affine as A
    return direct,E,F,T,A

def frame_atoms(raw,E):
    names={v['name']:i for i,v in enumerate(raw['variables'])}
    row=next(r for r in raw['residuals'] if r['label']=='shared.frame_definition')
    rhs={m:-c for m,c in E.normalize(row['terms']).items() if m!=(names['shared.W'],)}
    def plus(*ps):
        out={}
        for p in ps:
            for m,c in p.items():out[m]=out.get(m,0)+c
        return {m:c for m,c in out.items() if c}
    V=lambda i:{(i,):1};K=lambda c:{():c} if c else {}
    t=plus(V(names['t0']),K(16));q=V(names['pow2.output']);R=V(names['mul.1'])
    atoms=[t,plus(t,K(1)),plus(R,t),q,plus(q,K(1))]
    rest=plus(rhs,K(-2),*[{m:-c for m,c in E.multiply(a,a).items()} for a in atoms])
    for i in sorted(m[0] for m,c in rest.items() if len(m)==2):
        need(rest[(i,i)]==1 and rest.get((i,),0) in (0,2),'source frame square')
        atoms.append(plus(V(i),K(rest.get((i,),0)//2)))
    need(plus(K(2),*[E.multiply(a,a) for a in atoms])==rhs,'frame decomposition')
    return atoms

def changed_source(parent,variant,E):
    source=parent/'factorial_free_affine/raw_source.json'
    old=read(source);new=copy.deepcopy(old)
    names={v['name']:i for i,v in enumerate(new['variables'])}
    labels={}
    for i,r in enumerate(old['residuals']):labels.setdefault(r['label'],[]).append(i)
    def one(label):
        need(len(labels.get(label,[]))==1,'unique source label '+label)
        return labels[label][0]
    t=names['t0'];h=names['cofinal.horizon_root'];d=names['growth.power_base']
    R=names['mul.1'];F=names['crt.growth_majorant_F'];q=names['pow2.output']
    z=names['radix.odd_square_root_half'];sb=names['beta.odd_square_multiplier'];v=names['beta.odd_square_root_half']
    need(E.normalize(old['residuals'][0]['terms'])=={(R,):1,(F,F):-1},'selector source shape')
    changes={0:('selector.linear_offset',{(R,):1,(F,):-1}),
      one('radix.odd_square'):('radix.affine_four',{(q,):1,(z,):-4,():-1}),
      one('beta.odd_square_multiplier'):('beta.affine_odd_multiplier',{(sb,):1,(v,):-2,():-1})}
    if variant=='horizon16':
        changes[one('cofinal.horizon')]=('cofinal.affine_horizon',{(t,):1,(h,):-16,():16})
        changes[one('growth.base_definition')]=('growth.base_definition',{(d,):1,(t,):-1,():-18})
    elif variant in ('horizon8','horizon8_small_frame','horizon8_linear_frame','horizon8_difference_frame'):
        changes[one('cofinal.horizon')]=('cofinal.affine_horizon',{(t,):1,(h,):-8,():16})
        if variant in ('horizon8_linear_frame','horizon8_difference_frame'):
            changes[one('growth.base_definition')]=('growth.base_definition',{(d,):1,(t,):-1,():-18})
    elif variant!='original_horizon':raise ValueError(variant)
    frame_cert=None
    if variant in ('horizon8_small_frame','horizon8_linear_frame','horizon8_difference_frame'):
        atoms=frame_atoms(old,E)
        substitutions=[(t,{(h,):8,():-16}),(d,{(h,):16 if variant=='horizon8_small_frame' else 8,():2}),
          (R,{(F,):1}),(q,{(z,):4,():1})]
        transformed=[]
        for a in atoms:
            for coordinate,replacement in substitutions:a=E.substitute(a,coordinate,replacement)
            need(E.degree(a)<=1,'affine frame atom')
            transformed.append(a)
        used=sorted({m[0] for a in transformed for m in a if len(m)==1})
        bounds=[abs(a.get((),0))+sum(c*c//4 for m,c in a.items() if len(m)==1) for a in transformed]
        constant=max(16,max(bounds)+1)
        fr=one('shared.frame_definition');W=names['shared.W']
        replacement={(W,):1,():-constant}|{(i,i):-1 for i in used}
        changes[fr]=('shared.frame_definition',replacement)
        frame_cert={'schema':'linear_atom_majorant_v1','constant':constant,
          'original_atoms':[E.as_terms(a) for a in atoms],
          'substitutions':[{'coordinate':i,'replacement':E.as_terms(p)} for i,p in substitutions],
          'atoms':[E.as_terms(a) for a in transformed],'coordinate_squares':used,'atom_bounds':bounds,
          'identity':'For every integer z, a*z <= z*z+floor(a*a/4), and -a*z obeys the same bound.'}
    if variant=='horizon8_difference_frame':
        pr=one('cap.pooled_index_residue');yt=names['index0.Y'];yft=names['index2.Y']
        first={(yt,):1,(t,):-1,():-16};second={(yft,):1,(R,):-1,(t,):-1,():-16}
        difference={(yft,):1,(yt,):-1,(R,):-1}
        p=E.normalize(old['residuals'][pr]['terms'])
        for m,c in E.multiply(second,second).items():p[m]=p.get(m,0)-c
        for m,c in E.multiply(difference,difference).items():p[m]=p.get(m,0)+c
        p={m:c for m,c in p.items() if c}
        changes[pr]=('cap.pooled_index_residue',p)
        frame_cert['orientation_difference']={'row':pr,'retained_error':E.as_terms(first),
          'old_error':E.as_terms(second),'new_error':E.as_terms(difference),
          'small_error_bound':'(4m+5)W^2+4m < 4W^3 for m<=15,W>=19'}
    for i,(label,p) in changes.items():new['residuals'][i]={'label':label,'terms':E.as_terms(p)}
    new['variant']+=':signed_front_'+variant
    # Historical coordinate names are intentionally preserved. Their current
    # meanings are supplied by the source rows, never inferred from names.
    delta={'schema':'signed_front_source_delta_v1','profile':variant,
      'source_relative_path':'direct/factorial_free_affine/raw_source.json','source_sha256':sha(source),
      'changes':[{'row':i,'old':old['residuals'][i],'new':new['residuals'][i]} for i in sorted(changes)]}
    return new,delta,frame_cert

def measures(eq,poly):
    return {'variables':len(eq['variables']),'rows':len(eq['residuals']),
      'degree':max(len(m) for _,m in poly['terms']),'monomials':len(poly['terms']),
      'height':max(abs(c) for c,_ in poly['terms']),
      'row_height':max(abs(c) for r in eq['residuals'] for c,_ in r['terms'])}

def transfer_affine(parent,source,old,E,F,A,dense):
    oldrows=read(parent/'factorial_free_affine/projection_certificate.json')['retained_original_rows']
    newrows=read(source/'projection_certificate.json')['retained_original_rows']
    mapping={i:newrows.index(r) for i,r in enumerate(oldrows) if r in newrows}
    par=parent/('factorial_free_affine241_balanced' if dense else 'factorial_free_affine242_balanced')
    cert=read(par/'certificate.json')
    cert['endpoint']=source.name+('_dimension' if dense else '_balanced')
    cert['row_operations']=[[mapping[i],mapping[j],k] for i,j,k in cert['row_operations']]
    names={v['name']:i for i,v in enumerate(old['variables'])}
    rows=[E.normalize(r['terms']) for r in old['residuals']]
    for target,inputs in cert['coordinate_shears']:
        t=names[target];rest=F.add(F.V(t),{(names[n],):c for n,c in inputs.items()})
        rows=[E.substitute(r,t,rest) for r in rows]
    for i,j,k in cert['row_operations']:rows[i]=F.add(rows[i],{m:k*c for m,c in rows[j].items()})
    old_deleted=[p['row'] for p in cert['projections']]
    for p in cert['projections']:
        p['row']=mapping[p['row']];p['variable']=names[p['name']]
        q=E.candidate(rows[p['row']],p['variable'],False)
        need(q is not None and E.degree(q)<=1,'transferred affine projection '+p['name'])
        p['replacement']=E.as_terms(q)
        rows=[E.substitute(r,p['variable'],q) for r in rows]
    oldkeep=[i for i in range(len(oldrows)) if i not in old_deleted]
    new_deleted=[p['row'] for p in cert['projections']]
    newkeep=[i for i in range(len(newrows)) if i not in new_deleted]
    fm={j:newkeep.index(mapping[i]) for j,i in enumerate(oldkeep) if i in mapping and mapping[i] in newkeep}
    cert['final_row_operations']=[[fm[i],fm[j],k] for i,j,k in cert['final_row_operations']]
    eq,poly,metric=A.construct(old,cert)
    if source.name=='horizon8_difference_frame':
        # One finite row-basis choice removes the repeated horizon-square
        # leading coefficient. The certificate, not this search, proves
        # zero-set equivalence. Both directions are considered exactly.
        hn=next(i for i,v in enumerate(eq['variables']) if v['name']=='cofinal.horizon_root')
        polys=[E.normalize(r['terms']) for r in eq['residuals']]
        hits=[i for i,p in enumerate(polys) if p.get((hn,hn))==64]
        need(len(hits)==2,'two equal horizon-square coefficients')
        best=(metric['height'],metric['monomials'],None,cert,eq,poly,metric)
        for i,j in (hits,list(reversed(hits))):
            cc=copy.deepcopy(cert);cc['final_row_operations'].append([i,j,-1])
            ee,pp,mm=A.construct(old,cc)
            key=(mm['height'],mm['monomials'])
            if key<best[:2]:best=(*key,(i,j),cc,ee,pp,mm)
        cert,eq,poly,metric=best[3:]
    return cert,eq,poly,metric

def build(parent,out,variants):
    direct,E,F,T,A=load_modules(parent)
    def put(p,obj):
        p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(E.canonical_bytes(obj))
    all_metrics={}
    for variant in variants:
        folder=out/variant
        raw,delta,frame_cert=changed_source(direct,variant,E)
        fac,fc=F.transform(raw);pr,pc,_=E.optimize(fac,max_support=16);E.verify(fac,pr,pc)
        oldpr=read(direct/'parent/data/projected.json');oldtr=read(direct/'parent/equation/translation_certificate.json')
        shifts_by_name={oldpr['variables'][i]['name']:s for i,s in oldtr['shifts']}
        shifts={i:shifts_by_name[v['name']] for i,v in enumerate(pr['variables']) if v['name'] in shifts_by_name}
        eq=T.translate(pr,shifts);poly=E.expand(eq);metric=measures(eq,poly)
        for name,obj in [('source_delta.json',delta),('raw_source.json',raw),('factored_source.json',fac),
          ('factorization_certificate.json',fc),('projected.json',pr),('projection_certificate.json',pc),
          ('translation_certificate.json',{'convention':'old=new+shift','shifts':sorted(shifts.items())}),
          ('equation.json',eq),('expanded_polynomial.json',poly),('METRICS.json',metric)]:put(folder/name,obj)
        if frame_cert:put(folder/'frame_certificate.json',frame_cert)
        all_metrics[variant]={'stage':metric}
        for dense in (False,True):
            cert,ee,pp,mm=transfer_affine(direct,folder,eq,E,F,A,dense)
            endpoint=folder/('dimension' if dense else 'balanced')
            for name,obj in [('certificate.json',cert),('equation.json',ee),('expanded_polynomial.json',pp),('METRICS.json',mm)]:put(endpoint/name,obj)
            all_metrics[variant][endpoint.name]=mm
        print(json.dumps({variant:all_metrics[variant]},sort_keys=True))
    put(out/'ENDPOINTS.json',all_metrics)
    return all_metrics

if __name__=='__main__':
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--parent',type=Path,default=ROOT/'inherited_factorial_free')
    ap.add_argument('--output',type=Path,default=ROOT/'equations')
    ap.add_argument('--variants',nargs='+',choices=VARIANTS,default=list(DEFAULT_VARIANTS))
    args=ap.parse_args();build(args.parent,args.output,args.variants)
