#!/usr/bin/env python3
"""Transfer checked affine eliminations and row reductions to a new source."""
import argparse, copy, hashlib, json, sys
from pathlib import Path
HERE=Path(__file__).resolve().parent
PACKAGED=(HERE.parent/'stages').is_dir()
PARENT=(HERE.parent/'upstream/factorial_free/direct' if PACKAGED else HERE.parents[1]/'sources/incoming/ConZFC_Factorial_Free_Binomial_CRT_2026-10-25/ConZFC_Factorial_Free_Binomial_CRT_2026-10-25/direct')

def read(p):return json.loads(p.read_text())
def put(p,x):p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(E.canonical_bytes(x))
def facts(eq):
    pol=E.expand(eq)
    return pol,{'variables':len(eq['variables']),'rows':len(eq['residuals']),
      'degree':max(len(m) for c,m in pol['terms']),'monomials':len(pol['terms']),
      'height':max(abs(c) for c,m in pol['terms']),
      'row_height':max(abs(c) for r in eq['residuals'] for c,m in r['terms'])}

def build(source,out,dense=False,ashift=0,zshift=-1,parent=PARENT):
    global E,F
    sys.path.insert(0,str(parent/'parent/code'))
    import terminal_elimination as E
    import factor_horn as F
    old=read(source/'equation.json');oldpc=read(parent/'factorial_free_affine/projection_certificate.json')
    newpc=read(source/'projection_certificate.json')
    parentcert=read(parent/f'factorial_free_affine{241 if dense else 242}_balanced/certificate.json')
    # All affected affine rows precede growth.base_definition, the sole old deleted row.
    rowmap={i:newpc['retained_original_rows'].index(r) for i,r in enumerate(oldpc['retained_original_rows']) if r in newpc['retained_original_rows']}
    names={v['name']:i for i,v in enumerate(old['variables'])}
    rows=[E.normalize(r['terms']) for r in old['residuals']]
    operations=[]
    for name,delta in [('shared.A',ashift),('radix.progression_parameter',zshift)]:
        if delta:
            v=names[name];rest={(v,):1,():delta};rows=[E.substitute(p,v,rest) for p in rows]
            operations.append({'type':'translation','variable':v,'name':name,'delta':delta})
    for name,inputs in parentcert['coordinate_shears']:
        v=names[name];rest=F.add(F.V(v),{(names[n],):c for n,c in inputs.items()})
        rows=[E.substitute(p,v,rest) for p in rows]
        operations.append({'type':'shear','variable':v,'name':name,'restoration':E.as_terms(rest)})
    for i,j,k in parentcert['row_operations']:
        i,j=rowmap[i],rowmap[j];rows[i]=F.add(rows[i],{m:k*c for m,c in rows[j].items()})
        operations.append({'type':'row_add','target':i,'source':j,'multiple':k})
    dead=[];removed=[];skipped=[]
    for p in parentcert['projections']:
        i=rowmap[p['row']];v=names[p['name']];rest=E.candidate(rows[i],v,False)
        if rest is None or E.degree(rest)>1:
            skipped.append({'row':i,'name':p['name'],'reason':'not an affine monic consequence in this source'})
            continue
        rows=[E.substitute(r,v,rest) for r in rows]
        if rows[i]:raise ValueError('pivot did not vanish')
        operations.append({'type':'projection','row':i,'variable':v,'name':p['name'],'restoration':E.as_terms(rest)})
        dead.append(v);removed.append(i)
    # Map the parent's final row numbers through its original row ancestry.
    oldkept=[i for i in range(len(oldpc['retained_original_rows'])) if i not in [p['row'] for p in parentcert['projections']]]
    for i,j,k in parentcert['final_row_operations']:
        oi,oj=oldkept[i],oldkept[j]
        if oi not in rowmap or oj not in rowmap:continue
        i,j=rowmap[oi],rowmap[oj]
        if i in removed or j in removed:raise ValueError('row map points at removed row')
        rows[i]=F.add(rows[i],{m:k*c for m,c in rows[j].items()})
        operations.append({'type':'row_add','target':i,'source':j,'multiple':k})
    keep=[i for i in range(len(old['variables'])) if i not in dead];ren={v:i for i,v in enumerate(keep)}
    eq={'schema':'finite_quadratic_residuals_v1','domain':'unrestricted integers',
        'variant':f'fixed_growth_affine_{len(keep)}','polynomial':'sum(square(row) for row in residuals)',
        'variables':[old['variables'][v] for v in keep],
        'residuals':[{'label':old['residuals'][i]['label'],'terms':[[c,[ren[v] for v in m]] for m,c in sorted(r.items())]} for i,r in enumerate(rows) if i not in removed]}
    if any(len(m)>2 for r in eq['residuals'] for c,m in r['terms']):raise ValueError('degree increased')
    pol,met=facts(eq)
    cert={'schema':'integral_affine_operations_v1','input_sha256':hashlib.sha256((source/'equation.json').read_bytes()).hexdigest(),
        'output_sha256':hashlib.sha256(E.canonical_bytes(eq)).hexdigest(),'operations':operations,
        'retained_variables':keep,'retained_rows':[i for i in range(len(rows)) if i not in removed],
        'source_path':'stages/compressed/equation.json','inherited_map':rowmap,'dense':dense,'ashift':ashift,'zshift':zshift,'skipped_parent_projections':skipped}
    if out:
        for n,x in [('equation.json',eq),('expanded_polynomial.json',pol),('METRICS.json',met),('certificate.json',cert)]:put(out/n,x)
    return eq,pol,met,cert

if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('source',type=Path,nargs='?',default=HERE.parent/'stages/compressed' if PACKAGED else HERE/'frame_compressed');ap.add_argument('output',type=Path,nargs='?');ap.add_argument('--dense',action='store_true');ap.add_argument('--ashift',type=int,default=6);ap.add_argument('--zshift',type=int,default=0);ap.add_argument('--parent',type=Path,default=PARENT)
    a=ap.parse_args()
    if a.output is None:a.output=(HERE.parent/'equations'/('compact' if a.dense else 'balanced') if PACKAGED else HERE/('final229' if a.dense else 'final230'))
    eq,po,me,ce=build(a.source,a.output,a.dense,a.ashift,a.zshift,a.parent);print(json.dumps(me,indent=2))
