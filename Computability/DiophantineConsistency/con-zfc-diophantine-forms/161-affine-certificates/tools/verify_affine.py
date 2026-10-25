#!/usr/bin/env python3
"""Independent exact full-lineage replay. No producer/compiler imports.

Finite checks do not replace the ordinary unbounded proof in PROOF.md.
"""
from pathlib import Path
from collections import Counter
import argparse, copy, hashlib, json, zipfile

ROOT=Path(__file__).resolve().parent
ARCHIVE=ROOT.parent/'provenance'/'ConZFC_Factorial_Free_Binomial_CRT_2026-10-25.zip'
PREFIX='ConZFC_Factorial_Free_Binomial_CRT_2026-10-25/direct/'
def require(ok,message):
    if not ok:raise ValueError(message)
def polynomial(terms):
    out=Counter()
    for c,indices in terms:
        require(type(c) is int and all(type(j) is int for j in indices),'noninteger polynomial data')
        out[tuple(sorted(indices))]+=c
    return {m:c for m,c in out.items() if c}
def plus(p,q,k=1):
    out=dict(p)
    for m,c in q.items():out[m]=out.get(m,0)+k*c
    return {m:c for m,c in out.items() if c}
def product(p,q):
    out={}
    for m,c in p.items():
        for n,d in q.items():
            key=tuple(sorted(m+n));out[key]=out.get(key,0)+c*d
    return {m:c for m,c in out.items() if c}
def replace(p,index,value):
    out={};powers={0:{():1}}
    for mon,c in p.items():
        k=mon.count(index)
        while max(powers)<k:
            l=max(powers);powers[l+1]=product(powers[l],value)
        remaining=tuple(i for i in mon if i!=index)
        out=plus(out,product({remaining:c},powers[k]))
    return out
def dump_terms(p):return [[c,list(m)] for m,c in sorted(p.items())]
def rows(d):return [polynomial(r['terms']) for r in d['residuals']]
def data_equal(a,b,label):require(rows(a)==rows(b),label)
def monic_value(row,i):
    c=row.get((i,),0);require(c in (-1,1),'pivot coefficient not unit')
    rest=plus(row,{(i,):c},-1);require(all(i not in m for m in rest),'nonlinear pivot')
    return {m:-v//c for m,v in rest.items()}
def compact(source,r,keep_variables,keep_rows):
    ren={i:j for j,i in enumerate(keep_variables)}
    require(all(i in ren for k in keep_rows for m in r[k] for i in m),'discarded live variable')
    out=copy.deepcopy(source);out['variables']=[copy.deepcopy(source['variables'][i]) for i in keep_variables]
    out['residuals']=[dict(source['residuals'][k],terms=dump_terms({tuple(ren[i] for i in m):c for m,c in r[k].items()})) for k in keep_rows]
    return out
def factor(raw,old_factor,cert):
    r=rows(raw)
    for change in cert['changes']:
        require(r[change['row']]==polynomial(change['old']),'Horn source pattern changed')
        r[change['row']]=polynomial(change['new'])
    removed=set(cert['deleted_rows']);out=copy.deepcopy(old_factor)
    expected=[r[i] for i in range(len(r)) if i not in removed]+[polynomial(cert['new_row'])]
    require(len(expected)==len(out['residuals']),'Horn row census')
    for rr,p in zip(out['residuals'],expected):rr['terms']=dump_terms(p)
    return out
def project(source,cert,check_replacements=True):
    r=rows(source);deleted=set();elim=set()
    for step in cert['steps']:
        j=step['row_id'];i=step['variable'];v=monic_value(r[j],i)
        if check_replacements:require(v==polynomial(step['restoration']),'projection restoration mismatch')
        r=[replace(p,i,v) for p in r];require(not r[j],'nonzero projection pivot')
        require(all(len(m)<=2 for p in r for m in p),'old projection raises degree')
        deleted.add(j);elim.add(i)
    require(cert['retained_original_rows']==[i for i in range(len(r)) if i not in deleted],'projection row map')
    keep=cert['retained_original_variables'];unused=set(cert['unconstrained_removed'])
    require(set(keep)|elim|unused==set(range(len(source['variables']))),'projection variable partition')
    return compact(source,r,keep,cert['retained_original_rows'])
def translate(source,cert):
    r=rows(source)
    for i,c in cert['shifts']:r=[replace(p,i,{(i,):1,():c}) for p in r]
    out=copy.deepcopy(source)
    for rr,p in zip(out['residuals'],r):rr['terms']=dump_terms(p)
    return out
def affine(source,cert,check_replacements=True):
    names={v['name']:i for i,v in enumerate(source['variables'])};r=rows(source)
    for name,inputs in cert['coordinate_shears']:
        i=names[name];v={(i,):1}
        for name,c in inputs.items():v=plus(v,{(names[name],):c})
        require(v.get((i,))==1 and i not in [names[k] for k in inputs],'noninvertible shear')
        r=[replace(p,i,v) for p in r]
    for i,j,c in cert['row_operations']:
        require(i!=j,'invalid row operation');r[i]=plus(r[i],r[j],c)
    removed_rows=set();removed_vars=set()
    for p in cert['projections']:
        i=p['variable'];j=p['row'];v=monic_value(r[j],i)
        require(max(map(len,v),default=0)<=1,'affine projection nonlinear')
        if check_replacements:require(v==polynomial(p['replacement']),'affine projection differs')
        r=[replace(q,i,v) for q in r];require(not r[j],'affine pivot remained')
        removed_rows.add(j);removed_vars.add(i)
    out=compact(source,r,[i for i in range(len(source['variables'])) if i not in removed_vars],[i for i in range(len(r)) if i not in removed_rows]);r=rows(out)
    for i,j,c in cert.get('final_row_operations',[]):
        require(i!=j,'invalid final row operation');r[i]=plus(r[i],r[j],c)
    for rr,p in zip(out['residuals'],r):rr['terms']=dump_terms(p)
    return out
def expected_mutation(raw):
    out=copy.deepcopy(raw);names={v['name']:i for i,v in enumerate(out['variables'])}
    q,z,s,v=[names[n] for n in ['pow2.output','radix.odd_square_root_half','beta.odd_square_multiplier','beta.odd_square_root_half']];count=0
    for r in out['residuals']:
        if r['label']=='radix.odd_square':
            require(polynomial(r['terms'])=={():-1,(q,):1,(z,):-4,(z,z):-4},'raw radix mismatch')
            r['terms']=dump_terms({():-1,(q,):1,(z,):-4});count+=1
        elif r['label']=='beta.odd_square_multiplier':
            require(polynomial(r['terms'])=={():-1,(s,):1,(v,):-4,(v,v):-4},'raw beta mismatch')
            r['terms']=dump_terms({():-1,(s,):1,(v,):-2});count+=1
    require(count==2,'raw mutation census');return out
def read_json(z,name):return json.loads(z.read(PREFIX+name))
def lineage(archive):
    out={};report={}
    with zipfile.ZipFile(archive) as z:
        raw=read_json(z,'factorial_free_affine/raw_source.json');fac=read_json(z,'factorial_free_affine/factored_source.json')
        fc=read_json(z,'factorial_free_affine/factorization_certificate.json');pc=read_json(z,'factorial_free_affine/projection_certificate.json');tc=read_json(z,'factorial_free_affine/translation_certificate.json')
        data_equal(factor(raw,fac,fc),fac,'inherited Horn mutation differs')
        p=project(fac,pc);data_equal(p,read_json(z,'factorial_free_affine/projected.json'),'inherited projection differs')
        tr=translate(p,tc);data_equal(tr,read_json(z,'factorial_free_affine/equation.json'),'inherited translation differs')
        changed_tr=translate(project(factor(expected_mutation(raw),fac,fc),pc),tc)
        for profile,n in [('principal',242),('companion',241)]:
            ac=read_json(z,f'factorial_free_affine{n}_balanced/certificate.json')
            original=affine(tr,ac);data_equal(original,read_json(z,profile+'/equation.json'),'inherited affine lineage differs')
            out[profile]=affine(changed_tr,ac)
            report[profile]={'old_monic_projections':len(pc['steps']),'old_coordinate_shears':len(ac['coordinate_shears']),'old_affine_projections':len(ac['projections']),'old_final_row_operations':len(ac['final_row_operations']),'raw_to_final_source_commutation':True}
    return out,report
def recollect(eq):
    P={}
    for r in rows(eq):
        a=list(r.items())
        for i,(m,c) in enumerate(a):
            for j in range(i,len(a)):
                n,d=a[j];key=tuple(sorted(m+n));P[key]=P.get(key,0)+(1 if i==j else 2)*c*d
    return {m:c for m,c in P.items() if c}
def verify_endpoint(source,path):
    cert=json.loads((path/'certificate.json').read_text());changed=json.loads((path/'mutated_source.json').read_text());target=json.loads((path/'equation.json').read_text())
    data_equal(source,changed,'new changed source not reached by complete lineage')
    r=rows(source);deleted=set();elim=set()
    for p in cert['eliminated']:
        i=p['variable'];j=p['row'];v=polynomial(p['replacement']);require(monic_value(r[j],i)==v,'new affine restoration invalid')
        r=[replace(q,i,v) for q in r];require(not r[j],'new projection pivot nonzero');deleted.add(j);elim.add(i)
    keepv=[i for i in range(len(source['variables'])) if i not in elim];keepr=[i for i in range(len(r)) if i not in deleted]
    require(keepv==cert['retained_original_variables'] and keepr==cert['retained_original_rows'],'new coordinate or row map differs')
    data_equal(compact(source,r,keepv,keepr),target,'new final coefficient differs')
    P=recollect(target);supplied=json.loads((path/'expanded_polynomial.json').read_text());require(P==polynomial(supplied['terms']),'quartic expansion differs')
    n=len(target['variables']);require({i for m in P for i in m}==set(range(n)),'advertised variable absent')
    metrics={'domain':'unrestricted integers','variables':n,'quadratic_residuals':len(target['residuals']),'degree':max(map(len,P)),'collected_monomials':len(P),'coefficient_height':max(map(abs,P.values())),'residual_height':max(abs(c) for rr in rows(target) for c in rr.values())}
    require(metrics==json.loads((path/'metrics.json').read_text()),'metric claim differs');return metrics
def main():
    ap=argparse.ArgumentParser();ap.add_argument('--archive',type=Path,default=ARCHIVE);ap.add_argument('--equations',type=Path,default=ROOT.parent/'stages'/'affine');ap.add_argument('--receipt',type=Path);a=ap.parse_args()
    sources,report=lineage(a.archive)
    for profile in sources:report[profile]['endpoint']=verify_endpoint(sources[profile],a.equations/profile)
    report.update(status='PASS',archive_sha256=hashlib.sha256(a.archive.read_bytes()).hexdigest(),producer_imports=False,scope='Complete exact finite source lineage and coefficients; unbounded calibration is separate')
    text=json.dumps(report,indent=2,sort_keys=True)+'\n'
    if a.receipt:a.receipt.write_text(text)
    print(text,end='')
if __name__=='__main__':main()
