#!/usr/bin/env python3
"""Independent exact audit of the strict-horizon quartic endpoint maps.

This checker imports no producer modules. It uses the retained independent
algebra checker for raw-source factorization, then checks the source's monic
projection and translations, both endpoint transformations, every collected
coefficient, metrics, liveness, and deliberately damaged artifacts.
"""
from pathlib import Path
from collections import defaultdict
import argparse, copy, hashlib, importlib.util, json

ROOT=Path(__file__).resolve().parent
SOURCE=ROOT.parent/'direct/source'
OUTPUT=ROOT.parent/'direct'
FACTORIZATION_CHECKER=ROOT.parent/'sources/factorial_free/direct/parent/code/inherited_independent_algebra.py'

def read(p):return json.loads(p.read_text())
def canonical(x):return (json.dumps(x,sort_keys=True,separators=(',',':'),ensure_ascii=False)+'\n').encode()
def require(ok,msg):
    if not ok:raise ValueError(msg)
def norm(terms):
    a=defaultdict(int)
    for c,m in terms:
        require(type(c) is int and all(type(v) is int and v>=0 for v in m),'noninteger sparse term')
        a[tuple(sorted(m))]+=c
    return {m:c for m,c in a.items() if c}
def add(p,q,k=1):
    out=dict(p)
    for m,c in q.items():
        out[m]=out.get(m,0)+k*c
        if not out[m]:del out[m]
    return out
def mul(p,q):
    out=defaultdict(int)
    for a,c in p.items():
        for b,d in q.items():out[tuple(sorted(a+b))]+=c*d
    return {m:c for m,c in out.items() if c}
def subst(p,v,q):
    result={}
    for m,c in p.items():
        term={():c}
        for i in m:term=mul(term,q if i==v else {(i,):1})
        result=add(result,term)
    return result
def rows(eq):return [norm(r['terms']) for r in eq['residuals']]
def same(rs,eq,msg):require(rs==rows(eq),msg)
def remap(p,keep):
    ren={v:i for i,v in enumerate(keep)}
    require(all(v in ren for m in p for v in m),'deleted variable survived')
    return {tuple(ren[v] for v in m):c for m,c in p.items()}
def monic(p,v,q):
    require(all(v not in m for m in q),'cyclic restoration')
    desired=add({(v,):1},q,-1)
    require(p==desired or p=={m:-c for m,c in desired.items()},'invalid monic inverse')
def expand(rs):
    result={}
    for p in rs:result=add(result,mul(p,p))
    return result
def verify_factorization(source,checker_path):
    spec=importlib.util.spec_from_file_location('retained_independent_algebra',checker_path)
    require(spec is not None and spec.loader is not None,'factorization checker unavailable')
    checker=importlib.util.module_from_spec(spec)
    spec.loader.exec_module(checker)
    return checker.factorization(read(source/'raw_source.json'),read(source/'factored_source.json'),read(source/'factorization_certificate.json'))
def verify_projection(source):
    fac=read(source/'factored_source.json');pc=read(source/'projection_certificate.json')
    require(hashlib.sha256((source/'factored_source.json').read_bytes()).hexdigest()==pc['input_sha256'],'projection source hash')
    rs=rows(fac)
    for step in pc['steps']:
        ri,v,q=step['row_id'],step['variable'],norm(step['restoration'])
        monic(rs[ri],v,q);rs=[subst(p,v,q) for p in rs]
        require(not rs[ri],'nonzero discarded pivot')
        require(all(len(m)<=2 for p in rs for m in p),'source projection degree')
    keep=pc['retained_original_variables'];retained=pc['retained_original_rows']
    require(all(not p for i,p in enumerate(rs) if i not in retained),'unaccounted source row')
    rs=[remap(rs[i],keep) for i in retained]
    pr=read(source/'projected.json');same(rs,pr,'projected source mismatch')
    require([fac['variables'][i] for i in keep]==pr['variables'],'source variable map')
    require(hashlib.sha256((source/'projected.json').read_bytes()).hexdigest()==pc['output_sha256'],'projection output hash')
    for v,k in read(source/'translation_certificate.json')['shifts']:
        require(type(k) is int,'noninteger source translation')
        rs=[subst(p,v,{(v,):1,():k}) for p in rs]
    eq=read(source/'equation.json');same(rs,eq,'source translation mismatch')
    return eq,rs,len(pc['steps'])

def endpoint(source_eq,source_rows,cert):
    names={v['name']:i for i,v in enumerate(source_eq['variables'])}
    rs=copy.deepcopy(source_rows)
    for target,inputs in cert['coordinate_shears']:
        v=names[target]
        require(target not in inputs,'non-unimodular coordinate shear')
        require(all(type(c) is int for c in inputs.values()),'noninteger shear')
        replacement=add({(v,):1},{(names[n],):c for n,c in inputs.items()})
        rs=[subst(p,v,replacement) for p in rs]
    def apply(op):
        i,j,k=op
        require(type(k) is int and i!=j and 0<=i<len(rs) and 0<=j<len(rs),'non-unimodular row operation')
        rs[i]=add(rs[i],rs[j],k)
    for op in cert['row_operations']:apply(op)
    removed_rows=set();removed_vars=set()
    for step in cert['projections']:
        ri,v,q=step['row'],step['variable'],norm(step['replacement'])
        require(step['name']==source_eq['variables'][v]['name'],'pivot variable name')
        require(all(len(m)<=1 for m in q),'nonaffine endpoint restoration')
        monic(rs[ri],v,q)
        rs=[subst(p,v,q) for p in rs]
        require(not rs[ri],'nonzero endpoint pivot')
        removed_rows.add(ri);removed_vars.add(v)
    keep=[i for i in range(len(source_eq['variables'])) if i not in removed_vars]
    retained=[i for i in range(len(rs)) if i not in removed_rows]
    require(keep==cert['retained_variables'] and retained==cert['retained_rows'],'endpoint retention map')
    rs=[remap(rs[i],keep) for i in retained]
    for op in cert['final_row_operations']:apply(op)
    return rs,[source_eq['variables'][i] for i in keep]

def verify(which,source,output,eq,rs):
    target=output/('principal236' if which=='principal' else 'dense235');cert=read(target/'certificate.json')
    require(hashlib.sha256((source/'equation.json').read_bytes()).hexdigest()==cert['source_sha256'],'endpoint source hash')
    final,vmeta=endpoint(eq,rs,cert)
    actual=read(target/'equation.json');same(final,actual,'endpoint residual mismatch')
    require(actual['variables']==vmeta,'endpoint variable metadata')
    require(actual['domain']=='unrestricted integers','endpoint domain')
    poly=expand(final)
    require(poly==norm(read(target/'expanded_polynomial.json')['terms']),'collected coefficient mismatch')
    n=len(vmeta)
    metric={'variables':n,'rows':len(final),'degree':max(map(len,poly)),'monomials':len(poly),'height':max(map(abs,poly.values())),'row_height':max(abs(c) for p in final for c in p.values())}
    require(metric==read(target/'METRICS.json'),'metrics mismatch')
    require(set(i for m in poly for i in m)==set(range(n)),'dead endpoint coordinate')
    negatives=[]
    bad=copy.deepcopy(cert);bad['projections'][0]['replacement'][0][0]+=1
    try:endpoint(eq,rs,bad)
    except ValueError:negatives.append('altered monic replacement')
    else:raise ValueError('bad replacement accepted')
    bad=copy.deepcopy(cert);bad['final_row_operations'][0][1]=bad['final_row_operations'][0][0]
    try:endpoint(eq,rs,bad)
    except ValueError:negatives.append('noninvertible row operation')
    else:raise ValueError('noninvertible row operation accepted')
    bad=copy.deepcopy(actual);bad['residuals'][0]['terms'][0][0]+=1
    try:same(final,bad,'altered coefficient')
    except ValueError:negatives.append('altered final coefficient')
    else:raise ValueError('altered final coefficient accepted')
    return {'metrics':metric,'source_monic_projections':len(cert['projections']),'coordinate_shears':len(cert['coordinate_shears']),'row_operations':len(cert['row_operations'])+len(cert['final_row_operations']),'negative_controls_rejected':negatives,'all_coordinates_live':True,'all_quartic_coefficients_recollected':True,'equation_sha256':hashlib.sha256((target/'equation.json').read_bytes()).hexdigest()}

def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--source',type=Path,default=SOURCE);ap.add_argument('--output',type=Path,default=OUTPUT);ap.add_argument('--factorization-checker',type=Path,default=FACTORIZATION_CHECKER);ap.add_argument('--receipt',type=Path)
    a=ap.parse_args();source=a.source.resolve();out=a.output.resolve()
    factorization_edits=verify_factorization(source,a.factorization_checker.resolve())
    eq,rs,count=verify_projection(source)
    result={'status':'PASS','imports_no_producer_modules':True,'strict_source_factorization_edits_replayed':factorization_edits,'strict_source_monic_pivots_replayed':count,'endpoints':{which:verify(which,source,out,eq,rs) for which in ['principal','dense']},'scope':'Exact polynomial algebra; the changed arithmetic semantics and inherited logical calibration are separate mathematical proofs.'}
    text=json.dumps(result,sort_keys=True,indent=2)+'\n'
    if a.receipt:a.receipt.write_text(text)
    print(text,end='')

if __name__=='__main__':main()
