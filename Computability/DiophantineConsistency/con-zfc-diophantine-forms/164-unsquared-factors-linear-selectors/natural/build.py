#!/usr/bin/env python3
"""Canonical-sign extraction before natural-domain quadratization.

Every new variable remains natural.  The source mutation is justified by the
ordinary canonical-lift argument in PROOF.md, not by an orthant automorphism.
"""
from copy import deepcopy
from pathlib import Path
import argparse, importlib.util, json, hashlib, sys
sys.dont_write_bytecode=True
ROOT=Path(__file__).resolve().parent
BASE=ROOT/'inherited'
def module(name,path):
    s=importlib.util.spec_from_file_location(name,path);m=importlib.util.module_from_spec(s);s.loader.exec_module(m);return m
pc=module('round20_natural_contract',BASE/'contract_fixed.py')
checker=module('round20_natural_check',BASE/'check_natural.py')
def write(path,obj):
    path.parent.mkdir(parents=True,exist_ok=True);path.write_text(json.dumps(obj,indent=2,sort_keys=True)+'\n')
def add(*ps):
    p={}
    for q in ps:
        for m,c in q.items():p[m]=p.get(m,0)+c
    return {m:c for m,c in p.items() if c}
def scale(k,p):return {m:k*c for m,c in p.items() if k*c}

def transform(source):
    E=deepcopy(source);vs={v['name']:i for i,v in enumerate(E['variables'])}
    def atom(n):return {(vs[n],):1}
    def row(label,p):return {'label':label,'terms':pc.dump(p)}
    fresh=[]
    def gate(name,p):
        name='oriented.'+name;i=len(E['variables']);vs[name]=i
        E['variables'].append({'name':name,'kind':'canonical-sign gate'})
        fresh.append(row(name,add({(i,):1},scale(-1,p))))
        return {(i,):1}
    dif=add(atom('crt.encoded.Sp'),scale(-1,atom('crt.encoded.S')))
    factors=[dif]+[add(dif,atom(n)) for n in ('mul.339','mul.341','mul.343','mul.345','mul.347','mul.349','mul.351','mul.353')]
    factors+=[add(atom('mul.369'),scale(-1,atom('mul.363'))),add(atom('mul.372'),scale(-1,atom('mul.373')))]
    q=factors[0]
    for i,p in enumerate(factors[1:],1):q=gate('product'+str(i),pc.multiply(q,p))
    ac=add(atom('crt.encoded.a'),scale(-1,atom('crt.encoded.c')))
    bc=add(atom('crt.encoded.b'),scale(-1,atom('crt.encoded.c')))
    e=gate('inequality_product',pc.multiply(ac,bc))
    d=add(atom('crt.encoded.d'),{():2})
    z=gate('inequality_minus',pc.multiply(q,add(e,scale(-1,d))))
    z=gate('inequality_branch',pc.multiply(z,add(e,d)))
    w=gate('axiom_branch',pc.multiply(q,add(dif,atom('mul.358'))))
    deleted=['sqd.'+str(i) for i in range(15)]+['mul.355','mul.357']+['mul.'+str(i) for i in range(374,385)]
    deleted_ids={vs[n] for n in deleted};removed=[];rows=[]
    for ri,r in enumerate(E['residuals']):
        p=pc.loadpoly(r['terms'])
        if r['label']=='crt.nonnegative_evaluation':
            p=add(pc.multiply(z,z),pc.multiply(w,w),atom('sqd.15'),atom('sqd.16'),scale(-1,atom('mul.407')))
            r=row('crt.oriented_nonnegative_evaluation',p)
        elif any(p.get((i,))==1 for i in deleted_ids):removed.append(ri);continue
        if any(i in deleted_ids for m in p for i in m):raise ValueError(('remaining deleted use',ri))
        rows.append(r)
    E['residuals']=rows+fresh
    used=sorted({i for r in E['residuals'] for c,m in r['terms'] for i in m});ren={i:j for j,i in enumerate(used)}
    E['variables']=[E['variables'][i] for i in used]
    for r in E['residuals']:r['terms']=pc.dump(pc.loadpoly([[c,[ren[i] for i in m]] for c,m in r['terms']]))
    E['variant']='round20_canonical_sign_square_extraction';E['metrics'],poly=pc.metrics_and_polynomial(E)
    cert={'schema':'canonical_sign_square_extraction_v1','parent_equation_sha256':hashlib.sha256(pc.canonical(source)).hexdigest(),'deleted_variables':deleted,'removed_parent_row_ids':removed,'fresh_rows':[r['label'] for r in fresh],'retained_extended_parent_indices':used,'ordinary_proof':'PROOF.md'}
    return E,poly,cert

def build(output):
    source=json.loads((BASE/'cofinal_raw/equation.json').read_text());e,exp,cert=transform(source)
    for n,o in [('equation.json',e),('expanded_polynomial.json',exp),('transformation.json',cert)]:write(output/'raw'/n,o)
    result={}
    for name,cap in [('dimension206',24),('projected207',32),('projected208',32)]:
        priority=json.loads((ROOT/name/'priority.json').read_text())
        if sorted(priority)!=list(range(len(e['residuals']))):raise ValueError('invalid priority')
        pc.SOURCE_SHA256=hashlib.sha256(pc.canonical(e)).hexdigest();pc.ROW_PRIORITY=priority
        t,c,p=pc.contract(e,support_cap=cap);r,ind=checker.verify(e,t,c)
        if p['terms']!=ind:raise ValueError('expansion mismatch')
        result[name]=t['metrics']
        for n,o in [('equation.json',t),('elimination_certificate.json',c),('expanded_polynomial.json',p),('VERIFICATION.json',r),('priority.json',priority)]:write(output/name/n,o)
        print(name,t['metrics'],flush=True)
    basis=module('round20_row_emitter',ROOT/'apply_row_basis.py')
    for name,origin in [('natural206','dimension206'),('balanced207','projected207'),('sparse208','projected208')]:
        original=json.loads((output/origin/'equation.json').read_text())
        operations=json.loads((ROOT/name/'operations.json').read_text())
        target,polynomial=basis.emit(original,operations)
        mm=target['metrics']
        met=dict(variables=mm['variables'],rows=mm['quadratic_rows'],terms=mm['expanded_monomials'],height=mm['max_abs_expanded_coefficient'],row_height=mm['max_abs_row_coefficient'],row_support=sum(len(r['terms']) for r in target['residuals']))
        rc=dict(schema='invertible_integer_row_shears_v1',source=origin+'/equation.json',source_sha256=hashlib.sha256((output/origin/'equation.json').read_bytes()).hexdigest(),source_equation_sha256=hashlib.sha256(pc.canonical(original)).hexdigest(),operations=operations,metrics=met,equation=target)
        for n,o in [('equation.json',target),('expanded_polynomial.json',polynomial),('row_basis_certificate.json',rc),('operations.json',operations)]:write(output/name/n,o)
        result[name]=mm
    write(output/'SUMMARY.json',result)
    return result
if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--output',type=Path,required=True);a=p.parse_args();build(a.output)
