#!/usr/bin/env python3
"""Independent graph, polynomial-cut, leading-form and coefficient audit.

No producing builder is imported. Exact sparse-polynomial arithmetic is reused
from the retained independent parent checker.
"""
from pathlib import Path
from collections import Counter
import argparse, gzip, hashlib, importlib.util, json, sys

ROOT=Path(__file__).resolve().parent
PARENT=ROOT/'upstream'/'parent'
sys.path.insert(0,str(PARENT))
spec=importlib.util.spec_from_file_location('retained_independent_checker',PARENT/'verify.py')
parent=importlib.util.module_from_spec(spec);sys.modules[spec.name]=parent;spec.loader.exec_module(parent)
Ring,Poly,Lead,expression=parent.Ring,parent.Poly,parent.Lead,parent.expression
INPUTS=parent.INPUTS;PORTS=parent.PORTS
VARIANTS=[('equation_78_626.json','XY','V2',78,78,626),
          ('equation_79_464.json','XY','bV',79,79,464),
          ('equation_80_460.json','q4','bV',79,80,460)]

def need(condition,message):
    if not condition:raise ValueError(message)

def source_pins():
    pins=json.loads((ROOT/'SOURCE_PINS.json').read_text())
    for p in pins['files']:
        need(hashlib.sha256((ROOT/p['path']).read_bytes()).hexdigest()==p['sha256'],'Pinned source differs: '+p['path'])
    return len(pins['files'])

def cuts(weight,mode):
    out=[]
    for target,free,formula in parent.checks_for(weight):
        if mode=='XY' and target=='Y2':
            out.append(('D',['X','Y'],'X*Y'));continue
        if mode=='XY' and target=='V0':
            out.append(('V0',['D','Y'],'D*Y'));continue
        if target in ('Mtot','Znum'):
            free=['D' if s=='Y2' else s for s in free];formula=formula.replace('Y2','D')
        out.append((target,free,formula))
        if mode=='q4' and target=='Y2':out.append(('D',['q'],'q**4'))
    return out

def audit(path,mode,weight,parent_count,ops,degree):
    data=json.loads(path.read_text());ancestor_path=PARENT/f'equation{parent_count}.json';ancestor=json.loads(ancestor_path.read_text())
    need(data['parent_sha256']==hashlib.sha256(ancestor_path.read_bytes()).hexdigest(),'Parent identity mismatch')
    need(data['coefficient_binding']==ancestor['coefficient_binding'],'Coherent tuple binding changed')
    need(data['witnesses']==INPUTS and data['fixed_numerals']==PORTS,'Independent coordinate or fixed-port census differs')
    need(data['domain']=='strictly positive integers','Wrong domain')
    old={r[0]:r for r in ancestor['source']};new={r[0]:r for r in data['source']}
    if mode=='XY':
        need(set(new)==(set(old)-{'Y2'})|{'D'},'Unexpected XY register census')
        allowed={'Y2','V0','P1mu2','mu2inner'}
    else:
        need(set(new)==set(old)|{'D'},'Unexpected q4 register census')
        allowed={'P1mu2','mu2inner'}
    for n,row in old.items():
        if n not in allowed:need(new[n]==row,'Changed inherited register: '+n)
    known=set(INPUTS+PORTS);table={}
    for row in data['source']:
        need(len(row)==4,'Malformed row');name,op,a,b=row
        need(name not in known and op in ('+','-','*'),'Duplicate register or nonpolynomial operation')
        for operand in (a,b):need(type(operand) is int or isinstance(operand,str) and operand in known,'Forward or unknown operand')
        known.add(name);table[name]=(op,a,b)
    need(data['output']=='N','Wrong output')
    live=set()
    def mark(name):
        if type(name) is int or name in live:return
        live.add(name)
        if name in table:
            _,a,b=table[name];mark(a);mark(b)
    mark('N');need(live==known,'Dead register, input or coefficient port')
    counts=dict(sorted(Counter(r[1] for r in data['source']).items()))
    need(len(table)==ops==data['operations'],'Live operation count mismatch')
    need(counts==data['operation_breakdown'],'Operation breakdown mismatch')
    covered=set()
    for target,free,formula in cuts(weight,mode):
        ring=Ring(free);cache={x:ring.variable(x) for x in free}
        def expand(name):
            if type(name) is int:return ring.constant(name)
            if name in cache:return cache[name]
            need(name in table,'Undeclared symbolic cut input')
            covered.add(name);op,a,b=table[name];a,b=expand(a),expand(b)
            value=a+b if op=='+' else a-b if op=='-' else a*b
            cache[name]=value;return value
        need(expand(target)==expression(formula,ring),'Exact polynomial cut failed: '+target)
    need(covered==set(table),'Not every actual register has an exact identity')
    # The two required denominator divisibilities are literal polynomial identities.
    ring=Ring(['q','w','s']);q,w,s=[ring.variable(x) for x in ('q','w','s')]
    X=w*q;Y=q**3*s;D=X*Y if mode=='XY' else q**4
    multiplier=w*s if mode=='XY' else ring.constant(1)
    divisor=4*Y if mode=='XY' else 4*w*q**3*s**2
    need(D==q**4*multiplier and 4*X*Y**2==D*divisor,'Denominator divisibility identity failed')
    # Entire leading forms, not samples or unproved syntactic degree bounds.
    ring=Ring(INPUTS+PORTS)
    leading={x:Lead(1 if x in INPUTS else 0,ring.variable(x)) for x in INPUTS+PORTS}
    def get(x):return Lead(0,ring.constant(x)) if type(x) is int else leading[x]
    for name,op,a,b in data['source']:
        a,b=get(a),get(b)
        if op=='*':r=Lead(a.degree+b.degree,a.form*b.form)
        elif a.degree==b.degree:r=Lead(a.degree,a.form+b.form if op=='+' else a.form-b.form)
        elif a.degree>b.degree:r=a
        else:r=Lead(b.degree,b.form if op=='+' else -b.form)
        need(bool(r.form.terms),'Unresolved leading cancellation at '+name);leading[name]=r
    if weight=='V2':
        expected='16384*(beta*J)**378*w**48*s**110*i**20*(eta+zeta)**64*(T+alpha)**4*(beta*J-F-alpha)**2'
        powers={'beta':378,'J':378,'w':48,'s':110,'i':20,'eta':64,'T':4,'F':2};coef=16384
    elif mode=='XY':
        expected='-1024*(beta*J)**284*w**36*s**82*i**14*(eta+zeta)**46*(T+alpha)**2'
        powers={'beta':284,'J':284,'w':36,'s':82,'i':14,'eta':46,'T':2};coef=-1024
    else:
        expected='-1024*(beta*J)**284*w**34*s**80*i**14*(eta+zeta)**46*(T+alpha)**2'
        powers={'beta':284,'J':284,'w':34,'s':80,'i':14,'eta':46,'T':2};coef=-1024
    need(leading['N'].degree==degree==data['exact_degree'],'Attained global degree differs')
    need(leading['N'].form==expression(expected,ring),'Whole leading homogeneous form differs')
    mon=tuple(powers.get(x,0) for x in ring.names)
    need(leading['N'].form.terms.get(mon)==coef,'Missing displayed nonzero coefficient')
    for meta in data['coefficient_binding']['ports'].values():
        blob=(ROOT/'coefficients'/meta['file']).read_bytes();raw=gzip.decompress(blob)
        need(hashlib.sha256(blob).hexdigest()==meta['gzip_sha256'],'Coefficient compressed-byte mismatch')
        need(hashlib.sha256(raw).hexdigest()==meta['raw_sha256'],'Coefficient integer-byte mismatch')
        need(blob==(PARENT/'coefficients'/meta['file']).read_bytes(),'Coefficient differs from authentic parent payload')
    return {'positive_unknowns':len(INPUTS),'operations':ops,'degree':degree,'operation_breakdown':counts,
            'exact_cut_identities':len(cuts(weight,mode)),'covered_registers':len(covered),
            'entire_leading_terms':len(leading['N'].form.terms),'leading_form':expected,
            'nonzero_coefficient':str(coef)+'*beta^'+str(powers['beta']),
            'sha256':hashlib.sha256(path.read_bytes()).hexdigest(),
            'selected_register_degrees':{x:leading[x].degree for x in ('D','V0','R','Q','Mtot','Znum','RG','N')}}

def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--output',type=Path);a=p.parse_args()
    result={'status':'PASS','upstream_files_authenticated':source_pins()}
    values=parent.check_or_write(False)
    numerals=parent.check_or_write.__globals__['reconstruct']()
    beta,K0,MC,MF=[numerals[k] for k in PORTS]
    need(beta>=31 and beta%2==1 and K0>0 and 0<MC<beta<MF<2*beta,'Authentic coefficient port box fails')
    result['fixed_numerals']=values
    result['equations']={name:audit(ROOT/name,mode,weight,pcount,ops,degree) for name,mode,weight,pcount,ops,degree in VARIANTS}
    result['scope']='Independent exact source provenance, free polynomial identities, whole leading forms, all liveness/counts, and authentic fixed coefficients; unbounded correctness is proved in DENOMINATOR_PROOF.md and the retained parent proof closure.'
    text=json.dumps(result,indent=2)+'\n'
    if a.output:a.output.write_text(text)
    print(text,end='')

if __name__=='__main__':main()
