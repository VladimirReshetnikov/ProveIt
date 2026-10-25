#!/usr/bin/env python3
"""Exact signed factorization of the calibrated direct Horn source.

Only literal JSON is read. No upstream builder is imported. The copied
terminal_elimination module is the reviewed, standard-library-only monic
eliminator; its proof certificate is independently replayed.
"""
from pathlib import Path
from collections import defaultdict
from math import isqrt
import argparse, copy, hashlib, json
import terminal_elimination as E

def add(*ps):
    out=defaultdict(int)
    for p in ps:
        for m,c in p.items(): out[m]+=c
    return {m:c for m,c in out.items() if c}

def neg(p): return {m:-c for m,c in p.items()}
def V(i): return {(i,):1}

def affine_root(p):
    """Unique sign-normalized affine square root, checked by multiplication."""
    vs=sorted({v for m in p for v in m})
    if not vs:
        a=isqrt(p.get((),0))
        r={():a} if a else {}
    else:
        pivot=next(v for v in vs if p.get((v,v),0)>0)
        a=isqrt(p[(pivot,pivot)])
        if a*a!=p[(pivot,pivot)]: raise ValueError('not square')
        r={(pivot,):a}
        for v in vs:
            if v==pivot: continue
            num=p.get(tuple(sorted((v,pivot))),0)
            if num%(2*a): raise ValueError('fractional root')
            if num: r[(v,)]=num//(2*a)
        num=p.get((pivot,),0)
        if num%(2*a): raise ValueError('fractional constant root')
        if num:r[()]=num//(2*a)
    if E.multiply(r,r)!=p: raise ValueError('not exact affine square')
    return r

def transform(equation):
    e=copy.deepcopy(equation); e.pop('metrics',None)
    if e['domain']!='unrestricted integers': raise ValueError('integer domain required')
    names={v['name']:i for i,v in enumerate(e['variables'])}
    sq=[names['sqd.'+str(i)] for i in range(17)]
    rows=[E.normalize(r['terms']) for r in e['residuals']]
    definitions={}
    for s in sq:
        hits=[i for i,p in enumerate(rows) if e['residuals'][i]['label']=='nonnegative_square_difference' and p.get((s,))==1 and E.candidate(p,s,False) is not None]
        if len(hits)!=1: raise ValueError(('square definition',s,hits))
        definitions[s]=hits[0]
    roots={s:affine_root(E.candidate(rows[definitions[s]],s,False)) for s in sq}
    # Recover the eleven-link literal product chain, not guessed wire names.
    chain=[];factors=sq[:9]+['bundle',sq[13],sq[14]]
    previous=factors[0]
    for f in factors[1:]:
        right=add(V(sq[11]),V(sq[12])) if f=='bundle' else V(f)
        product=E.multiply(V(previous),right)
        candidates=[]
        for rid,p in enumerate(rows):
            for m,c in p.items():
                if c==1 and len(m)==1 and E.candidate(p,m[0],False)==product:
                    candidates.append((rid,m[0]))
        if len(candidates)!=1: raise ValueError(('product chain',f,candidates))
        rid,previous=candidates[0];chain.append((rid,previous))
    oldroot=chain[-1][1]
    protected=set(sq[:9]+sq[13:15]+[v for _,v in chain[:-1]])
    allowed={definitions[s] for s in sq[:9]+sq[13:15]}|{i for i,_ in chain}
    for rid,p in enumerate(rows):
        if rid not in allowed and any(v in protected for m in p for v in m):
            raise ValueError(('factor escapes source',rid))
    # First nine factors, modus ponens and generalization now signed.
    changes=[]
    for s in sq[:9]+sq[13:15]:
        rid=definitions[s];new=add(V(s),neg(roots[s]))
        changes.append({'row':rid,'old':E.as_terms(rows[rid]),'new':E.as_terms(new)})
        rows[rid]=new;e['variables'][s]['kind']='gate'
    # Nine ordinary factors cost eight products. Move the two inference
    # factors before the final square; only then multiply by the bundle sum.
    rid9,out9=chain[8];rid10,out10=chain[9];rid11,out11=chain[10]
    rewrites={rid9:add(V(out9),neg(E.multiply(V(chain[7][1]),V(sq[13])))),
              rid10:add(V(out10),neg(E.multiply(V(out9),V(sq[14])))),
              rid11:add(V(out11),neg(E.multiply(V(out10),V(out10))))}
    for rid,new in rewrites.items():
        changes.append({'row':rid,'old':E.as_terms(rows[rid]),'new':E.as_terms(new)})
        rows[rid]=new
    root=len(e['variables']);e['variables'].append({'name':'factored.horn','kind':'gate'})
    newrow=add(V(root),neg(E.multiply(V(oldroot),add(V(sq[11]),V(sq[12])))))
    # All external uses of oldroot become the exact factored Horn value.
    for rid,p in enumerate(rows):
        if rid not in {i for i,_ in chain} and any(oldroot in m for m in p):
            rows[rid]=E.substitute(p,oldroot,V(root))
            changes.append({'row':rid,'old':E.as_terms(p),'new':E.as_terms(rows[rid])})
    rows.append(newrow);e['residuals'].append({'label':'factored.horn','terms':[]})
    # The guarded bundle tests ((c-a)(c-b))^2=(d+1)^2. Form its signed
    # product first. Reuse sqd.9 for H and the old product for G=H^2-D^2.
    h=sq[9];unused=sq[10]
    oldproduct=E.multiply(V(h),V(unused))
    hits=[(rid,m[0]) for rid,p in enumerate(rows) for m,c in p.items()
          if c==1 and len(m)==1 and E.candidate(p,m[0],False)==oldproduct]
    if len(hits)!=1:raise ValueError('guard product')
    pr,g=hits[0]
    guardroot=roots[sq[11]]
    if guardroot.get((g,)) not in (-1,1):raise ValueError('guard interface')
    other=[v for m in guardroot for v in m if v!=g]
    if len(other)!=1:raise ValueError('guard companion')
    dv=other[0]
    dhits=[(rid,E.candidate(p,dv,False)) for rid,p in enumerate(rows)
           if E.candidate(p,dv,False) is not None]
    if len(dhits)!=1:raise ValueError('guard companion definition')
    dr,D2=dhits[0]
    if E.degree(D2)>2:raise ValueError('guard companion degree')
    guard_allowed={definitions[h],definitions[unused],pr,dr,definitions[sq[11]]}
    for rid,p in enumerate(rows):
        if rid not in guard_allowed and any(v in {h,unused,g,dv} for m in p for v in m):
            raise ValueError(('guard escapes source',rid))
    guard_rewrites={definitions[h]:add(V(h),neg(E.multiply(roots[h],roots[unused]))),
        pr:add(V(g),neg(E.multiply(V(h),V(h))),D2),
        definitions[sq[11]]:add(V(sq[11]),neg(E.multiply(V(g),V(g))))}
    for rid,new in guard_rewrites.items():
        changes.append({'row':rid,'old':E.as_terms(rows[rid]),'new':E.as_terms(new)});rows[rid]=new
    deleted={definitions[unused],dr}
    e['variables'][h]['kind']='gate'
    e['residuals']=[dict(e['residuals'][i],terms=E.as_terms(p)) for i,p in enumerate(rows) if i not in deleted]
    e['variant']+=':signed_factorization'
    certificate={'schema':'signed_horn_factorization_v1','input_sha256':hashlib.sha256(E.canonical_bytes(equation)).hexdigest(),
        'square_variables':sq,'square_roots':{str(s):E.as_terms(p) for s,p in roots.items()},
        'product_chain':chain,'changes':changes,'deleted_rows':sorted(deleted),
        'guard_variables':{'h':h,'old_second_square':unused,'g':g,'old_D_square':dv},
        'new_root':root,'new_row':E.as_terms(newrow),
        'identity':'(product(L_i^2))*(B^2+G^2) = (product(L_i))^2*(B^2+G^2)',
        'guard_identity':'((c-a)^2*(c-b)^2-D^2)^2 = (((c-a)*(c-b))^2-D^2)^2'}
    certificate['output_sha256']=hashlib.sha256(E.canonical_bytes(e)).hexdigest()
    return e,certificate

def main():
    ap=argparse.ArgumentParser();ap.add_argument('input',type=Path);ap.add_argument('output',type=Path);ap.add_argument('--cap',type=int,default=16);args=ap.parse_args()
    eq=json.loads(args.input.read_text());factored,fc=transform(eq)
    out,cert,metrics=E.optimize(factored,max_support=args.cap)
    check=E.verify(factored,out,cert);args.output.mkdir(parents=True,exist_ok=True)
    for name,obj in [('factored_source.json',factored),('factorization_certificate.json',fc),('equation.json',out),('projection_certificate.json',cert),('expanded_polynomial.json',E.expand(out)),('METRICS.json',metrics|check)]:
        (args.output/name).write_bytes(E.canonical_bytes(obj))
    print(json.dumps(metrics|check,indent=2))
if __name__=='__main__':main()
