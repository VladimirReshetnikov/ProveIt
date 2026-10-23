#!/usr/bin/env python3
"""Independent exact parent, support-isolation, and target-extraction audit.

This checks finite algebra and data. It does not test or decide consistency.
Uses only Python standard library. All checks remain active under python -O.
"""
import hashlib,itertools,json,math
from pathlib import Path
from coeff_poly import parse_poly
ROOT=Path(__file__).resolve().parent
def require(x,msg):
    if not x:raise ValueError(msg)
def add(a,b,k=1):
    out=dict(a)
    for e,c in b.items():
        out[e]=out.get(e,0)+k*c
        if not out[e]:del out[e]
    return out
def mul(a,b):
    out={}
    for e,c in a.items():
        for f,d in b.items():
            g=tuple(x+y for x,y in zip(e,f));out[g]=out.get(g,0)+c*d
    return {g:c for g,c in out.items() if c}
def parent_rows():
    raw=(ROOT/'parent_system.json').read_bytes();require(hashlib.sha256(raw).hexdigest()=='ac2a67782d344d1e74fd93bc3f09fae0097eaed1829fd8194ae235ae84763e48','parent SHA256')
    d=json.loads(raw);names=d['variables']+d['constants'];n=len(names);zero=(0,)*n;env={}
    for i,name in enumerate(names):
        e=list(zero);e[i]=1;env[name]={tuple(e):1}
    def read(x):return ({zero:x} if x else {}) if type(x) is int else env[x]
    for name,op,a,b in d['source']:
        a,b=read(a),read(b);env[name]=mul(a,b) if op=='*' else add(a,b,-1 if op=='-' else 1)
    rows=[]
    for a,b in d['comparisons']:
        p=add(read(a),read(b),-1);shifted={}
        for e,c in p.items():
            require(sum(e[:31])<=2,'parent exceeds quadratic degree')
            terms={e:c}
            for i in range(31):
                if e[i]:
                    nt={}
                    for f,v in terms.items():
                        for j in range(f[i]+1):
                            g=list(f);g[i]=j;g=tuple(g);nt[g]=nt.get(g,0)+v*math.comb(f[i],j)
                    terms=nt
            shifted=add(shifted,terms)
        rows.append(shifted)
    return rows,d['variables']
def audit(path,rows,names):
    d=json.loads(path.read_text());w=d['weights'];W=max(w);require(len(w)==31 and len(set(w))==31 and min(w)>0,'weights must be31 distinct positive integers')
    require(d['variables']==names,'parent variable order')
    expansion={}
    for i in range(32):
        for j in range(i,32):
            a=[0]*31
            if i:a[i-1]+=1
            if j:a[j-1]+=1
            expansion[tuple(a)]=sum(x*y for x,y in zip(a,w))
    require(len(expansion)==528,'quadratic expansion size')
    supports={tuple(t['alpha']) for r in d['rows'] for t in r['terms']};require(len(supports)==71,'support size')
    for a in supports:
        collisions=[b for b,v in expansion.items() if v==expansion[a]]
        require(collisions==[a],'supported monomial collision: '+str(a))
    source_terms=[]
    for r in d['rows']:
        j=r['original_row_one_based']-1;reconstructed={}
        for t in r['terms']:
            a=tuple(t['alpha']);require(sum(a)<=2,'degree')
            pol=parse_poly(t['coefficient'],d['ports']);weighted=parse_poly(t['weighted_coefficient'],d['ports'])
            factor=math.factorial(2-sum(a))*math.prod(math.factorial(e) for e in a)
            require(weighted=={p:c*factor for p,c in pol.items()},'factorial coefficient')
            for p,c in pol.items():reconstructed[a+p]=c
            weight=expansion[a];require(t['weight']==weight and t['encoding_exponent']==r['target_exponent']-weight,'target record')
            source_terms.append((r['target_exponent'],a,t['encoding_exponent']))
        require(reconstructed==rows[j],'shifted parent row mismatch')
    require(len(source_terms)==136,'136 weighted terms')
    require(len({e for _,_,e in source_terms})==136,'coefficient positions in D must be distinct')
    checks=0;hits=0
    targets={r['target_exponent'] for r in d['rows']}
    for h,a,e in source_terms:
        for b,weight in expansion.items():
            checks+=1
            if e+weight in targets:
                require(e+weight==h and a==b,'cross-target contamination')
                hits+=1
    require(hits==136,'each source term must hit exactly its own monomial/target')
    require(d['rows'][-1]['constant_coefficient']=='1','positive highest coefficient')
    return dict(file=path.name,W=W,selected_monomials=len(supports),all_monomials=528,distinct_all_sums=len(set(expansion.values())),unselected_collisions=528-len(set(expansion.values())),source_terms=136,extraction_checks=checks,successful_diagonal_terms=hits,nine_exact_degree_formula=108296*W+53272)
def main():
    rows,names=parent_rows();results=[audit(p,rows,names) for p in sorted(ROOT.glob('targets_sparse[0-9]*.json'))]
    out=dict(status='PASS',scope='Exact finite parent algebra and supported-monomial extraction; inherited compiler equivalence remains a dependency',variants=results)
    (ROOT/'source_certificate.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
if __name__=='__main__':main()
