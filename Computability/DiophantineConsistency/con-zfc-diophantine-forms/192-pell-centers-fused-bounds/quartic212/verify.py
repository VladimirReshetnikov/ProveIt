#!/usr/bin/env python3
"""Independent exact checks of the quartic-center source change and row basis.

No producer module is imported. Finite identities do not prove the unbounded
Pell/CRT/calculus theorems; those are the ordinary proofs in the report.
"""
from pathlib import Path
from collections import defaultdict
from itertools import combinations_with_replacement
import argparse, copy, hashlib, json, tempfile


def require(p,message):
    if not p: raise ValueError(message)


def load(path):
    return json.loads(path.read_bytes())


def row(r,n):
    out={}
    for c,m in r['terms']:
        require(type(c) is int and c!=0,'Invalid coefficient')
        require(all(type(i) is int and 0<=i<n for i in m),'Invalid index')
        require(m==sorted(m) and len(m)<=2,'Invalid quadratic monomial')
        key=tuple(m)
        require(key not in out,'Duplicate monomial')
        out[key]=c
    require(out,'Empty residual')
    return out


def expansion(e):
    out=defaultdict(int)
    for r in e['residuals']:
        p=list(row(r,len(e['variables'])).items())
        for i,j in combinations_with_replacement(range(len(p)),2):
            (a,c),(b,d)=p[i],p[j]
            out[tuple(sorted(a+b))] += c*d*(1 if i==j else 2)
    return {m:c for m,c in out.items() if c}


def apply(rows,ops,inverse=False):
    result=copy.deepcopy(rows)
    for op in (list(reversed(ops)) if inverse else ops):
        i,j,k=op['target'],op['source'],op['multiple']
        require(type(i) is int and type(j) is int and i!=j,'Bad elementary row operation')
        require(0<=i<len(rows) and 0<=j<len(rows),'Bad row index')
        require(type(k) is int and k!=0,'Bad row multiple')
        if inverse:k=-k
        for m,c in result[j].items():
            result[i][m]=result[i].get(m,0)+k*c
            if result[i][m]==0:del result[i][m]
    return result


def verify(source,raw_dir,reduced_dir,mutations=False):
    require(hashlib.sha256(source.read_bytes()).hexdigest()==
      '20a2108353a3756ed7d1ddfdc71695131dcf0b6d94039988d9565ac48e6e1f0a',
      'Pinned source mismatch')
    old=load(source);new=load(raw_dir/'equation.json');red=load(reduced_dir/'equation.json')
    def check_graft(e):
        require(len(e['variables'])==212 and len(e['residuals'])==152,'Wrong dimensions')
        expect=copy.deepcopy(old['variables'])
        expect[208]['name']='growth_pell.t4F'
        expect += [{'kind':'signed_growth_witness','name':'growth_pell.t2'},
                   {'kind':'signed_growth_witness','name':'growth_pell.t4'}]
        require(e['variables']==expect,'Coordinate binding differs')
        special={125:{():-64,(0,):1,(178,178):-4},
                 147:{(2,211):-1,(208,):1},
                 148:{():-1,(2,208):-2,(207,207):1,(208,208):-1},
                 149:{(2,):1,(211,):-1,(209,211):-2},
                 150:{(0,0):-1,(210,):1},
                 151:{(210,210):-1,(211,):1}}
        for j,r in enumerate(e['residuals']):
            p=row(r,212)
            if j in special:require(p==special[j],'Incorrect new residual '+str(j))
            else:require(r==old['residuals'][j],'Altered retained residual '+str(j))
        occurrences=[j for j,r in enumerate(e['residuals'])
                     if any(178 in m for c,m in r['terms'])]
        require(occurrences==[125],'Horizon helper leaks into other equations')
        require({i for r in e['residuals'] for c,m in r['terms'] for i in m}==set(range(212)),
                'Coordinate liveness differs')
    check_graft(new)
    cert=load(raw_dir/'certificate.json')
    require(cert['input_sha256']==hashlib.sha256(source.read_bytes()).hexdigest(),'Graft source hash')
    require(cert['output_sha256']==hashlib.sha256((raw_dir/'equation.json').read_bytes()).hexdigest(),
            'Graft target hash')
    rows=[row(r,212) for r in new['residuals']]
    reduced=[row(r,212) for r in red['residuals']]
    basis=load(reduced_dir/'basis_certificate.json')
    require(red['variables']==new['variables'],'Basis changes coordinate domain')
    require(basis['input_sha256']==hashlib.sha256((raw_dir/'equation.json').read_bytes()).hexdigest(),
            'Basis source hash')
    require(basis['output_sha256']==hashlib.sha256((reduced_dir/'equation.json').read_bytes()).hexdigest(),
            'Basis output hash')
    require(apply(rows,basis['operations'])==reduced,'Forward row certificate fails')
    require(apply(reduced,basis['operations'],True)==rows,'Inverse row certificate fails')
    receipts=[]
    for folder,e in [(raw_dir,new),(reduced_dir,red)]:
        p=expansion(e)
        exported=load(folder/'expanded_polynomial.json')
        q={tuple(m):c for c,m in exported['terms']}
        require(len(q)==len(exported['terms']) and q==p,'Collected polynomial mismatch')
        expected={'variables':212,'residuals':152,'degree':max(map(len,p)),
                  'monomials':len(p),'coefficient_height':max(map(abs,p.values())),
                  'residual_height':max(abs(c) for r in e['residuals'] for c,m in r['terms']),
                  'residual_monomials':sum(len(r['terms']) for r in e['residuals'])}
        met=load(folder/'metrics.json')
        for k,v in expected.items():require(met[k]==v,'Metric differs: '+k)
        require(expected['degree']==4,'Not a quartic')
        receipts.append(expected)
    rejected=0
    if mutations:
        for index,term_index in [(125,0),(147,0),(148,1),(149,0),(150,0),(151,0)]:
            bad=copy.deepcopy(new);bad['residuals'][index]['terms'][term_index][0]+=1
            try:check_graft(bad)
            except ValueError:rejected+=1
            else:raise ValueError('Mutation was not rejected')
        bad=copy.deepcopy(basis['operations']);bad[0]['multiple']+=1
        try:
            require(apply(rows,bad)==reduced,'Changed row operation')
        except ValueError:rejected+=1
        else:raise ValueError('Basis mutation was not rejected')
    # Recurrence fixtures check identities only; not the unbounded proof.
    fixtures=0
    for a in [5,9,17,65,257]:
        x,y=1,0
        for n in range(33):
            require(x*x-(a*a-1)*y*y==1,'Pell norm fixture')
            require((y-n)%(a-1)==0,'Pell index fixture')
            if n:
                v2=lambda k:(k & -k).bit_length()-1
                require(v2(y)==v2(n),'Pell valuation fixture')
            x,y=a*x+(a*a-1)*y,x+a*y
            fixtures+=1
    return {'status':'PASS','graft_retained_rows':146,
            'graft_changed_rows':4,'graft_added_rows':2,
            'row_basis_operations':len(basis['operations']),
            'collected_polynomials':receipts,'rejected_mutations':rejected,
            'pell_fixture_count':fixtures,
            'scope':'Exact finite source, row, expansion and metric checks; unbounded proofs are separate.'}


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--source',type=Path,required=True)
    p.add_argument('--raw',type=Path,required=True)
    p.add_argument('--reduced',type=Path,required=True)
    p.add_argument('--mutations',action='store_true')
    p.add_argument('--receipt',type=Path)
    a=p.parse_args();r=verify(a.source,a.raw,a.reduced,a.mutations)
    s=json.dumps(r,indent=2)+'\n'
    if a.receipt:a.receipt.write_text(s)
    print(s,end='')
