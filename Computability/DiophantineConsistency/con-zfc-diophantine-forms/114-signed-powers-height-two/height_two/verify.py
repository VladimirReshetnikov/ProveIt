#!/usr/bin/env python3
"""Independent certificate checker for the supplied height-two quartic.

No builder code is imported.  Exact polynomial identities recover every
source row, and an ordered-pair convolution independently checks every
coefficient of the complete quartic.  All checks survive python -O.
"""
from __future__ import annotations
import argparse
from collections import Counter, defaultdict
import copy
import hashlib
import json
from pathlib import Path


def check(ok, why):
    if not ok:
        raise ValueError(why)


def poly(terms):
    p = defaultdict(int)
    for c,m in terms:
        check(type(c) is int and all(type(v) is int for v in m), 'integer coefficient/index')
        p[tuple(sorted(m))] += c
    return {m:c for m,c in p.items() if c}


def add_to(p, q, scale=1):
    for m,c in q.items():
        p[m] = p.get(m,0)+scale*c
        if not p[m]:
            del p[m]


def digest(data):
    return hashlib.sha256(data).hexdigest()


def audit(source, equation, cert, expanded):
    n=cert['source_variables']
    s=cert['signal_count']
    u=cert['unit_count']
    sr=source['residuals']
    rr=equation['residuals']
    check(n == len(source['variables']), 'source dimension')
    check(len(equation['variables']) == s+u, 'output dimension')
    check(equation['variables'][:n] == source['variables'], 'source coordinates retained')
    check(equation['domain'] == 'unrestricted integers', 'domain')
    check(len(rr) == u+len(sr)+len(cert['new_products']), 'row count')
    check(poly(rr[0]['terms']) == {(s,):1,():-1}, 'seed unit')
    for i in range(1,u):
        check(poly(rr[i]['terms']) == {(s+i,):1,(s+i-1,s+i-1):-1}, 'unit chain')
    new_prod={p['wire']:tuple(p['monomial']) for p in cert['new_products']}
    check(set(new_prod) == set(range(n,s)), 'new product wire range')
    check(len(set(new_prod.values())) == len(new_prod), 'new product hash-consing')
    for j,(z,m) in enumerate(new_prod.items()):
        check(len(m)==2 and all(0 <= x < n for x in m), 'new product inputs')
        check(poly(rr[u+len(sr)+j]['terms']) == {(z,):1,m:-1}, 'new product definition')
    old_prod={}
    for p in cert['canonical_original_product_producers']:
        z=p['wire']; m=tuple(p['monomial']); i=p['row']
        check(0 <= z < n and len(m)==2 and all(0 <= x < z for x in m), 'original product topology')
        check(poly(sr[i]['terms']) == {(z,):1,m:-1}, 'original product definition')
        check(poly(rr[u+i]['terms']) == {(z,):1,m:-1}, 'retained original product')
        check(m not in old_prod, 'canonical product distinctness')
        old_prod[m]=(z,i)

    def collapse(terms):
        out=defaultdict(int)
        for c,m in terms:
            reduced=[]
            for v in m:
                check(0 <= v < s+u, 'variable index range')
                if v < n:
                    reduced.append(v)
                elif v < s:
                    reduced.extend(new_prod[v])
                # Every unit specializes to one.
            out[tuple(sorted(reduced))] += c
        return {m:c for m,c in out.items() if c}

    identities=0
    for i,rmap in enumerate(cert['row_maps']):
        check(rmap['source_row'] == i, 'source row ordering')
        original=poly(sr[i]['terms'])
        expected=dict(original)
        for repl in rmap['product_replacements']:
            m=tuple(repl['monomial']); z=repl['wire']
            check(m in original and len(m)==2, 'replaced source term')
            if z < n:
                check(old_prod.get(m,(-1,-1))[0] == z, 'original product reference')
                add_to(expected, poly(sr[old_prod[m][1]]['terms']), original[m])
            else:
                check(new_prod.get(z) == m, 'new product reference')
        check(collapse(rr[u+i]['terms']) == expected, ('complete source-row identity',i))
        identities += 1

    # Structural collision certificate.  Private units occur in exactly one
    # source term each.  Raw quadratic products have at most two occurrences.
    unit_occ=Counter(); raw_quad=Counter(); output_occ=Counter(); raw_cubic=Counter()
    for i,row in enumerate(rr[u:u+len(sr)]):
        terms=poly(row['terms'])
        pure=[]; unmasked=[]
        for m,c in terms.items():
            check(abs(c)==1 and 1 <= len(m) <= 2, 'masked source term form')
            units=[v for v in m if v>=s]
            if units:
                check(len(units)==1 and units[0] > s, 'one private unit per masked term')
                unit_occ[units[0]] += 1
            elif len(m)==1:
                check(abs(c)==1, 'unmasked anchor sign')
                z=m[0]; output_occ[z]+=1; unmasked.append(z)
                check(str(i) in cert['source_definition_outputs'] and cert['source_definition_outputs'][str(i)]==z,
                      'unmasked source definition output')
            else:
                check(all(v < n for v in m), 'pure quadratic source input')
                pure.append(m); raw_quad[m]+=1
        check(len(pure)<=1 and len(unmasked)<=1, 'one pure product and output per source row')
        if pure and unmasked:
            z=unmasked[0]; m=pure[0]
            check(max(m)<z, 'pure cubic maximum output')
            raw_cubic[tuple(sorted(m+(z,)))]+=1
    for z,m in new_prod.items():
        output_occ[z]+=1; raw_quad[m]+=1
        raw_cubic[tuple(sorted(m+(z,)))]+=1
    check(unit_occ == Counter({s+i:1 for i in range(1,u)}), 'private unit unique occurrence')
    check(max(output_occ.values(),default=0)==1, 'unmasked signal unique occurrence')
    check(max(raw_quad.values(),default=0)<=2, 'raw quartic square multiplicity')
    check(max(raw_cubic.values(),default=0)<=1, 'raw cubic unique occurrence')
    check(len(cert['unit_uses'])==u-1, 'unit use ledger length')

    # Full exact expansion uses ordered pairs, independently of the builder's
    # upper-triangular squaring loop and its term-order choices.
    full=defaultdict(int)
    for row in rr:
        r=poly(row['terms'])
        check(max(map(len,r),default=0)<=2, 'quadratic row degree')
        for a,c in r.items():
            for b,d in r.items():
                full[tuple(sorted(a+b))] += c*d
    full={m:c for m,c in full.items() if c}
    supplied=poly(expanded['terms'])
    check(len(supplied)==len(expanded['terms']), 'unique supplied monomials')
    check(full==supplied, 'all collected quartic coefficients')
    check(expanded['variables']==s+u, 'expanded dimension')
    check(max(map(len,full))==4, 'exact degree four')
    check(set(full.values())=={-2,1,2}, 'exact coefficient alphabet')
    check(set(v for m in full for v in m)==set(range(s+u)), 'all variables live')
    check(full.get(())==1, 'constant coefficient one')
    metrics=equation['metrics']
    check(metrics['variables']==s+u and metrics['quadratic_rows']==len(rr)
          and metrics['expanded_monomials']==len(full)
          and metrics['max_abs_expanded_coefficient']==2 and metrics['exact_degree']==4,
          'complete measured metrics')
    check(metrics['coefficient_histogram']=={str(k):v for k,v in sorted(Counter(full.values()).items())},
          'coefficient histogram')
    return {'status':'PASS', 'source_row_identities':identities,
            'canonical_original_products':len(old_prod), 'new_product_definitions':len(new_prod),
            'unit_chain_equations':u, 'variables':s+u,
            'quadratic_rows':len(rr), 'quartic_coefficients_checked':len(full),
            'degree':4, 'height':2, 'coefficient_alphabet':[-2,1,2],
            'constant_coefficient':1,
            'zero_set_transfer':'coordinate projection and unique polynomial extension'}


def main():
    ap=argparse.ArgumentParser(); ap.add_argument('directory',type=Path)
    ap.add_argument('--mutations',action='store_true')
    args=ap.parse_args(); d=args.directory
    names=['source.json','equation.json','certificate.json','expanded_polynomial.json']
    raw={name:(d/name).read_bytes() for name in names}
    objects=[json.loads(raw[name]) for name in names]
    build=json.loads((d/'BUILD.json').read_text())
    check(digest(raw['source.json'])==build['source_sha256'],'source hash binding')
    for name in names[1:]:
        check(digest(raw[name])==build[name+'_sha256'], name+' hash binding')
    receipt=audit(*objects)
    if args.mutations:
        mutations=[]
        a=copy.deepcopy(objects); a[1]['residuals'][0]['terms'][1][0]=-2; mutations.append(('unit seed',a))
        a=copy.deepcopy(objects); a[1]['residuals'][1]['terms'][1][0]=1; mutations.append(('unit recurrence sign',a))
        a=copy.deepcopy(objects); a[2]['new_products'][0]['monomial'][0]+=1; mutations.append(('product pullback',a))
        a=copy.deepcopy(objects); a[3]['terms'][0][0]+=1; mutations.append(('expanded coefficient',a))
        a=copy.deepcopy(objects); a[0]['residuals'][0]['terms'][0][0]-=1; mutations.append(('source identity',a))
        a=copy.deepcopy(objects); a[1]['residuals'][a[2]['unit_count']]['terms'][0][0]*=-1; mutations.append(('source row sign',a))
        rejected=[]
        for name,parts in mutations:
            try:
                audit(*parts)
            except (ValueError,KeyError,IndexError):
                rejected.append(name)
            else:
                raise ValueError('corruption accepted: '+name)
        receipt['corruptions_rejected']=rejected
    print(json.dumps(receipt,sort_keys=True,indent=2))


if __name__=='__main__':
    main()
