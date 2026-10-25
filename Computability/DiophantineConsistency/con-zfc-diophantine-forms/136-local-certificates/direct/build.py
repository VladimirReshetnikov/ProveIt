#!/usr/bin/env python3
"""Build a 306-integer quartic from the pinned 324-integer parent.

Only literal polynomial operations occur here. Unbounded arithmetic is proved
in PROOF.md; this program does not search for a refutation or a zero.
"""
from pathlib import Path
import hashlib
import json
import copy

ROOT = Path(__file__).resolve().parent
PARENT = ROOT / 'parent' / 'integer324-equation.json'
OUT = ROOT / 'integer306'
PIN = '1c5367452a0bd4dd7e9e4bceb1508b62dbd2ff61'

def canonical(x):
    return (json.dumps(x, sort_keys=True, separators=(',', ':'))+'\n').encode()

def digest(x):
    return hashlib.sha256(canonical(x)).hexdigest()

def poly(terms):
    p = {}
    for c, mon in terms:
        m = tuple(sorted(mon))
        p[m] = p.get(m, 0) + c
    return {m:c for m,c in p.items() if c}

def plus(*ps):
    z = {}
    for p in ps:
        for m,c in p.items():
            z[m] = z.get(m,0)+c
    return {m:c for m,c in z.items() if c}

def times(p,q):
    z = {}
    for m,a in p.items():
        for n,b in q.items():
            t = tuple(sorted(m+n))
            z[t] = z.get(t,0)+a*b
    return {m:c for m,c in z.items() if c}

def neg(p):
    return {m:-c for m,c in p.items()}

def terms(p):
    return [[c,list(m)] for m,c in sorted(p.items()) if c]

def var(i):
    return {(i,):1}

def write(path,data):
    path.parent.mkdir(parents=True,exist_ok=True)
    path.write_bytes(canonical(data))

def main():
    old = json.loads(PARENT.read_text())
    if len(old['variables']) != 324 or len(old['residuals']) != 208:
        raise ValueError('Unexpected parent dimensions')
    names = {v['name']:i for i,v in enumerate(old['variables'])}
    old_guard_ids = list(range(3,12))
    dropped = sorted(names[f'guard{g}.{a}'] for g in old_guard_ids for a in 'abc')
    removed_rows = [i for i,r in enumerate(old['residuals'])
                    if r['label'] in {f'domain_guard.{g}' for g in old_guard_ids}]
    if len(dropped) != 27 or len(removed_rows) != 9:
        raise ValueError('Guard inventory changed')
    keep = [i for i in range(324) if i not in dropped]
    rename = {i:j for j,i in enumerate(keep)}
    def remap(p):
        return {tuple(sorted(rename[i] for i in m)):c for m,c in p.items()}
    selected = ['index3.X','index5.X','index6.X','index7.X','index8.X',
                'index10.X','index11.X','index13.X','index14.X']
    x_indices = [names[n] for n in selected]
    orientation = plus({():9}, *[neg(var(i)) for i in x_indices])
    rows = []
    row_map = []
    pool_old = None
    for i,r in enumerate(old['residuals']):
        if i in removed_rows:
            continue
        p = poly(r['terms'])
        if r['label'] == 'cap.pooled_index_residue':
            if pool_old is not None:
                raise ValueError('Duplicate pool row')
            pool_old = i
            p = plus(p,orientation)
        rows.append({'label':r['label'],'terms':terms(remap(p))})
        row_map.append([i,len(rows)-1])
    if pool_old is None:
        raise ValueError('Missing pooled index row')
    vs = [copy.deepcopy(old['variables'][i]) for i in keep]
    # The final centered chart has requested indices
    # k_a=z10-1, k_b=z11, ..., k_vq=z17, k_index=z18.
    requested = [plus(var(rename[names['crt.encoded.a']]),{():-1})]
    requested += [var(rename[names['crt.encoded.'+a]]) for a in
                  ['b','c','d','S','Sp','u','vq']]
    products = []
    previous = requested[0]
    for j in range(1,7):
        i = len(vs)
        vs.append({'name':f'orientation.P{j+1}','kind':'gate'})
        rows.append({'label':f'orientation.product_{j+1}',
                     'terms':terms(plus(var(i),neg(times(previous,requested[j]))))})
        products.append(i)
        previous = var(i)
    triple = list(range(len(vs),len(vs)+3))
    vs += [{'name':f'orientation.positive_product.{a}','kind':'integer_guard'}
           for a in 'abc']
    a,b,c = triple
    fused = plus(times(previous,requested[7]), {():-1},
                 {(a,a):-1,(b,b):-1,(c,c):-1,(c,):-1})
    rows.append({'label':'orientation.fused_strict_product','terms':terms(fused)})
    new = {'schema':old['schema'],'domain':'unrestricted integers',
           'polynomial':'sum of squares of all listed residuals',
           'source_commit':PIN,'variant':'linear_orientation_pool_integer306',
           'variables':vs,'residuals':rows}
    expanded = {}
    for r in rows:
        p = poly(r['terms'])
        if max(map(len,p),default=0)>2:
            raise ValueError('Nonquadratic row')
        expanded = plus(expanded,times(p,p))
    metrics = {'variables':len(vs),'residuals':len(rows),
               'degree':max(map(len,expanded)),
               'monomials':len(expanded),
               'coefficient_height':max(map(abs,expanded.values())),
               'residual_height':max(abs(c) for r in rows for c,m in r['terms'])}
    certificate = {
        'schema':'linear_orientation_guard_compression_v1',
        'parent_canonical_sha256':digest(old),
        'output_canonical_sha256':digest(new),
        'domain':'unrestricted integers',
        'removed_parent_rows':removed_rows,
        'removed_parent_variables':dropped,
        'retained_parent_variables':keep,
        'retained_row_map':row_map,
        'pool_parent_row':pool_old,
        'pool_output_row':dict(row_map)[pool_old],
        'orientation_parent_terms':terms(orientation),
        'selected_parent_abscissas':x_indices,
        'selected_seed_names':selected,
        'private_pool_quotient_parent_index':names['cap.pooled_quotient'],
        'requested_eight_output_terms':[terms(p) for p in requested],
        'product_output_variables':products,
        'strict_product_output_triple':triple,
        'unbounded_proof':'../PROOF.md',
        'quotient_map':'q_new=q_old+sum(1-Xi)/(A-1); inverse subtracts this integer',
        'guard_map':'Restore each deleted nonnegative scalar with a fresh ternary Legendre triple.'}
    write(OUT/'equation.json',new)
    write(OUT/'expanded_polynomial.json',{'variables':len(vs),'terms':terms(expanded)})
    write(OUT/'transformation_certificate.json',certificate)
    write(OUT/'METRICS.json',metrics)
    with (OUT/'residuals.txt').open('w') as f:
        f.write('Domain: all 306 coordinates range independently over Z.\n')
        f.write('P = sum_{j=0}^{205} r_j^2.  The equation is P=0.\n\n')
        for j,r in enumerate(rows):
            pieces=[]
            for c,m in r['terms']:
                mon='*'.join('z'+str(i) for i in m)
                pieces.append(f'{c:+d}'+('*'+mon if mon else ''))
            f.write(f'r{j} [{r["label"]}] = '+ ' '.join(pieces)+'\n')
    with (OUT/'variables.tsv').open('w') as f:
        f.write('index\tname\tkind\n')
        for i,v in enumerate(vs):
            f.write(f'{i}\t{v["name"]}\t{v["kind"]}\n')
    print(json.dumps(metrics,indent=2))

if __name__ == '__main__':
    main()
