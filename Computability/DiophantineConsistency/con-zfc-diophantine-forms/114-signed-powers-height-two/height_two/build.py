#!/usr/bin/env python3
"""Compile a literal quadratic SOS system to a coefficient-height-two quartic.

The construction is entirely over unrestricted integers.  It preserves the
old coordinates, adds product wires and private units, and never uses a
truth-dependent coefficient.  Run ``python build.py SOURCE OUTDIR``.
"""
from __future__ import annotations
import argparse
import collections
import hashlib
import json
from pathlib import Path


def require(ok, message):
    if not ok:
        raise ValueError(message)


def canonical(terms):
    result = collections.defaultdict(int)
    for c, m in terms:
        result[tuple(sorted(m))] += c
    return {m: c for m, c in result.items() if c}


def expand_squares(rows):
    out = collections.defaultdict(int)
    for row in rows:
        terms = list(canonical(row['terms']).items())
        for i, (m, c) in enumerate(terms):
            for j in range(i, len(terms)):
                n, d = terms[j]
                out[tuple(sorted(m+n))] += c*d*(1 if i == j else 2)
    return {m: c for m, c in out.items() if c}


def dump(path, obj):
    path.write_text(json.dumps(obj, sort_keys=True, separators=(',', ':'))+'\n')


def sha(data):
    return hashlib.sha256(data).hexdigest()


def compile_system(source, anchor_linear=False):
    variables = [dict(v) for v in source['variables']]
    n = len(variables)
    rows = source['residuals']
    require(all(len(m) <= 2 for r in rows for c,m in r['terms']), 'quadratic source required')
    # A source gate output is used without a unit mask only in its unique
    # triangular definition.  All other linear occurrences are masked.
    outputs = {}
    used_outputs = set()
    producers = {}
    for i, row in enumerate(rows):
        if row['label'] not in ('addition', 'multiplication'):
            continue
        candidates = [m[0] for c,m in row['terms']
                      if c == 1 and len(m) == 1 and variables[m[0]]['kind'] == 'gate']
        require(len(candidates) == 1, ('gate output', i, candidates))
        z = candidates[0]
        require(z not in used_outputs, ('repeated output', z))
        require(all(j < z for c,m in row['terms'] if m != [z] for j in m),
                ('nontriangular source definition', i, z))
        outputs[i] = z
        used_outputs.add(z)
        if len(row['terms']) == 2:
            for c,m in row['terms']:
                if c == -1 and len(m) == 2:
                    producers.setdefault(tuple(m), (z, i))

    freq = collections.Counter(tuple(m) for r in rows for c,m in r['terms'] if len(m) == 2)
    chosen = {}
    for i, row in enumerate(rows):
        options = []
        for c,m in row['terms']:
            if abs(c) != 1 or len(m) != 2:
                continue
            t = tuple(m)
            if t in producers and producers[t][1] == i:
                options = [t]
                break
            if freq[t] <= 2:
                options.append(t)
        if options:
            chosen[i] = options[0]

    if anchor_linear:
        # A further source linear term can remain unmasked when its signal
        # has no other unmasked occurrence.  If a raw product is retained in
        # that row, the chosen signal must be strictly later than both inputs.
        # This is only a coefficient simplification; no variable is eliminated.
        for i,row in enumerate(rows):
            if i in outputs:
                continue
            for c,m in row['terms']:
                if (abs(c)==1 and len(m)==1 and m[0] not in used_outputs
                        and (i not in chosen or max(chosen[i]) < m[0])):
                    outputs[i]=m[0]
                    used_outputs.add(m[0])
                    break

    # Any product used by more than two original rows is kept literally only
    # at its canonical original producer; all other uses share that wire.
    product_wires = {m: z for m,(z,i) in producers.items()}
    new_products = []
    def product(m):
        m = tuple(m)
        if m not in product_wires:
            z = len(variables)
            variables.append({'kind':'product_wire', 'name':f'product.{len(new_products)}'})
            product_wires[m] = z
            new_products.append((z, m))
        return product_wires[m]
    transformed = []
    row_maps = []
    masks = []
    # Temporary unit identifiers are negative.  Resolve them after all signal
    # wires have been allocated so the namespaces remain disjoint.
    def unit(kind, origin):
        masks.append({'use':kind, 'origin':origin})
        return -len(masks)-1  # u_1=-2, while seed u_0=-1
    for i, row in enumerate(rows):
        terms = []
        replacements = []
        for c, old_m in row['terms']:
            m = tuple(old_m)
            if len(m) == 2 and chosen.get(i) != m:
                z = product(m)
                replacements.append({'monomial':list(m), 'wire':z})
                m = (z,)
            if len(m) == 2:
                require(abs(c) == 1, 'retained quadratic coefficient')
                terms.append([c, list(m)])
            elif len(m) == 1 and outputs.get(i) == m[0] and abs(c) == 1:
                terms.append([c, list(m)])
            else:
                for occurrence in range(abs(c)):
                    u = unit('constant' if not m else 'linear', [i, list(old_m), occurrence])
                    terms.append([1 if c > 0 else -1, list(m)+( [u] )])
        transformed.append({'label':f'source.{i}:{row["label"]}', 'terms':terms})
        row_maps.append({'source_row':i, 'output':outputs.get(i),
                         'kept_quadratic':list(chosen[i]) if i in chosen else None,
                         'product_replacements':replacements})

    # A product newly introduced after a different retained occurrence gives
    # two copies of its squared monomial, never three.  Verify that structural
    # invariant independently of the eventual coefficient collection.
    pure_counts = collections.Counter(chosen.values())
    pure_counts.update(m for z,m in new_products)
    require(max(pure_counts.values(), default=0) <= 2, 'pure product multiplicity')
    for z,m in new_products:
        transformed.append({'label':f'product.{z}', 'terms':[[1,[z]],[-1,list(m)]]})

    signal_count = len(variables)
    unit_count = len(masks)+1
    variables += [{'kind':'unit_seed' if i == 0 else 'private_unit', 'name':f'unit.{i}'}
                  for i in range(unit_count)]
    def resolve(v):
        return signal_count + (-v-1) if v < 0 else v
    for row in transformed:
        row['terms'] = [[c, sorted(resolve(v) for v in m)] for c,m in row['terms']]
    unit_rows = [{'label':'unit.seed', 'terms':[[1,[signal_count]],[-1,[]]]}]
    for i in range(1,unit_count):
        unit_rows.append({'label':f'unit.{i}', 'terms':[[1,[signal_count+i]],
                          [-1,[signal_count+i-1,signal_count+i-1]]]})
    result_rows = unit_rows + transformed
    expanded = expand_squares(result_rows)
    height = max(map(abs, expanded.values()))
    degree = max(map(len, expanded))
    require(height == 2, ('coefficient height', height))
    require(degree == 4, ('degree', degree))
    require(set(v for m in expanded for v in m) == set(range(len(variables))), 'unused variable')
    metrics = {'variables':len(variables), 'source_variables':n,
               'new_product_wires':len(new_products), 'private_unit_uses':len(masks),
               'unit_variables':unit_count, 'source_rows':len(rows),
               'quadratic_rows':len(result_rows), 'expanded_monomials':len(expanded),
               'exact_degree':degree, 'max_abs_expanded_coefficient':height,
               'coefficient_histogram':dict(sorted(collections.Counter(expanded.values()).items()))}
    result = {'schema':'quadratic_sum_squares_v1', 'domain':'unrestricted integers',
              'variant':'private_units_height_two'+('_anchored' if anchor_linear else ''), 'variables':variables,
              'residuals':result_rows, 'metrics':metrics}
    certificate = {'schema':'height_two_units_certificate_v1', 'source_variables':n,
                   'signal_count':signal_count, 'unit_count':unit_count,
                   'source_definition_outputs':outputs,
                   'canonical_original_product_producers':[
                       {'monomial':list(m), 'wire':z, 'row':i} for m,(z,i) in sorted(producers.items())],
                   'new_products':[{'wire':z,'monomial':list(m)} for z,m in new_products],
                   'row_maps':row_maps, 'unit_uses':masks,
                   'pure_quadratic_occurrence_bound':max(pure_counts.values(),default=0)}
    polynomial = {'schema':'sparse_integer_polynomial_v1', 'variables':len(variables),
                  'terms':[[c,list(m)] for m,c in sorted(expanded.items())]}
    return result, certificate, polynomial


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('source',type=Path)
    parser.add_argument('output',type=Path)
    parser.add_argument('--anchor-linear',action='store_true')
    args=parser.parse_args()
    raw=args.source.read_bytes()
    src=json.loads(raw)
    result, certificate, polynomial=compile_system(src,args.anchor_linear)
    args.output.mkdir(parents=True,exist_ok=True)
    (args.output/'source.json').write_bytes(raw)
    dump(args.output/'equation.json',result)
    dump(args.output/'certificate.json',certificate)
    dump(args.output/'expanded_polynomial.json',polynomial)
    receipt={'source_sha256':sha(raw),'metrics':result['metrics']}
    for name in ('equation.json','certificate.json','expanded_polynomial.json'):
        receipt[name+'_sha256']=sha((args.output/name).read_bytes())
    dump(args.output/'BUILD.json',receipt)
    print(json.dumps(receipt,indent=2))


if __name__ == '__main__':
    main()
