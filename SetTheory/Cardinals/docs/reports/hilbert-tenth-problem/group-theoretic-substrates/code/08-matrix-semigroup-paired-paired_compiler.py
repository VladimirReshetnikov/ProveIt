#!/usr/bin/env python3
"""Authored bounded normal-form Diophantine compiler. Standard library only.

Reads pinned numerical JSON, never imports or executes the source compiler.
A polynomial is a literal sum of squares of sparse integer residuals.
"""
import argparse
import hashlib
import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent
SOURCE_SHA256 = '506144b361b2bea634d468a94921644d91868dc089a257fe289a0bf51b74cec9'
DEFAULT_SOURCE = ROOT / 'data/semigroup.json'
M = 114
I2 = ((1, 0), (0, 1))
P = ((1, 2), (0, 1))


def require(ok, message):
    if not ok:
        raise ValueError(message)


def matrix(a, size=2):
    require(isinstance(a, (list, tuple)) and len(a) == size and
            all(isinstance(row, (list, tuple)) and len(row) == size for row in a),
            'Wrong matrix shape')
    require(all(type(v) is int for row in a for v in row), 'Matrix entries must be integers, not booleans')
    return tuple(tuple(row) for row in a)


def multiply(a, b):
    """Exactly eight scalar multiplications and four additions for 2x2 inputs."""
    return tuple(tuple(a[i][0]*b[0][j] + a[i][1]*b[1][j]
                       for j in range(2)) for i in range(2))


def inverse(a):
    require(a[0][0]*a[1][1]-a[0][1]*a[1][0] == 1, 'Expected SL2 matrix')
    return ((a[1][1], -a[0][1]), (-a[1][0], a[0][0]))


def block(a, b=P):
    return ((a[0][0], a[0][1], 0, 0), (a[1][0], a[1][1], 0, 0),
            (0, 0, b[0][0], b[0][1]), (0, 0, b[1][0], b[1][1]))


def target_upper(full):
    """Validate the interface domain diag(T,P); no claim about other targets."""
    full = matrix(full, 4)
    top = tuple(row[:2] for row in full[:2])
    require(full == block(top), 'Target is outside the diag(T,P) interface')
    return top


def load_constants(path=DEFAULT_SOURCE):
    raw = Path(path).read_bytes()
    require(hashlib.sha256(raw).hexdigest() == SOURCE_SHA256, 'Fixed numerical source hash mismatch')
    source = json.loads(raw)
    entries = source['generators']
    require([g['name'] for g in entries] ==
            [f'A{i}' for i in range(1,M+1)] + [f'B{i}' for i in range(1,M+1)] + ['C'],
            'Generator order mismatch')
    gen = {g['name']:matrix(g['matrix'],4) for g in entries}
    for a in gen.values():
        require(all(a[i][j] == 0 for i in range(4) for j in range(4) if (i<2)!=(j<2)),
                'Off-diagonal block')
        inverse(tuple(row[:2] for row in a[:2]))
        inverse(tuple(row[2:] for row in a[2:]))
    top = lambda a: tuple(row[:2] for row in a[:2])
    h = tuple(top(gen[f'A{i}']) for i in range(1,M+1))
    g = tuple(inverse(top(gen[f'B{i}'])) for i in range(1,M+1))
    c = top(gen['C'])
    require(tuple(row[2:] for row in gen['C'][2:]) == P, 'Marker matrix mismatch')
    return {'h':h, 'g':g, 'c':c, 'generators':gen, 'source_sha256':SOURCE_SHA256}


def selector(s, i):
    return f'e_{s}_{i}'


def part(z, s, a, b, sign):
    return f'{z}_{s}_{a}{b}_{sign}'


def add(poly, coeff, *names):
    if not coeff:
        return
    mon = tuple(sorted(names))
    poly[mon] = poly.get(mon, 0) + coeff
    if poly[mon] == 0:
        del poly[mon]


def signed_terms(z, s, a, b):
    if s == 0:
        return [(int(a==b), ())] if a==b else []
    return [(1,(part(z,s,a,b,'p'),)),(-1,(part(z,s,a,b,'n'),))]


def t_terms(mode, a, b):
    return [(1,(f'T_{a}{b}',))] if mode == 'signed' else [
        (1,(f'T_{a}{b}_p',)),(-1,(f'T_{a}{b}_n',))]


def check_parameters(r, mode):
    require(type(r) is int and r >= 0, 'r must be a fixed nonnegative integer')
    require(mode in ('signed', 'natural'), 'Unknown target mode')


def auxiliary_names(r):
    check_parameters(r, 'signed')
    for s in range(1,r+1):
        yield from (selector(s,i) for i in range(1,M+1))
        yield from (part(z,s,a,b,sign) for z in ('H','G') for a in range(2)
                    for b in range(2) for sign in ('p','n'))


def external_names(mode):
    check_parameters(0, mode)
    for a in range(2):
        for b in range(2):
            if mode == 'signed':
                yield f'T_{a}{b}'
            else:
                yield f'T_{a}{b}_p'
                yield f'T_{a}{b}_n'


def residuals(constants, r, mode='signed'):
    """Stream (name, sparse residual). Monomials are tuples of variable names."""
    check_parameters(r, mode)
    for s in range(1,r+1):
        q = {():-1}
        for i in range(1,M+1):
            add(q,1,selector(s,i))
        yield f'select_{s}',q
        for z in ('H','G'):
            mats = constants[z.lower()]
            for a in range(2):
                for b in range(2):
                    q = {}
                    for v,mon in signed_terms(z,s,a,b):
                        add(q,v,*mon)
                    for i,tile in enumerate(mats,1):
                        for k in range(2):
                            for v,mon in signed_terms(z,s-1,a,k):
                                add(q,-v*tile[k][b],selector(s,i),*mon)
                    yield f'update_{z}_{s}_{a}{b}',q
        for z in ('H','G'):
            for a in range(2):
                for b in range(2):
                    yield f'canonical_{z}_{s}_{a}{b}', {
                        tuple(sorted((part(z,s,a,b,'p'),part(z,s,a,b,'n')))):1}
    for a in range(2):
        for b in range(2):
            q = {}
            for k in range(2):
                for v,mon in signed_terms('H',r,a,k):
                    add(q,v*constants['c'][k][b],*mon)
                for t,tmon in t_terms(mode,a,k):
                    for g,gmon in signed_terms('G',r,k,b):
                        add(q,-t*g,*tmon,*gmon)
            yield f'terminal_{a}{b}',q
    if mode == 'natural':
        for a in range(2):
            for b in range(2):
                yield f'canonical_T_{a}{b}', {(f'T_{a}{b}_n',f'T_{a}{b}_p'):1}


def evaluate_poly(q, values):
    """Unoptimized evaluator whose exact arithmetic counts are in ledger()."""
    total = 0
    for mon, coeff in q.items():
        product = 1
        for name in mon:
            product *= values[name]
        total += coeff*product
    return total


def validate_values(r, mode, values):
    require(type(values) is dict, 'Expected a variable assignment dictionary')
    aux, ext = set(auxiliary_names(r)),set(external_names(mode))
    require(set(values) == aux|ext, 'Missing or unexpected variables')
    require(all(type(v) is int for v in values.values()), 'Assignments must be integers, not booleans')
    require(all(values[n]>=0 for n in aux), 'Auxiliaries must be natural (including zero)')
    if mode == 'natural':
        require(all(values[n]>=0 for n in ext), 'Natural target inputs must be nonnegative')


def evaluate(constants, r, values, mode='signed', failures_limit=8):
    validate_values(r,mode,values)
    total, count, failed, maximum = 0,0,[],0
    for name,q in residuals(constants,r,mode):
        value = evaluate_poly(q,values)
        count += 1
        maximum = max(maximum,abs(value).bit_length())
        total += value*value
        if value and len(failed)<failures_limit:
            failed.append({'residual':name,'value':value})
    return {'sos':total,'zero':total==0,'residual_count':count,
            'first_failures':failed,'maximum_residual_magnitude_bits':maximum}


def target_values(target, mode='signed'):
    check_parameters(0,mode)
    target = matrix(target)
    out = {}
    for a in range(2):
        for b in range(2):
            v = target[a][b]
            if mode == 'signed':
                out[f'T_{a}{b}'] = v
            else:
                out[f'T_{a}{b}_p'],out[f'T_{a}{b}_n'] = max(v,0),max(-v,0)
    return out


def certificate(constants, sequence, target=None, mode='signed'):
    check_parameters(0,mode)
    require(isinstance(sequence,(list,tuple)) and all(type(i) is int and 1<=i<=M for i in sequence),
            'Tile sequence must contain indices 1..114')
    out, h, g = {},I2,I2
    for s,i in enumerate(sequence,1):
        out.update({selector(s,j):int(i==j) for j in range(1,M+1)})
        h,g = multiply(h,constants['h'][i-1]),multiply(g,constants['g'][i-1])
        for z,mat in [('H',h),('G',g)]:
            for a in range(2):
                for b in range(2):
                    v = mat[a][b]
                    out[part(z,s,a,b,'p')],out[part(z,s,a,b,'n')] = max(v,0),max(-v,0)
    target = multiply(multiply(h,constants['c']),inverse(g)) if target is None else matrix(target)
    out.update(target_values(target,mode))
    return {'schema':'paired-matrix-certificate-v1','source_sha256':SOURCE_SHA256,
            'r':len(sequence),'mode':mode,'sequence':list(sequence),'target':[list(row) for row in target],
            'values':out}


def ledger(constants, r, mode='signed'):
    """Counts are reconstructed from emitted residuals, not asserted formulas."""
    check_parameters(r,mode)
    count, degrees, monomials, coeffmax = 0,{},[0,0,0],0
    used = set()
    for _,q in residuals(constants,r,mode):
        count += 1
        degree = max(map(len,q),default=0)
        degrees[str(degree)] = degrees.get(str(degree),0)+1
        for mon,c in q.items():
            monomials[len(mon)] += 1
            coeffmax = max(coeffmax,abs(c))
            used.update(mon)
    n = sum(monomials)
    return {'schema':'paired-matrix-ledger-v1','source_sha256':SOURCE_SHA256,'r':r,'mode':mode,
            'inner_tile_alphabet':M,'generator_word_length':2*r+1,
            'natural_auxiliary_count':len(list(auxiliary_names(r))),
            'external_input_count':len(list(external_names(mode))),
            'external_domain':'Z' if mode=='signed' else 'N',
            'residual_count':count,'residual_degree_histogram':degrees,
            'sos_total_degree':2*max(map(int,degrees)),
            'literal_residual_monomials_by_degree':monomials,
            'literal_residual_monomials_total':n,'maximum_residual_coefficient_absolute':coeffmax,
            'maximum_residual_coefficient_magnitude_bits':coeffmax.bit_length(),
            'distinct_variables_in_residuals':len(used),
            'generic_sparse_evaluator_multiplications':sum(d*k for d,k in enumerate(monomials))+n+count,
            'generic_sparse_evaluator_additions':n+count,
            'evaluation_count_convention':'Start each monomial product at 1; multiply once per variable, once by coefficient; add each monomial; square each residual and add each square. No optimizations; excludes validation, comparisons, lookups, loop/control, parsing and polynomial construction.'}


def export(constants, r, mode='signed'):
    check_parameters(r,mode)
    return {'schema':'literal-sparse-integer-sos-v1','source_sha256':SOURCE_SHA256,
            'r':r,'mode':mode,'external_variables':list(external_names(mode)),
            'natural_auxiliary_variables':list(auxiliary_names(r)),
            'meaning':'F = sum(residual.polynomial ** 2); each polynomial is sum(coefficient * product(variables))',
            'residuals':[{'name':name,'polynomial':[{'coefficient':c,'variables':list(mon)}
                         for mon,c in sorted(q.items())]} for name,q in residuals(constants,r,mode)],
            'ledger':ledger(constants,r,mode)}


def main():
    if hasattr(sys,'set_int_max_str_digits'):
        sys.set_int_max_str_digits(0)
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--source',default=str(DEFAULT_SOURCE))
    sub = parser.add_subparsers(dest='command',required=True)
    for name in ('export','ledger'):
        p = sub.add_parser(name); p.add_argument('r',type=int)
        p.add_argument('--mode',choices=['signed','natural'],default='signed')
    p = sub.add_parser('certificate'); p.add_argument('sequence',help='JSON array of tile IDs')
    p.add_argument('--target',help='JSON signed 2x2 integer matrix; defaults to product target')
    p.add_argument('--mode',choices=['signed','natural'],default='signed')
    p = sub.add_parser('verify'); p.add_argument('certificate_file')
    args = parser.parse_args(); constants = load_constants(args.source)
    if args.command == 'export':
        result = export(constants,args.r,args.mode)
    elif args.command == 'ledger':
        result = ledger(constants,args.r,args.mode)
    elif args.command == 'certificate':
        result = certificate(constants,json.loads(args.sequence),None if args.target is None else json.loads(args.target),args.mode)
    else:
        cert = json.loads(Path(args.certificate_file).read_text())
        require(cert.get('source_sha256') == SOURCE_SHA256,'Certificate source mismatch')
        require(cert.get('schema') == 'paired-matrix-certificate-v1','Certificate schema mismatch')
        check_parameters(cert['r'],cert['mode'])
        require(len(cert['sequence']) == cert['r'],'Certificate sequence length mismatch')
        expected = certificate(constants,cert['sequence'],cert['target'],cert['mode'])
        require(cert['values'] == expected['values'],'Certificate auxiliary data or target differs from the encoded sequence')
        result = evaluate(constants,cert['r'],cert['values'],cert['mode'])
    print(json.dumps(result,indent=2,sort_keys=True))
    return 0 if args.command!='verify' or result['zero'] else 1


if __name__ == '__main__':
    raise SystemExit(main())
