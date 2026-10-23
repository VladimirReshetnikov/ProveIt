#!/usr/bin/env python3
"""Build the whole compact54-sharp H2082 candidate, without changing reports."""
from pathlib import Path
import gzip
import hashlib
import json
import arithmetic

ROOT = Path(__file__).resolve().parent


def digest(data):
    return hashlib.sha256(data).hexdigest()


def write_json(path, obj):
    path.parent.mkdir(exist_ok=True)
    path.write_text(json.dumps(obj, indent=2) + '\n')


def main():
    config = json.loads((ROOT/'CONFIG.json').read_text())
    fixed = {}
    rows = []
    for natural in [False, True]:
        obj, values = arithmetic.build(False, natural, 'global', 'H2082')
        obj['coherent_tuple'] = config['tuple']
        obj['coefficient_bound_exponent'] = config['height_exponent']
        domain = 'natural' if natural else 'positive'
        name = 'gap2082_' + domain + '.json'
        write_json(ROOT/'generated'/name, obj)
        live = {n['name'] for n in obj['nodes'] if n['kind']=='fixed'}
        for key in live:
            if key in fixed and fixed[key]!=values[key]:
                raise ValueError('fixed value collision')
            fixed[key] = values[key]
        rows.append({'file':name, 'operations':obj['total_operations'],
                     'operation_counts':obj['operation_counts'],
                     'exact_degree':config['exact_degree'], 'domain':domain})
    bindings = []
    (ROOT/'fixed').mkdir(exist_ok=True)
    for name, value in sorted(fixed.items()):
        raw = abs(value).to_bytes(max(1, (abs(value).bit_length()+7)//8), 'little')
        blob = gzip.compress(raw, mtime=0)
        # Canonicalize only generated files; preserve received tuple bytes.
        blob = blob[:9]+b'\xff'+blob[10:]
        path = 'fixed/'+name+'.bin.gz'
        (ROOT/path).write_bytes(blob)
        bindings.append({'name':name, 'path':path,
                         'sign':(value>0)-(value<0), 'bits':abs(value).bit_length(),
                         'raw_bytes':len(raw), 'raw_sha256':digest(raw),
                         'gzip_sha256':digest(blob)})
    write_json(ROOT/'fixed/BINDING.json', {
        'format':'signed unsigned-magnitude little-endian; gzip mtime0 OS255',
        'tuple_binding':'coefficients/COEFFICIENT_BINDING.json',
        'records':bindings, 'live_fixed_leaves':len(bindings),
        'total_raw_bytes':sum(b['raw_bytes'] for b in bindings)})
    write_json(ROOT/'generated/METRICS.json', rows)
    write_json(ROOT/'generated/DEGREE_CERTIFICATE.json', {
        'exact_sparse_identities':3, 'exact_degree':config['exact_degree'],
        'R_degree':4*config['Ecode']-1,
        'N_degree':2*config['threshold_B_power']+config['threshold_b_power'],
        'diagonal_leading_coefficient':'2^186 * base_scale^922760 * threshold_scale^400 > 0',
        'scope':'Exact local cancellation identities, universal degree comparison and nonzero positive leader; source/finalizer degree propagation follows the retained ordinary proof.'})
    print(json.dumps(rows, indent=2))


if __name__=='__main__':
    main()
