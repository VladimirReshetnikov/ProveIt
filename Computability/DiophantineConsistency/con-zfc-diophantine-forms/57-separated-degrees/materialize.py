#!/usr/bin/env python3
"""Materialize every nonliteral coefficient leaf of the delivered 9/10 DAGs.

Native ports are authenticated before use. Signed coefficients are represented
by a sign and a gzip-compressed unsigned little-endian magnitude. Powers of two
are also written in full; there is no oracle or consistency-dependent choice.
"""
from pathlib import Path
from hashlib import sha256
import gzip
import json

ROOT = Path(__file__).resolve().parent


def require(value, label):
    if not value:
        raise ValueError(label)


def native_ports():
    binding = json.loads((ROOT / 'coefficients/COEFFICIENT_BINDING.json').read_text())
    values = {}
    for r in binding['materialization']['files']:
        packed = (ROOT / 'coefficients' / r['file']).read_bytes()
        raw = gzip.decompress(packed)
        require(sha256(packed).hexdigest() == r['gzip_sha256'], 'native gzip hash')
        require(sha256(raw).hexdigest() == r['sha256'], 'native raw hash')
        values[r['port']] = int.from_bytes(raw, 'little')
        require(values[r['port']].bit_length() == r['bits'], 'native bit length')
    return [values[n] for n in ('beta', 'K', 'MC', 'MF_source')]


def recipe_value(recipe, ports):
    total = 0
    for term in recipe:
        value = term['coefficient']
        for port, exponent in zip(ports, term['powers']):
            value *= port ** exponent
        total += value
    return total


def main():
    ports = native_ports()
    values, recipes = {}, {}
    for label in ('nine_positive', 'nine_natural', 'ten_integer'):
        body = json.loads((ROOT / 'generated' / (label + '.json')).read_text())
        for r in body['coefficient_recipes']:
            if r['name'] in recipes:
                require(recipes[r['name']] == r['terms'], 'incompatible recipe names')
            recipes[r['name']] = r['terms']
        for name, field in [('base_scale', 'base_scale_exponent'),
                            ('threshold_scale', 'threshold_scale_exponent'),
                            ('mask_scale', 'mask_scale_exponent')]:
            if field in body:
                value = 1 << body[field]
                require(name not in values or values[name] == value, 'scale mismatch')
                values[name] = value
    values.update({name: recipe_value(r, ports) for name, r in recipes.items()})
    out = ROOT / 'fixed'
    out.mkdir(exist_ok=True)
    records = []
    for name, value in sorted(values.items()):
        magnitude = abs(value)
        raw = magnitude.to_bytes(max(1, (magnitude.bit_length()+7)//8), 'little')
        packed = gzip.compress(raw, compresslevel=9, mtime=0)
        filename = name + '.bin.gz'
        (out / filename).write_bytes(packed)
        record = dict(name=name, file=filename, sign=(value > 0)-(value < 0),
                      bits=magnitude.bit_length(), raw_bytes=len(raw),
                      gzip_bytes=len(packed), sha256=sha256(raw).hexdigest(),
                      gzip_sha256=sha256(packed).hexdigest())
        if name in recipes:
            record['recipe'] = recipes[name]
        else:
            record['power_of_two_exponent'] = magnitude.bit_length()-1
        records.append(record)
    manifest = dict(schema='signed-fixed-coefficients-v1',
                    native_binding='../coefficients/COEFFICIENT_BINDING.json',
                    encoding='sign times unsigned little-endian magnitude',
                    files=records,
                    total_raw_bytes=sum(r['raw_bytes'] for r in records),
                    total_gzip_bytes=sum(r['gzip_bytes'] for r in records))
    (out / 'FIXED_BINDING.json').write_text(json.dumps(manifest, indent=2)+'\n')
    print(json.dumps({k: v for k, v in manifest.items() if k != 'files'}, indent=2))
    print('Materialized coefficient leaves:', len(records))


if __name__ == '__main__':
    main()
