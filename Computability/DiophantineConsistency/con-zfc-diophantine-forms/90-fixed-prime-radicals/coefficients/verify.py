#!/usr/bin/env python3
"""Reconstruct and bind every fixed numeral of the integer equations.

This executes only the finite source-34 coefficient recipe. It does not
simulate the machine to halting or test consistency. Python standard library.
"""
from pathlib import Path
import gzip
import hashlib
import importlib.util
import json

HERE = Path(__file__).resolve().parent
PORT_MAP = {'beta': 'beta', 'K0': 'K', 'MC': 'MC', 'MF': 'MF_source'}


def require(ok, description):
    if not ok:
        raise RuntimeError(description)


def verify():
    binding = json.loads((HERE/'BINDING.json').read_text())
    inherited = json.loads((HERE.parent/'inherited/PAYLOAD_BINDING.json').read_text())
    spec = importlib.util.spec_from_file_location('finite_source34', HERE/'source34/build_coefficients.py')
    source = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(source)
    rebuilt, audit = source.construct()
    values = {name: rebuilt[old] for name, old in PORT_MAP.items()}
    values.update(cone_A=1 << 1113, cone_B=1 << 666104)
    require(set(binding['ports']) == set(values), 'exact six fixed numerals')
    summaries = {}
    for name, value in values.items():
        entry = binding['ports'][name]
        require(entry['file'] == 'payloads/'+name+'.bin.gz', 'fixed payload path '+name)
        packed = (HERE/entry['file']).read_bytes()
        raw = gzip.decompress(packed)
        canonical = value.to_bytes((value.bit_length()+7)//8, 'little')
        require(raw == canonical, 'byte-identical finite reconstruction '+name)
        require(hashlib.sha256(raw).hexdigest() == entry['sha256_raw'], 'raw hash '+name)
        require(hashlib.sha256(packed).hexdigest() == entry['sha256_gzip'], 'compressed hash '+name)
        require(len(raw) == entry['raw_bytes'] and value.bit_length() == entry['bits'], 'size '+name)
        if name in PORT_MAP:
            old = inherited['payloads'][PORT_MAP[name]]
            require(entry['sha256_raw'] == old['sha256'], 'inherited tuple identity '+name)
            require(entry['sha256_gzip'] == old['gzip_sha256'], 'inherited compressed identity '+name)
        summaries[name] = {'bits': value.bit_length(), 'raw_bytes': len(raw),
                           'sha256_raw': entry['sha256_raw'], 'reconstruction': 'PASS'}
    require(values['beta'] == (1 << 1064921)-1, 'literal beta')
    # JSON object keys are strings; the finite Python recipe uses integers
    # for prime factors and modular orders.
    require(json.loads(json.dumps(audit)) == inherited['audit'], 'all inherited finite recipe audits')
    return {'status': 'PASS', 'coherent_tuple': binding['coherent_tuple'],
            'raw_bytes': sum(x['raw_bytes'] for x in summaries.values()),
            'fixed_numerals': summaries, 'finite_recipe_audit': audit,
            'scope': 'Exact finite coefficient reconstruction and source binding; no unbounded simulation.'}


if __name__ == '__main__':
    result = verify()
    (HERE/'VERIFICATION.json').write_text(json.dumps(result, indent=2, sort_keys=True)+'\n')
    print(json.dumps(result, indent=2, sort_keys=True))
