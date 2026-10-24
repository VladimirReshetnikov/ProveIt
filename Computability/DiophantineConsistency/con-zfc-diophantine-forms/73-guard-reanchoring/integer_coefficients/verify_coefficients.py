#!/usr/bin/env python3
"""Decode the actual payloads independently of the constructor; standard library."""
import gzip
import json
from provenance import (ROOT, require, sha256, verify_sources, load_source34,
                        make_binding, write_json)


def main():
    source_count = verify_sources()
    inherited_raw = (ROOT/'upstream'/'source34'/'PAYLOAD_BINDING.json').read_bytes()
    inherited = json.loads(inherited_raw)
    payload_dir = ROOT/'payloads'
    require((payload_dir/'COEFFICIENT_BINDING.json').read_bytes() == inherited_raw,
            'active payload manifest is the authentic complete source manifest')
    raw_values = {}
    for name,expected in inherited['payloads'].items():
        raw = (payload_dir/(name+'.bin')).read_bytes()
        compressed = (payload_dir/(name+'.bin.gz')).read_bytes()
        require(gzip.decompress(compressed) == raw, 'gzip round trip: '+name)
        require(sha256(raw) == expected['sha256'], 'upstream raw hash: '+name)
        require(sha256(compressed) == expected['gzip_sha256'], 'upstream gzip hash: '+name)
        value = int.from_bytes(raw, 'little')
        require(value.bit_length() == expected['bits'], 'exact bitlength: '+name)
        require(len(raw) == expected['bytes'] == (value.bit_length()+7)//8,
                'minimal unsigned representation: '+name)
        raw_values[name] = raw
    binding = json.loads((ROOT/'COEFFICIENT_BINDING.json').read_text())
    require(binding == make_binding(raw_values, inherited), 'whole four-port binding')
    # This authenticated checker does not import or execute the constructor.
    checker = load_source34('authenticated_source34_independent_checker', 'verify_independent.py')
    audit = checker.run(payload_dir)
    receipt = {
        'status': 'PASS', 'authenticated_source_files': source_count,
        'upstream_checker_git_blob': '2d209c315b2c3d922349d499b7bd9476be499e75',
        'imports_or_executes_constructor': False,
        'all_raw_and_gzip_hashes_match_upstream': True,
        'complete_port_binding_checked': True,
        'tuple_sha256': binding['tuple_sha256'], 'independent_audit': audit,
        'scope': 'Finite exact coefficient decoding and compiler prerequisites; no consistency test or new formal semantic certificate.'
    }
    write_json(ROOT/'VERIFICATION.json', receipt)
    print(json.dumps(receipt, indent=2))


if __name__ == '__main__':
    main()
