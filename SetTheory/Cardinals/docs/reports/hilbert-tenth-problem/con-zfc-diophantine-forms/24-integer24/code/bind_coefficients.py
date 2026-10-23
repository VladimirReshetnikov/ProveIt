#!/usr/bin/env python3
"""Bind every delivered circuit to the one materialized four-port tuple.

Usage: python3 code/bind_coefficients.py
Idempotent. Preserved upstream packets are never changed.
"""
import json
from pathlib import Path
from circuit_tools import PORTS, normalized_ports, audit_dag, digest, source_digest, require

ROOT = Path(__file__).resolve().parents[1]
PIN = 'ae3007ca4467011e0e051c84acb4a1dd13971b0e'
SOURCE_MAP = {
    'baseline67': 'baseline67_source.json',
    'retained59_system': 'retained59_source.json',
    **{'optimized_' + n: n + '_source.json' for n in (
        'norm12_product', 'norm12_system',
        'merger12_product', 'merger12_system',
        'merger13_product', 'merger13_system')}
}


def bind_one(path, manifest, binding_hash, pins):
    original = json.loads(path.read_text())
    p = normalized_ports(original)
    require(p['fixed_numerals'] == PORTS, 'unexpected coefficient interface: ' + path.name)
    ledger = audit_dag(p, check_ledger=False)
    name = path.stem
    q = dict(name=name, witnesses=p['witnesses'],
             domain=p.get('domain', p.get('witness_domain')),
             fixed_numerals=PORTS, source=p['source'])
    require(q['domain'] in ('strictly positive integers', 'unrestricted integers'),
            'unexpected domain')
    if 'output' in p:
        q.update(output=p['output'], exact_degree=p['exact_degree'])
    else:
        q.update(comparisons=p['comparisons'],
                 residual_exact_degrees=p['residual_exact_degrees'])
        q['exact_maximum_degree'] = max(q['residual_exact_degrees'])
    q.update(ledger=ledger, source_sha256=source_digest(q['source']),
             coefficient_binding='../coefficients/COEFFICIENT_BINDING.json',
             coefficient_binding_sha256=binding_hash,
             coefficient_instance=manifest['instance'],
             coefficient_payload_sha256={r['port']: r['sha256'] for r in manifest['files']},
             coefficient_contract='All four fixed numerals are the complete tuple in the binding; ports are never spliced.',
             proof_reference='../con_zfc_synthesis.tex',
             formal_status='Ordinary mathematical proofs formalizable in ZFC; no new Lean or Rocq theorem.')
    if name in SOURCE_MAP:
        source_name = SOURCE_MAP[name]
        local = 'upstream/' + source_name
        record = pins[local]
        q['preserved_source'] = dict(path='../' + local, sha256=record['sha256'],
                                    repository='VladimirReshetnikov/ProveIt',
                                    commit=PIN, repository_path=record['repository_path'])
        q['arithmetic_relation_to_source'] = (
            'Same polynomial template after Bm1->beta and Kconstant->K0 port renaming; new complete coefficient binding.'
            if name == 'baseline67' else
            'Same residual system and ports, with new complete coefficient binding.'
            if name == 'retained59_system' else
            'Exact arithmetic refactoring of the same polynomial or residual system in four symbolic ports; new complete coefficient binding.')
    else:
        builder = ('build_signed24.py' if name.startswith('signed_') else
                   'build_optimized_1069.py' if name.startswith('optimized_tightest_') else
                   'build_optimized_1073.py' if name.startswith('optimized_tight_') else
                   'build_optimized_1081.py')
        q['builder'] = '../code/' + builder
    path.write_text(json.dumps(q, indent=2) + '\n')
    return dict(file=str(path.relative_to(ROOT)), sha256=digest(path.read_bytes()),
                variables=len(q['witnesses']), domain=q['domain'],
                equations=1 if 'output' in q else len(q['comparisons']),
                degree=q.get('exact_degree', q.get('exact_maximum_degree')),
                operations=q['ledger']['operations'], source_sha256=q['source_sha256'])


def main():
    binding = ROOT / 'coefficients/COEFFICIENT_BINDING.json'
    manifest = json.loads(binding.read_text())
    require([r['port'] for r in manifest['files']] == PORTS, 'coefficient tuple order mismatch')
    records = json.loads((ROOT/'evidence/SOURCE_PINS.json').read_text())['files']
    pins = {r['local_path']: r for r in records}
    paths = sorted((ROOT/'circuits').glob('*.json'))
    require(len(paths) == 20, 'expected exactly 20 arithmetic circuit packets')
    output = [bind_one(path, manifest, digest(binding.read_bytes()), pins) for path in paths]
    receipt = dict(status='PASS', coefficient_instance=manifest['instance'],
                   coefficient_binding_sha256=digest(binding.read_bytes()), circuits=output,
                   circuit_count=len(output))
    (ROOT/'evidence/CIRCUIT_INDEX.json').write_text(json.dumps(receipt, indent=2)+'\n')
    print(json.dumps(dict(status='PASS', circuit_count=len(output),
                         coefficient_instance=manifest['instance']), indent=2))


if __name__ == '__main__':
    main()
