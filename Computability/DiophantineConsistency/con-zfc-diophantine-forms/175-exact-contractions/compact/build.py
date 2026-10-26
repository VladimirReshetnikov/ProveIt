#!/usr/bin/env python3
"""Build inverse-Lucas, trace-linear compact polynomials from a pinned parent.

This script changes literal polynomial gates only. Mathematical equivalence
is proved in PROOF.md; the verifier does not infer it from bounded tests.
"""
from pathlib import Path
from collections import Counter
import argparse, copy, gzip, hashlib, importlib.util, json

ROOT = Path(__file__).resolve().parent


def construct(weight):
    parent = ROOT / 'inherited/trace87_degree232.json'
    graph = json.loads(parent.read_text())
    rows = []
    for name, op, a, b in graph['source']:
        if name in {'v0', 'Rp1sq', 'Rp1sqm4', 'rank_cubic', 'v_rank_cubic'}:
            continue
        if name == 'V0k':
            a, b = 'XY', 'kY'
        if name == 'q4s':
            rows += [['ksq', '*', 'k', 'k'], ['ksqm4', '-', 'ksq', 4],
                     ['inverse_cubic', '*', 'V0k', 'ksqm4']]
        if name == 'eclear':
            b = 'inverse_cubic'
        if name == 'L' and weight == 'b2':
            a, b = 'cTR', 'cTR'
        rows.append([name, op, a, b])
    graph.update(
        name='inverse_trace85_degree232_' + weight,
        source=rows, operations=len(rows),
        operation_breakdown=dict(Counter(r[1] for r in rows)),
        exact_degree=232, transport_weight=weight,
        generation='Inverse Lucas correction at k; unsquared strong trace; '
                   + ('squared transport coordinate.' if weight == 'b2' else 'bV transport.'),
        proof='PROOF.md',
        parent={'path':'inherited/trace87_degree232.json',
                'sha256':hashlib.sha256(parent.read_bytes()).hexdigest()},
        status='Ordinary proof at explicitly inherited native/refutation calibration; '
               'no new proof-assistant closure and no claim of global minimality.')
    graph['coefficient_binding']['path'] = 'coefficients/'
    return graph


def emit(check=False):
    for weight in ('b2', 'bV'):
        graph = construct(weight)
        target = ROOT / 'equations' / (graph['name'] + '.json')
        content = json.dumps(graph, indent=2) + '\n'
        if check:
            if target.read_text() != content:
                raise ValueError('Equation reconstruction mismatch: ' + target.name)
        else:
            target.parent.mkdir(exist_ok=True)
            target.write_text(content)
    source = ROOT / 'inherited/rebuild_coefficients_149.py'
    spec = importlib.util.spec_from_file_location('fixed_recipe', source)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    values = module.reconstruct()
    binding = construct('b2')['coefficient_binding']['ports']
    receipts = []
    for name, value in values.items():
        item = binding[name]
        raw = value.to_bytes((value.bit_length()+7)//8, 'little')
        if hashlib.sha256(raw).hexdigest() != item['raw_sha256']:
            raise ValueError('Fixed coefficient differs: ' + name)
        if value.bit_length() != item['bits']:
            raise ValueError('Fixed coefficient bit length differs: ' + name)
        output = ROOT / 'coefficients' / item['file']
        if check:
            if gzip.decompress(output.read_bytes()) != raw:
                raise ValueError('Payload differs: ' + name)
        else:
            output.write_bytes(gzip.compress(raw, compresslevel=9, mtime=0))
        receipts.append({'port':name,'bits':value.bit_length(),
                         'raw_sha256':hashlib.sha256(raw).hexdigest(),
                         'gzip_sha256':hashlib.sha256(output.read_bytes()).hexdigest()})
    report = {'fixed_coefficient_reconstruction':receipts,
              'variants':[{'weight':w,'operations':85,'degree':232,
                           'carrier_degree':21 if w=='b2' else 57}
                          for w in ('b2','bV')]}
    if not check:
        (ROOT / 'BUILD.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--check', action='store_true')
    emit(parser.parse_args().check)
