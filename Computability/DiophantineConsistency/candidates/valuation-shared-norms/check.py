#!/usr/bin/env python3
"""Exact every-node identity, binding, liveness and degree certificates.

Normal and optimized Python run the same explicit acceptance checks.  No
parent builder, frozen H10 emitter, array or Lean compiler is executed.
"""
import argparse
import copy
import gzip
import hashlib
import importlib.util
import json
from pathlib import Path
import random
import sys

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parent


def need(ok, message):
    if not ok:
        raise ValueError(message)


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def encoded(value):
    return (json.dumps(value, indent=2)+'\n').encode()


def module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    result = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(result)
    return result


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--output', type=Path, default=ROOT/'CHECKS.json')
    args = ap.parse_args()
    manifest_path = ROOT/'MANIFEST.json'
    if manifest_path.exists():
        for r in json.loads(manifest_path.read_text())['files']:
            raw = (ROOT/r['path']).read_bytes()
            need(sha(raw) == r['sha256'] and len(raw) == r['bytes'], 'candidate manifest item')
    pins = json.loads((ROOT/'SOURCE_PINS.json').read_text())
    need(pins['archive_sha256'] == '11267f89709f1bb10ba1237d29733727d9c41cebd783041419eb0773e6e7f937', 'whole arrival pin')
    need(len(pins['files']) == 124, 'complete120-member integer12 subtree plus four provenance files')
    for r in pins['files']:
        raw = (ROOT/r['path']).read_bytes()
        need(sha(raw) == r['sha256'] and len(raw) == r['bytes'], 'pinned source/proof engine member')
    need(len([p for p in (ROOT/'source').rglob('*') if p.is_file()]) == 120, 'no parent-source additions')
    # These helpers are unchanged copies of the already reviewed generic
    # exact cut checker; the new builder is a separate implementation.
    proof = module('valuation_exact_cut_checker', ROOT/'common/check_engine.py')
    build = module('valuation_shared_builder', ROOT/'build.py')
    leading = module('valuation_actual_leading_term', ROOT/'leading.py')
    binding_path = ROOT/'source/inherited/root_fusion/coefficients/BINDING.json'
    binding = json.loads(binding_path.read_text()); ports = {}; raw_bytes = 0
    for name, r in binding['payloads'].items():
        raw = gzip.decompress((binding_path.parent/r['file']).read_bytes())
        need(sha(raw) == proof.PORT_HASHES[name] == r['raw_sha256'], 'actual fixed coefficient bytes')
        ports[name] = int.from_bytes(raw, 'little'); raw_bytes += len(raw)
    need(raw_bytes == 615883 and ports['beta'] == 2**1064921-1
         and ports['cone_A'] == 2**1113 and ports['cone_B'] == 2**666104, 'whole six-port tuple')

    outputs, certificates = build.build_all()
    results, degree, negatives = {}, {}, []
    rng = random.Random(2082022400)
    for name, child in outputs.items():
        path = ROOT/(name+'.json'); cert_path = ROOT/'certificates'/(name+'.json')
        need(path.read_bytes() == encoded(child) and cert_path.read_bytes() == encoded(certificates[name]), 'deterministic complete rebuild')
        parent_path = ROOT/child['parent_equation']
        parent = json.loads(parent_path.read_text()); cert = json.loads(cert_path.read_text())
        exact = proof.prove_circuit(parent, child, cert)
        structure = proof.census(child)
        need((ROOT/child['coefficient_binding']).resolve() == binding_path.resolve(), 'actual coefficient binding path')
        degree[name] = leading.leading_certificate(child)
        need(structure['syntactic_degree_upper_bound'] == degree[name]['exact_degree'], 'matching degree upper/lower certificates')
        diagnostics = 0
        for prime in (1000000007, 1000000009, 2147483647):
            pports = {k: v % prime for k, v in ports.items()}
            for k in range(32):
                values = {v: rng.randrange(prime) for v in child['variables']}
                if k < 4:
                    values[('c', 's', 'r', 'v')[k]] = 0
                need(proof.evaluate(parent, values, pports, prime) == proof.evaluate(child, values, pports, prime), 'supplementary whole-value diagnostic')
                diagnostics += 1
        for label in ['output', 'coefficient']:
            bad = copy.deepcopy(child)
            if label == 'output':
                bad['nodes'][bad['output']][0] = 'add'
            else:
                i = next(i for i, n in enumerate(bad['nodes']) if n == ['coefficient', 'beta'])
                bad['nodes'][i][1] = 'MC'
            bad_cert = copy.deepcopy(cert); bad_cert['child_sha256'] = sha(encoded(bad))
            try:
                proof.prove_circuit(parent, bad, bad_cert)
            except ValueError:
                negatives.append(name+': operation-preserving '+label+' mutation rejected by exact proof')
            else:
                raise ValueError('changed whole circuit escaped exact proof')
        bad = copy.deepcopy(child)
        bad['degree_certificate']['coefficient']['2'] += 1
        try:
            leading.leading_certificate(bad)
        except ValueError:
            negatives.append(name+': wrong attained leading coefficient rejected')
        else:
            raise ValueError('wrong exact degree witness escaped independent gate calculation')
        results[name] = dict(parent_sha256=sha(parent_path.read_bytes()), child_sha256=sha(path.read_bytes()),
            parent_operations=parent['operations'], saved_operations=parent['operations']-child['operations'],
            structure=structure, whole_identity=exact, actual_degree=degree[name],
            supplementary_modular_comparisons=diagnostics)
    need((ROOT/'DEGREE.json').read_bytes() == encoded(degree), 'deterministic actual-circuit degree certificate')
    metrics = json.loads((ROOT/'METRICS.json').read_text())
    need([(x['name'], x['operations']) for x in metrics] == [(n, p['operations']) for n, p in outputs.items()], 'metric export')
    receipt = dict(status='PASS', python_optimized=not __debug__, pinned_integer12_source_files=120,
        pinned_provenance_helpers=4, whole_source34_raw_bytes=raw_bytes,
        whole_source34_raw_hashes=proof.PORT_HASHES, circuits=results, negative_controls_rejected=negatives,
        scope='The stored children are pointwise equal to the complete accepted valuation parents. Actual child leading terms certify exact degrees after numeral specialization. Inherited ordinary native/calibration proof unchanged; no Lean/internal-ZFC claim.')
    args.output.write_bytes(encoded(receipt))
    print(json.dumps(dict(status='PASS', python_optimized=not __debug__,
        circuits={n: dict(operations=r['structure']['operations'], exact_degree=r['actual_degree']['exact_degree'],
                         exact_cuts=len(r['whole_identity']['exact_local_identities'])) for n, r in results.items()},
        rejected_negative_controls=len(negatives)), indent=2))


if __name__ == '__main__':
    main()
