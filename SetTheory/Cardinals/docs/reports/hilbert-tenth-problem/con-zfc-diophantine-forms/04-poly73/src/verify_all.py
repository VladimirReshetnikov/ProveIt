#!/usr/bin/env python3
"""Reproduce the practical finite checks, without expanding K215 coefficients."""
from __future__ import annotations

import hashlib
import json
from pathlib import Path

import audit_compiler_transcription as audit
import diophantine
import k215_constants as compiler
import normalize_k215_direct as normalizer
import quadratic_elimination as quadratic

ROOT = Path(__file__).resolve().parents[1]


def read(relative):
    return json.loads((ROOT / relative).read_text())


def require(condition, message):
    if not condition:
        raise ValueError(message)


def main():
    sources = read('provenance/upstream_sources.json')['files']
    for item in sources:
        raw = (ROOT / item['package_path']).read_bytes()
        require(hashlib.sha256(raw).hexdigest() == item['sha256'],
                'upstream source SHA-256 differs: ' + item['package_path'])
        if 'git_blob_sha1' in item:
            blob = b'blob ' + str(len(raw)).encode() + b'\0' + raw
            require(hashlib.sha1(blob).hexdigest() == item['git_blob_sha1'],
                    'upstream Git blob differs: ' + item['package_path'])
    print('PASS: all packaged upstream source digests', flush=True)

    arithmetic = diophantine.verify()
    require(arithmetic == read('verification/arithmetic.json'), 'arithmetic receipt differs')
    for name, packet in diophantine.emitted_packets().items():
        require(packet == read('data/' + name), 'generated circuit differs: ' + name)
    print('PASS: circuit ledgers, emitted packets, degree and identity diagnostics', flush=True)

    source = normalizer.load_source(ROOT / 'data/k215.tm')
    require(normalizer.document(source) == read('data/normalized_k215.json'), 'normalized table differs')
    normalization = normalizer.verify(source)
    require(normalization == read('verification/normalizer.json'), 'normalization receipt differs')
    print('PASS: literal K215 table, all relabeled transitions, initializer and paired prefix', flush=True)

    machine_path = ROOT / 'data/normalized_k215.json'
    machine = compiler.Machine.read(machine_path)
    constants = compiler.manifest(machine_path, machine)
    constants['self_tests'] = dict(helical=compiler.toy_helical_test(),
                                 compiler=compiler.compiler_test(),
                                 window_count=compiler.window_count_test())
    require(json.loads(json.dumps(constants)) == read('data/constants_recipe.json'),
            'coefficient recipe receipt differs')
    require(constants['exact_layout_scalars']['b'] == 5**35, 'radix parameter')
    require(constants['exact_layout_scalars']['L'] == 5**36, 'cell width')
    require(constants['exact_layout_scalars']['d'] == 5**71, 'bit width')
    print('PASS: exact K215 scalar recipe, two-sided tableau, five compiler fixtures and cross count', flush=True)

    transcription = audit.run(ROOT / 'src/upstream/explore_fixed_raw_universal_76.py',
                              ROOT / 'src/upstream/complete75_half_binomial_compiler.py')
    require(transcription == read('verification/compiler_transcription.json'), 'transcription receipt differs')
    print('PASS: authenticated ancestor compiler functions and exact sparse-layout comparisons', flush=True)

    system = quadratic.build()
    require(system == read('data/quadratic83.json'), 'quadratic system differs')
    text = (ROOT / 'data/quadratic83.txt').read_text()
    for number, eq in enumerate(system['equations'], 1):
        line = f"{number:02d}. {eq['name']}: {eq['text']} = 0"
        require(line in text, 'printed quadratic equation differs: ' + eq['name'])
    print('PASS: all 46 printed quadratic equations, exact elimination and quartic degree', flush=True)

    result = dict(status='PASS',
                  authenticated_upstream_files=len(sources),
                  arithmetic_fixtures=arithmetic['arithmetic_evaluation_fixtures'],
                  machine_rows=normalization['transition_rows'],
                  paired_simulation_steps=normalization['paired_blank_steps'],
                  exact_window_count=constants['exact_window_count']['allowed_windows'],
                  exact_b_power_of_five=35, exact_d_power_of_five=71,
                  materialized_small_compiler_fixtures=len(constants['self_tests']['compiler']),
                  quadratic_variables=system['variable_count'],
                  quadratic_equations=system['equation_count'],
                  quartic_degree=system['single_equation_degree'],
                  no_full_K215_window_enumeration=True,
                  no_K215_halting_or_nonhalting_decision=True,
                  no_new_kernel_formalization=True)
    (ROOT / 'verification/full.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
