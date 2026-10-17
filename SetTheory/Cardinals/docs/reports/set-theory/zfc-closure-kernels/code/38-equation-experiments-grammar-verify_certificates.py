#!/usr/bin/env python3
"""Replay the delivered RM certificates without running a search or compiler.

The independent source-08 path engine is used through the unchanged source-19
arbitrary-reference wrapper. Its original command-line verifier expects the
219-node Coq DAG; these artifacts instead use the exact reviewed 217-node
source-19 reference whose hash is pinned below. Six corruption controls are
regenerated only in a temporary directory and are not retained in the package.
"""
from __future__ import annotations
import hashlib
import json
from pathlib import Path
import re
import sys
from tempfile import TemporaryDirectory
from types import SimpleNamespace

if sys.flags.optimize:
    raise SystemExit('Run without -O: the inherited independent verifier uses assertions.')
sys.dont_write_bytecode = True
BASE = Path(__file__).resolve().parent
SOURCE = BASE / 'research-inputs/Computability/BusyBeaver/Research/ZFC'
sys.path.insert(0, str(SOURCE))
import full_grammar_experiment as common
import layout_grammar_experiment as layout

REFERENCE_SHAS = {
    'grammar-baseline': 'a3c6729948f84d2d28beed5763b69244e988e7886fff244cdd27cec704a5d839',
    'grammar-rotation': 'c91c3c8aa1480cdfdf2b4276e39b765fbe6163401dbfc6155bb5a9d93021a93b',
    'grammar-plateau': 'c91c3c8aa1480cdfdf2b4276e39b765fbe6163401dbfc6155bb5a9d93021a93b',
}
ENGINE = (BASE / 'research-inputs/SetTheory/Cardinals/docs/reports/set-theory/'
          'zfc-closure-kernels/code/08-schema-machine-verify_rm_certificate.py')
CASES = ('grammar-baseline', 'grammar-rotation', 'grammar-plateau')


def require(condition, message):
    if not condition:
        raise ValueError(message)


def table_summary(path, expected_sha):
    data = path.read_bytes()
    digest = hashlib.sha256(data).hexdigest()
    require(digest == expected_sha, f'Table hash differs from recorded result: {path.name}')
    rows, start = {}, None
    for line in data.decode('ascii').splitlines():
        if line.startswith('#! start '):
            require(start is None, 'duplicate start')
            start = int(line.split()[-1])
        elif line and not line.startswith('#'):
            m = re.fullmatch(r'(\d+) ([01]) ([01]) ([LR]) (\d+)', line)
            require(m is not None, 'malformed binary table row')
            q, bit, write, direction, target = m.groups()
            key = int(q), int(bit)
            require(key not in rows, 'duplicate binary table row')
            rows[key] = int(write), direction, int(target)
    require(start == 0, 'expected blank-start control zero')
    require(set(rows) == {(q, b) for q in range(268) for b in (0, 1)},
            'expected exactly 268 binary working states')
    require(all(0 <= target <= 268 for _, _, target in rows.values()), 'invalid terminal target')
    require(any(target == 268 for _, _, target in rows.values()), 'unreferenced terminal')
    return {'working_states': 268, 'transition_rows': 536,
            'separate_terminal': 268, 'sha256': digest,
            'scope': 'Literal-table structure and recorded hash only; no binary simulation proof.'}


def main():
    engine = common.load_file('package_independent_source08', ENGINE)
    reference_object = json.loads((BASE / 'grammar-baseline/reference_dag.json').read_text())
    checks = {}
    for name in CASES:
        folder = BASE / name
        reference, candidate, certificate = (folder / 'reference_dag.json',
                                             folder / 'candidate_dag.json',
                                             folder / 'rm_bisimulation.json')
        reference_sha = hashlib.sha256(reference.read_bytes()).hexdigest()
        require(reference_sha == REFERENCE_SHAS[name],
                f'{name}: reference differs from the reviewed source-19 DAG')
        require(json.loads(reference.read_text()) == reference_object,
                f'{name}: reference semantics differ from the baseline')
        result = layout.independent_check(engine, reference, candidate, certificate)
        require(result['pairs'] == 4533 and result['reference_nodes'] == 217
                and result['candidate_nodes'] == 206, 'Unexpected certificate sizes')
        require(result['instructions'] == {'EInc': 2601, 'EDecnz': 1931, 'EHalt': 1},
                'Unexpected operation-site census')
        recorded = json.loads((folder / 'results.json').read_text())
        result['binary_table'] = table_summary(folder / 'candidate.tm', recorded['total_table_sha256'])
        result['reference_sha256'] = reference_sha
        result['candidate_sha256'] = hashlib.sha256(candidate.read_bytes()).hexdigest()
        result['certificate_sha256'] = hashlib.sha256(certificate.read_bytes()).hexdigest()
        checks[name] = result
    base = BASE / 'grammar-baseline'
    wrapper = SimpleNamespace(verify=lambda a, b, c: layout.independent_check(engine, a, b, c))
    with TemporaryDirectory(prefix='zfc-grammar-certificate-') as temp:
        controls = common.mutation_checks(wrapper, base / 'reference_dag.json',
                                          base / 'candidate_dag.json',
                                          base / 'rm_bisimulation.json', Path(temp))
    require(len(controls) == 6 and all(c['rejected'] for c in controls),
            'Certificate-corruption controls did not all reject')
    print(json.dumps({'status': 'PASS', 'checks': checks, 'corruption_controls': controls,
                      'searches_rerun': False, 'compiler_executed': False,
                      'kernel_proof_or_ZFC_endpoint': False}, indent=2))


if __name__ == '__main__':
    main()
