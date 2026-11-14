#!/usr/bin/env python3
"""Fresh universal replay for the literal U208; inherited mathematical engine."""
import argparse
import gzip
import hashlib
import json
import sys
import time
from pathlib import Path
from build import ROOT, read, census, need

sys.path.insert(0, str(Path(__file__).parent / 'runtime'))
import native_symbolic as s


def check(machine, output):
    need(__debug__ and not sys.flags.optimize, 'Universal replay requires assertions')
    machine, output = Path(machine), Path(output)
    output.mkdir(parents=True, exist_ok=True)
    table = read(machine / 'u208.native.tm')
    census(table, 208, 254)
    sites = json.loads((machine / 'sites.json').read_text())
    need(len(sites) == 3909, 'Source census')
    lemmas, blocks = s.prove_blocks(table)
    cases, used = [], set()
    began = time.monotonic()
    for i, site in enumerate(sites):
        for positive in ((False, True) if site[1] == 'CD' else (False,)):
            answer = s.case(table, lemmas, site, positive)
            used.update(answer['rows'])
            answer['rows'] = sorted(answer['rows'])
            answer.pop('trace')
            cases.append({'site_index': i, 'positive': positive, **answer})
        if (i + 1) % 500 == 0:
            print(f'Rederived {len(cases)} universal contracts', flush=True)
    for block in blocks:
        for event in block['trace']:
            used.add(tuple(event[1][:2]))
    need(len(cases) == 5084 and used == set(table), 'Contract/row coverage')
    need(all(len(c['duration']) == 13 and c['duration'][0] > 0
             and all(v >= 0 for v in c['duration']) for c in cases), 'Positive duration')
    steps = sum(c['symbolic_steps'] for c in cases)
    need(steps == 1251865, 'Inference census changed')
    normalized = json.loads(json.dumps(cases))
    with gzip.open(ROOT / 'evidence/u208_runtime_cases.json.gz', 'rt') as f:
        need(normalized == json.load(f), 'Fresh contracts differ from sealed discovery replay')
    result = {'status': 'UNIVERSAL_RUNTIME_PASS', 'working_states': 208,
              'transition_rows': 416, 'literal_rows_covered': len(used),
              'source_primitives': 3909, 'contracts': len(cases),
              'symbolic_inferences': steps, 'list_induction_lemmas': len(blocks),
              'minimum_duration_constant': min(c['duration'][0] for c in cases),
              'all_duration_coefficients_nonnegative': True,
              'arbitrary_primary_registers': 9, 'arbitrary_gap': True,
              'arbitrary_nonempty_spare_list': True, 'complete_tape_checked': True,
              'fresh_contracts_equal_saved': True, 'seconds': time.monotonic() - began,
              'table_sha256': hashlib.sha256((machine / 'u208.native.tm').read_bytes()).hexdigest(),
              'engine_sha256': {p.name: hashlib.sha256(p.read_bytes()).hexdigest()
                                for p in (Path(s.__file__), Path(s.r.__file__))},
              'blocks': blocks,
              'scope': 'Executable ordinary induction, not a proof-assistant kernel certificate.'}
    (output / 'runtime.json').write_text(json.dumps(result, indent=2) + '\n')
    return result


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--machine', type=Path, required=True)
    p.add_argument('--output', type=Path, required=True)
    a = p.parse_args()
    print(json.dumps(check(a.machine, a.output), indent=2))
