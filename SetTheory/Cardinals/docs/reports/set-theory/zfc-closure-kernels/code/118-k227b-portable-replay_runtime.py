#!/usr/bin/env python3
"""Re-derive the complete portable K229/K228/K227 unary/list runtime certificates.

Python standard library only. Run this driver, not the historical engines' CLIs.
Outputs go to a separate directory; the sealed inputs are never rewritten.
"""
from pathlib import Path
import argparse
import hashlib
import importlib.util
import json
import sys
import time

ROOT = Path(__file__).resolve().parent
NAMES = ('delayed_erasure229', 'loop_delayed228', 'source_fold227_zerofix')
SCOPE = ('All independent natural primary registers, every decrement guard, all natural '
         'extra gaps, arbitrary first spare and finite spare tail; exact whole-tape/head/'
         'source-successor contract and positive duration.')


def require(value, message):
    if not value:
        raise ValueError(message)


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def normalized(value):
    return json.loads(json.dumps(value, sort_keys=True))


def write_json(path, value, compact=False):
    text = json.dumps(value, separators=(',', ':')) if compact else json.dumps(value, indent=2)
    path.write_text(text + '\n', encoding='utf-8')


def manifest_check(names):
    require(__debug__ and not sys.flags.optimize,
            'Runtime checking requires assertions enabled; do not use -O, -OO, or PYTHONOPTIMIZE.')
    manifest = json.loads((ROOT / 'RUNTIME_DEPENDENCIES.json').read_text())
    for relative, expected in manifest['runtime_files'].items():
        path = (ROOT / relative).resolve()
        require(path.is_relative_to(ROOT), ('Runtime dependency escapes packet', relative))
        require(sha(path) == expected, ('Changed pinned runtime dependency', relative))
    for name in names:
        for filename, expected in manifest['sealed_inputs'][name].items():
            require(sha(ROOT / name / filename) == expected, ('Changed sealed input', name, filename))
    return manifest


def validate_inputs(name, manifest):
    directory = ROOT / name
    config = json.loads((directory / 'construction.json').read_text())
    sealed = json.loads((directory / 'universal_runtime.json').read_text())
    sites = json.loads((directory / 'sites.json').read_text())
    require(sealed['status'] == 'UNIVERSAL_MATHEMATICAL_PASS', 'Sealed run was not complete')
    require(sealed['checker_sha256'] == manifest['original_driver_sha256'], 'Unexpected historical driver')
    require(sealed['inherited_engine_sha256'] == manifest['runtime_files']['runtime/symbolic_runtime.py'],
            'Sealed run used a different engine')
    require(type(config['append']) is int and config['append'] == 1, 'Unexpected append convention')
    require(config['logical_to_physical'] == [6, 2, 0, 4, 3, 7, 8, 5, 1], 'Unexpected register routing')
    require(isinstance(sites, list) and sites, 'Empty source')
    leaves, prefixes = set(), set()
    for row in sites:
        require(isinstance(row, list) and len(row) == 3, ('Malformed source row', row))
        pc, op, arg = row
        require(isinstance(pc, str) and 0 < len(pc) < 64 and set(pc) <= {'0', '1'}, 'Unsafe source prefix')
        require(pc not in leaves, 'Duplicate source leaf')
        require(op in ('CI', 'CD', 'CB', 'CC', 'CH'), 'Unknown primitive')
        if op in ('CI', 'CD'):
            require(type(arg) is int and 0 <= arg < 9, 'Invalid register')
        elif op in ('CB', 'CC'):
            require(type(arg) is int and arg >= 1, 'Invalid jump count')
        else:
            require(arg is None, 'Malformed halt')
        leaves.add(pc)
        prefixes.update(pc[:i] for i in range(len(pc)))
    require(not (leaves & prefixes), 'Source is not prefix-free')
    require(all(p + b in leaves or p + b in prefixes for p in prefixes for b in ('0', '1')),
            'Source tree is incomplete')
    require(len(prefixes) == len(leaves) - 1, 'Wrong source tree census')
    require(sum(row[1] == 'CH' for row in sites) == 1, 'Wrong halt count')
    expected_cases = sum(2 if row[1] == 'CD' else 1 for row in sites)
    require(expected_cases == config['guarded_cases'] == sealed['cases'], 'Incomplete guard coverage')
    require(sha(directory / 'candidate.tm') == config['table_sha256'] == sealed['table_sha256'],
            'Table binding mismatch')
    require(sha(directory / 'sites.json') == sealed['sites_sha256'], 'Source binding mismatch')
    source_pin = config.get('sites_sha256', config.get('source_sha256'))
    require(source_pin == sealed['sites_sha256'], 'Construction source binding mismatch')
    return directory, config, sealed, sites


def load_engine():
    # Load the exact vendored helper, then the exact vendored symbolic engine.
    # No historical default path, main(), sites(), or validate_inputs() is used.
    sys.dont_write_bytecode = True
    for name in ('independent_runtime', 'symbolic_runtime'):
        path = ROOT / 'runtime' / (name + '.py')
        spec = importlib.util.spec_from_file_location(name, path)
        require(spec is not None and spec.loader is not None, ('Cannot load engine', name))
        module = importlib.util.module_from_spec(spec)
        sys.modules[name] = module
        spec.loader.exec_module(module)
        require(Path(module.__file__).resolve() == path.resolve(), 'Unexpected imported engine path')
    return sys.modules['symbolic_runtime']


def replay(name, output_root, manifest, engine):
    directory, config, sealed, sites = validate_inputs(name, manifest)
    output = (output_root / name).resolve()
    for protected in [ROOT / n for n in NAMES] + [ROOT / 'runtime', ROOT / 'licenses']:
        require(not output.is_relative_to(protected.resolve()), 'Output would overwrite sealed packet data')
    output.mkdir(parents=True, exist_ok=True)
    table = engine.r.table(directory / 'candidate.tm')
    states = {q for q, _ in table}
    require(set(table) == {(q, b) for q in states for b in (0, 1)}, 'Partial literal table')
    require(95 in states and 96 in states and 254 not in states, 'Wrong engine-label interface')
    require({z for _, _, z in table.values()} - states == {254}, 'Undefined transition target')
    require(len(states) == config['working_states'] == sealed['working_states'], 'Wrong working-state count')
    require([line for line in (directory / 'candidate.tm').read_text().splitlines()
             if line.startswith('#! start ')] == ['#! start 95'], 'Wrong start declaration')
    engine.r.PHY = tuple(config['logical_to_physical'])
    started = time.monotonic()
    cases, used = [], set()
    receipt = dict(status='IN_PROGRESS', working_states=len(states),
                   table_sha256=sha(directory / 'candidate.tm'), sites_sha256=sha(directory / 'sites.json'),
                   checker_sha256=sha(__file__), inherited_engine_sha256=sha(ROOT / 'runtime/symbolic_runtime.py'),
                   header_base=64, append=config['append'], logical_to_physical=list(engine.r.PHY), scope=SCOPE)
    try:
        lemmas, blocks = engine.prove_blocks(table)
        sealed_blocks = json.loads((directory / 'universal_blocks.json').read_text())
        require(normalized(blocks) == sealed_blocks, 'Fresh generic block schemas differ from sealed schemas')
        for index, site in enumerate(sites):
            for positive in ((False, True) if site[1] == 'CD' else (False,)):
                result = engine.case(table, lemmas, site, positive, append=config['append'])
                used.update(result.pop('rows'))
                result.pop('trace')
                cases.append(dict(index=index, positive=positive, **result))
                if len(cases) % 1000 == 0:
                    print(name, 'PROVED', len(cases), 'SECONDS', round(time.monotonic() - started, 2), flush=True)
        require(len(cases) == config['guarded_cases'], 'Missing guarded case')
        require(used == set(table), 'Some literal rows were not covered')
        receipt.update(status='UNIVERSAL_MATHEMATICAL_PASS', cases=len(cases),
                       symbolic_steps=sum(c['symbolic_steps'] for c in cases), used_rows=len(used),
                       minimum_actual_steps=min(c['duration'][0] for c in cases),
                       maximum_symbolic_steps=max(c['symbolic_steps'] for c in cases))
        fresh_cases = normalized(cases)
        sealed_cases = json.loads((directory / 'universal_cases.json').read_text())
        require(fresh_cases == sealed_cases, 'Fresh complete case certificates differ from sealed certificates')
        # Execution duration and wrapper identity necessarily differ. All other
        # sealed result fields, including every scientific metric, must agree.
        execution_only = {'seconds', 'checker_sha256'}
        actual_metrics = {k: v for k, v in receipt.items() if k not in execution_only}
        expected_metrics = {k: v for k, v in sealed.items() if k not in execution_only}
        require(normalized(actual_metrics) == expected_metrics,
                ('Fresh result metrics differ', actual_metrics, expected_metrics))
        receipt['seconds'] = time.monotonic() - started
        write_json(output / 'universal_cases.json', cases, compact=True)
        write_json(output / 'universal_blocks.json', blocks)
        write_json(output / 'universal_runtime.json', receipt)
        comparison = dict(status='PORTABLE_RUNTIME_REPLAY_PASS', candidate=name,
                          fresh_cases_equal_sealed=True, fresh_blocks_equal_sealed=True,
                          all_nonexecution_result_fields_equal_sealed=True,
                          excluded_execution_fields=sorted(execution_only),
                          fresh_driver_sha256=sha(__file__), sealed_driver_sha256=sealed['checker_sha256'],
                          fresh_helper_sha256=sha(ROOT / 'runtime/independent_runtime.py'),
                          runtime_manifest_sha256=sha(ROOT / 'RUNTIME_DEPENDENCIES.json'),
                          cases=len(cases), symbolic_steps=receipt['symbolic_steps'], used_rows=len(used),
                          mathematical_scope=SCOPE,
                          proof_status='Executable ordinary mathematical evidence; not a proof-assistant kernel check.')
        write_json(output / 'comparison.json', comparison)
        print(json.dumps(comparison), flush=True)
        return comparison
    except Exception as exc:
        receipt.update(status='NOT_PROVED', cases=len(cases), seconds=time.monotonic() - started,
                       reason=repr(exc), site_index=locals().get('index'), site=locals().get('site'),
                       positive=locals().get('positive'))
        write_json(output / 'universal_runtime.json', receipt)
        raise


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('candidates', nargs='*', choices=NAMES, help='Default: replay all three complete machines')
    parser.add_argument('--output-dir', type=Path, default=ROOT / 'replay_output' / 'runtime')
    parser.add_argument('--check-only', action='store_true', help='Check pins and inputs without claiming a runtime replay')
    args = parser.parse_args()
    names = tuple(dict.fromkeys(args.candidates)) or NAMES
    manifest = manifest_check(names)
    for name in names:
        validate_inputs(name, manifest)
    if args.check_only:
        print(json.dumps({'status': 'PORTABLE_RUNTIME_INPUTS_ONLY_PASS', 'candidates': names}), flush=True)
        return
    engine = load_engine()
    results = [replay(name, args.output_dir.resolve(), manifest, engine) for name in names]
    print(json.dumps({'status': 'ALL_REQUESTED_RUNTIME_REPLAYS_PASS', 'results': results}), flush=True)


if __name__ == '__main__':
    main()
