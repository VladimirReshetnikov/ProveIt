"""Saved-evidence rejection controls for the geometric/cochain comparison.

Run only after the coordinated audit and timings have finished. This script
does no discovery and measures no runtime. Every mutation is a reproducible
JSON-path edit to a byte-pinned input. Its finite rejection tests are not an
exhaustiveness claim or independent reconstruction of solver execution traces.
Only the four native verifier entry points use exact-argument memoization:
byte-identical previously verified proofs reuse their actual boolean result.
All research acceptance/accounting checks run again for every mutation.
"""
import argparse
from contextlib import ExitStack
from copy import deepcopy
from hashlib import sha256
import json
from pathlib import Path
import sys
from unittest.mock import patch

DATA = Path(__file__).resolve().parent
ROOT = DATA.parent.parent
sys.path.insert(0, str(ROOT/'fast'))
from fastunknot.diagram import Diagram
from geometric_descent_research.check_evidence import (
    check_audit, check_benchmark, replay_result)
from geometric_descent_research import check_evidence as evidence
from geometric_descent_research.common import (
    canonical_bytes, configs, digest, save, source_hashes)

if not __debug__:
    raise RuntimeError('corruption controls require assertions enabled')

REJECTION_ERRORS = (AssertionError, KeyError, ValueError, TypeError, IndexError)


def at(value, path):
    for key in path:
        value = value[key]
    return value


def edited(original, operations):
    """Apply a retained edit program; copy paths refer to the current document."""
    value = deepcopy(original)
    for operation in operations:
        path = operation['path']
        parent = at(value, path[:-1])
        kind = operation['operation']
        if kind == 'set':
            parent[path[-1]] = deepcopy(operation['value'])
        elif kind == 'delete':
            del parent[path[-1]]
        elif kind == 'copy':
            parent[path[-1]] = deepcopy(at(value, operation['source_path']))
        elif kind == 'reverse':
            at(value, path).reverse()
        elif kind == 'rehash-result':
            sample = at(value, path)
            payload = canonical_bytes(sample['result'])
            sample['result_sha256'] = sha256(payload).hexdigest()
            sample['serialized_bytes'] = len(payload)
        else:
            raise ValueError('unrecognized mutation operation')
    return value


def set_to(path, value):
    return dict(operation='set', path=path, value=value)


def delete(path):
    return dict(operation='delete', path=path)


def chain_path(result):
    return ['partial_chain'] if result['status'] == 'INCONCLUSIVE' else ['certificate', 'chain']


def native_result_valid(diagram, result, native):
    if result['status'] == 'INCONCLUSIVE':
        return bool(native['verify_crushing_chain'](diagram, result['partial_chain']))
    return bool(native['verify_crushing_recognition'](diagram, result['certificate']))


def typed(value):
    """Canonical JSON key material with container and scalar types preserved."""
    if type(value) is Diagram:
        return ['Diagram.pd', typed(value.pd)]
    if type(value) is dict and all(type(k) is str for k in value):
        return ['dict', [[key, typed(value[key])] for key in sorted(value)]]
    if type(value) in (list, tuple):
        return [type(value).__name__, [typed(item) for item in value]]
    if value is None or type(value) in (str, bool, int, float):
        return [type(value).__name__, value]
    raise TypeError('argument outside exact verifier cache domain')


class NativeVerifierCache:
    """Cache actual native booleans only; callbacks and exceptions are uncached.

    Keys contain complete typed argument bytes, not just their SHA256. Diagram
    arguments here are fresh validated PD objects from the research checker.
    The retained hashes describe keys; dictionary equality uses the full bytes.
    No source, certificate, result, config or research summary is rewritten.
    """
    NAMES = ('verify_crushing_chain', 'verify_crushing_recognition',
             'verify_normal_pachner_descent', 'verify_normal_geometric_descent')

    def __init__(self, output):
        self.stack = ExitStack()
        self.wrappers = {}
        output['native_verifier_cache'] = dict(
            scope='Exact typed arguments to four native verifier entry points only; every changed native source/proof argument misses.',
            unchanged_controls_populate_first=True,
            callbacks_bypass=True, research_checker_results_cached=False,
            fresh_duplicate_native_replay_claimed=False, functions={})
        for name in self.NAMES:
            original = getattr(evidence, name)
            counts = dict(hits=0, misses=0, bypasses=0, exceptions=0,
                          returned_true=0, returned_false=0, nonboolean_returns=0, entries=[])
            output['native_verifier_cache']['functions'][name] = counts
            self.wrappers[name] = self._wrap(original, counts)

    @staticmethod
    def _wrap(original, counts):
        cache = {}

        def verify(*args, **kwargs):
            key = None
            if not kwargs:
                try:
                    key = canonical_bytes(typed(args))
                except TypeError:
                    pass
            if key is not None and key in cache:
                counts['hits'] += 1
                return cache[key]
            counts['misses' if key is not None else 'bypasses'] += 1
            try:
                answer = original(*args, **kwargs)
            except BaseException:
                counts['exceptions'] += 1
                raise
            if type(answer) is bool:
                counts['returned_true' if answer else 'returned_false'] += 1
                if key is not None:
                    cache[key] = answer
                    counts['entries'].append(dict(arguments_sha256=sha256(key).hexdigest(), result=answer))
            else:
                counts['nonboolean_returns'] += 1
            return answer
        return verify

    def install(self):
        for name, verifier in self.wrappers.items():
            self.stack.enter_context(patch.object(evidence, name, verifier))

    def restore(self):
        self.stack.close()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--audit', type=Path, default=DATA/'geometric-descent-audit.json')
    parser.add_argument('--benchmark', type=Path, default=DATA/'geometric-descent-benchmark.json')
    parser.add_argument('--output', type=Path, default=DATA/'geometric-descent-corruption-controls.json')
    args = parser.parse_args()
    script = Path(__file__).resolve()
    assert args.output.resolve() not in {script, args.audit.resolve(), args.benchmark.resolve()}
    script_bytes = script.read_bytes()
    audit_bytes, benchmark_bytes = args.audit.read_bytes(), args.benchmark.read_bytes()
    audit, benchmark = json.loads(audit_bytes), json.loads(benchmark_bytes)
    pins = source_hashes()
    output = dict(schema='geometric-descent-corruption-controls-v1', passed=False,
        source_sha256=pins, script_sha256=sha256(script_bytes).hexdigest(),
        audit_sha256=sha256(audit_bytes).hexdigest(),
        benchmark_sha256=sha256(benchmark_bytes).hexdigest(),
        valid_controls=[], records=[], skipped_controls=[], failures=[], active_control=None,
        discovery_used=False, timings_performed=False, exhaustive=False,
        execution_trace_reconstructed=False,
        scope='Finite saved-evidence trust-boundary controls; no h transport or general complexity claim.')
    native_cache = NativeVerifierCache(output)
    save(args.output, output)

    def unchanged():
        assert source_hashes() == pins
        assert script.read_bytes() == script_bytes
        assert args.audit.read_bytes() == audit_bytes
        assert args.benchmark.read_bytes() == benchmark_bytes

    def cache_counts():
        return {name: {field: counts[field] for field in ('hits', 'misses', 'bypasses', 'exceptions')}
                for name, counts in output['native_verifier_cache']['functions'].items()}

    def cache_delta(before):
        after = cache_counts()
        return {name: {field: after[name][field]-value for field, value in counts.items()}
                for name, counts in before.items()}

    def valid(name, verify, **metadata):
        output['active_control'] = dict(name=name, expected='accepted')
        save(args.output, output)
        before = cache_counts()
        assert verify(), 'valid control rejected: '+name
        output['valid_controls'].append(dict(name=name, accepted=True,
                                             native_cache_delta=cache_delta(before), **metadata))
        output['active_control'] = None
        save(args.output, output)

    def reject(name, target, operations, **metadata):
        original = audit if target == 'audit' else benchmark
        changed = edited(original, operations)
        assert canonical_bytes(changed) != canonical_bytes(original), 'ineffective mutation: '+name
        record = dict(name=name, target=target, mutations=operations,
            mutated_document_sha256=digest(changed), expected='rejected',
            native_validity=None)
        record.update(metadata)
        output['active_control'] = record
        save(args.output, output)
        before = cache_counts()
        try:
            accepted = (check_audit(changed) if target == 'audit' else
                        check_benchmark(changed, audit, audit_bytes))
        except REJECTION_ERRORS as error:
            accepted = False
            record.update(rejection_type=type(error).__name__, rejection_message=str(error))
        else:
            record.update(rejection_type=None, rejection_message=None)
        assert not accepted, 'accepted mutation: '+name
        record['rejected'] = True
        record['native_cache_delta'] = cache_delta(before)
        output['records'].append(record)
        output['active_control'] = None
        save(args.output, output)

    native_cache.install()
    try:
        valid('unchanged complete audit', lambda: check_audit(audit), calls=14)
        valid('unchanged complete benchmark', lambda: check_benchmark(benchmark, audit, audit_bytes), calls=50)
        first_pin = next(iter(pins))
        audit_controls = [
            ('audit changed source pin', [set_to(['source_sha256', first_pin], '0'*64)]),
            ('audit missing case', [delete(['records', 6])]),
            ('audit missing arm', [delete(['records', 0, 'arms', 'geometric'])]),
            ('audit bool call count', [set_to(['coverage', 'ordinary_calls_completed'], True)]),
            ('audit geometric method relabelled', [set_to(['config', 'geometric', 'pachner_descent_method'], 'cochain')]),
            ('audit input PD changed', [set_to(['records', 0, 'input_pd'], [[0, 0, 1, 1]])]),
            ('audit endpoint equality negated', [set_to(['records', 0, 'endpoint_comparison', 'exact_typed_equality'], False)]),
        ]
        for name, operations in audit_controls:
            reject(name, 'audit', operations)

        base = ['records', 0, 'arms', 'geometric', 'result']
        stats = base+['stats']
        stat_controls = [
            ('bool pivot counter', [set_to(stats+['lp_pivots'], False)]),
            ('missing capped anchors', [delete(stats+['anchors_tested'])]),
            ('exceeded pivot cap', [set_to(stats+['lp_pivots'], 10001)]),
        ]
        for name, operations in stat_controls:
            reject(name, 'audit', operations)
        cpath = base+chain_path(at(audit, base))
        reject('geometric result recast as v4', 'audit', [set_to(cpath+['schema'], 'diagram-crushing-v4')])
        partial = next((i for i, case in enumerate(audit['records'])
                        if case['arms']['geometric']['result']['status'] == 'INCONCLUSIVE'), None)
        if partial is None:
            output['skipped_controls'].append(dict(name='partial marked complete', reason='all geometric outcomes conclusive'))
        else:
            reject('partial marked complete without terminal proof', 'audit', [
                set_to(['records', partial, 'arms', 'geometric', 'result', 'status'], 'KNOTTED')])

        # A real geometric macro is found only in already returned whole-call
        # evidence. This control performs no search to manufacture one.
        witness = None
        for i, case in enumerate(audit['records']):
            result = case['arms']['geometric']['result']
            path = ['records', i, 'arms', 'geometric', 'result']+chain_path(result)
            for j, step in enumerate(at(audit, path)['steps']):
                if step['schema'] == 'normal-geometric-descent-v1':
                    witness = path+['steps', j]
                    break
            if witness is not None:
                break
        if witness is None:
            output['skipped_controls'].append(dict(name='geometric macro corruptions', reason='no accepted geometric macro in the audited calls'))
        else:
            real_stats = ['records', witness[1], 'arms', 'geometric', 'result', 'stats']
            reject('macro counts algebraically consistent but absent', 'audit', [
                set_to(real_stats+['pachner_descent_macros'], 0),
                set_to(real_stats+['pachner_descent_upward_moves'], 0),
                set_to(real_stats+['pachner_descent_downward_moves'], 0)])
            if at(audit, real_stats+['pachner_descent_upward_moves']) > 0:
                reject('elementary totals consistent with D but contradict UDD proofs', 'audit', [
                    set_to(real_stats+['pachner_descent_upward_moves'], 0),
                    set_to(real_stats+['pachner_descent_downward_moves'],
                           at(audit, real_stats+['pachner_descent_macros']))])
            reject('geometric macro wrong source binding', 'audit', [set_to(witness+['source_sha256'], '0'*64)])
            endpoint = ['records', witness[1], 'endpoint_comparison', 'endpoints', 'geometric']
            reject('nonterminal endpoint hash changed', 'audit', [set_to(endpoint+['source_sha256'], '0'*64)])

        # Version five deliberately accepts old native packets, while the new
        # experiment's geometric arm requires its selected producer language.
        legacy = next((i for i, case in enumerate(audit['records']) if any(
            step['schema'] == 'normal-pachner-descent-v1'
            for step in at(case['arms']['cochain']['result'], chain_path(case['arms']['cochain']['result']))['steps'])), None)
        if legacy is None:
            output['skipped_controls'].append(dict(name='native-valid alternate policy proof', reason='no accepted cochain macro in the audited calls'))
        else:
            case = audit['records'][legacy]
            alternate = deepcopy(case['arms']['cochain']['result'])
            at(alternate, chain_path(alternate))['schema'] = 'diagram-crushing-v5'
            diagram = Diagram.from_pd(case['input_pd'])
            valid('native-valid same-diagram legacy proof in v5',
                  lambda: native_result_valid(diagram, alternate, native_cache.wrappers),
                  case_id=case['id'], result_sha256=digest(alternate), scope='Native topology proof; not geometric-policy provenance.')
            try:
                replay_result(diagram, 'geometric', alternate, configs('geometric'))
            except REJECTION_ERRORS:
                policy_rejected = True
            else:
                policy_rejected = False
            assert policy_rejected, 'geometric policy accepted a legacy macro'
            target = ['records', legacy, 'arms', 'geometric', 'result']
            ops = [dict(operation='copy', path=target,
                        source_path=['records', legacy, 'arms', 'cochain', 'result']),
                   set_to(target+chain_path(alternate)+['schema'], 'diagram-crushing-v5')]
            reject('native-valid same-diagram wrong-policy proof', 'audit', ops,
                   native_validity=True, direct_policy_replay_rejected=True, case_id=case['id'])
            timed_index = next((i for i, record in enumerate(benchmark['records']) if record['id'] == case['id']), None)
            if timed_index is None:
                output['skipped_controls'].append(dict(name='native-valid wrong timed result', reason='legacy macro case excluded from timing protocol'))
            else:
                timed_target = ['records', timed_index, 'paired', 0, 'samples', 'geometric']
                timed_source = ['records', timed_index, 'paired', 0, 'samples', 'cochain', 'result']
                timed_ops = [dict(operation='copy', path=timed_target+['result'], source_path=timed_source),
                    set_to(timed_target+['result']+chain_path(alternate)+['schema'], 'diagram-crushing-v5'),
                    dict(operation='rehash-result', path=timed_target)]
                assert at(edited(benchmark, timed_ops), timed_target+['result']) == alternate
                reject('timed native-valid wrong full result with recomputed hash', 'benchmark', timed_ops,
                       native_validity=True, case_id=case['id'], native_control_result_sha256=digest(alternate))

        # Timed payloads are bound to the audited full result, even if an
        # attacker also recomputes the sample's advertised digest and length.
        sample = ['records', 0, 'paired', 0, 'samples', 'geometric']
        warmup = ['records', 0, 'warmups', 'geometric']
        timing_controls = [
            ('timing changed audit hash', [set_to(['audit_sha256'], '0'*64)]),
            ('timing wrong coverage', [set_to(['calls_completed'], 49)]),
            ('timing pair order reversed', [dict(operation='reverse', path=['records', 0, 'paired', 0, 'order'])]),
            ('timing bool duration', [set_to(sample+['elapsed_ns'], True)]),
            ('timing float byte count', [set_to(sample+['serialized_bytes'], float(at(benchmark, sample+['serialized_bytes'])))]),
            ('timing changed hash', [set_to(sample+['result_sha256'], '0'*64)]),
            ('timing missing full result', [delete(sample+['result'])]),
            ('timing warmup result altered and rehashed', [set_to(warmup+['result', 'stats', 'lp_pivots'], 1),
                                                          dict(operation='rehash-result', path=warmup)]),
            ('timing forged median ratio', [set_to(['records', 0, 'summary', 'median_paired_cochain_over_geometric'], -1.0)]),
        ]
        for name, operations in timing_controls:
            reject(name, 'benchmark', operations)
        assert len({record['name'] for record in output['records']}) == len(output['records'])
        unchanged()
        output.update(passed=True, rejected_mutations=len(output['records']),
                      accepted_valid_controls=len(output['valid_controls']))
        save(args.output, output)
    except BaseException as error:
        output['passed'] = False
        output['failures'].append(dict(active_control=deepcopy(output['active_control']),
            error_type=type(error).__name__, message=str(error)))
        save(args.output, output)
        raise
    finally:
        native_cache.restore()
    print(json.dumps(dict(passed=True, rejected_mutations=len(output['records']),
                         accepted_valid_controls=len(output['valid_controls']),
                         skipped_controls=len(output['skipped_controls'])), sort_keys=True))


if __name__ == '__main__':
    main()
