#!/usr/bin/env python3
"""Separate observed-checkpoint verification overlay. CODE ONLY / HOLD."""
import argparse
import contextlib
import hashlib
import importlib.util
import io
import json
import sys
from pathlib import Path

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
REPOSITORY = ROOT.parents[1]
OLD = ROOT / 'research/round16-common-name-centering'
OBSERVATION = ROOT / 'reviews/round16-common-name-centering-observed-checkpoint.json'
SEALS = {
    'research/round16-square-weighted-projections': '34b2b1b6f27dea48cfc7692ad64e5a034304e76cb0d3ef47eae87ec194862acd',
    'research/round16-common-name-centering-plan': 'ed0f0365d85209797f50fd450bde8b929fc853772e9ae2fb1d1346d090bff4e1',
    'research/signed-pell-cap-nine-factor-projections': 'c48ecc2d0cf12e125ecc9ab45849073e6d06a303a38e130aa6fd42859168aefd',
}
CORE = {'replay.py', 'substitution.py', 'PROOF.md', 'README.md'}


def need(ok, why):
    if not ok:
        raise ValueError(why)


def get(path):
    return json.loads(path.read_bytes())


def meta(path):
    data = path.read_bytes()
    return dict(bytes=len(data), sha256=hashlib.sha256(data).hexdigest())


def inventory(folder, excluded=None):
    need(folder.is_dir() and not folder.is_symlink(), 'ordinary input directory')
    out = {}
    for path in sorted(folder.rglob('*')):
        need(not path.is_symlink(), 'no symlink input ' + str(path))
        if path.is_file() and path != excluded:
            out[str(path.relative_to(folder))] = meta(path)
    return out


def authenticate():
    pins = get(HERE / 'SOURCE_PINS.json')
    need(pins['schema'] == 'held_fast_sparse_substitution_replay_pins_v1', 'overlay pin schema')
    need(pins['closed_dependencies'] == SEALS, 'exact three sealed parents')
    need(set(pins['core']) == CORE, 'exact four reviewed core files')
    for name, record in pins['files'].items():
        need(meta(ROOT / name) == record, 'whole external input ' + name)
    for name, record in pins['core'].items():
        need(meta(HERE / name) == record, 'reviewed overlay core ' + name)
    hold = get(HERE / 'HOLD_INVENTORY.json')
    need(hold['schema'] == 'held_fast_sparse_substitution_replay_inventory_v1', 'held overlay schema')
    need(set(hold['files']) == CORE | {'SOURCE_PINS.json'}, 'exact held overlay payload names')
    need(hold['files'] == inventory(HERE, HERE / 'HOLD_INVENTORY.json'), 'whole held overlay inventory')
    observation = get(OBSERVATION)
    need(observation['schema'] == 'observed_not_accepted_fixed_centering_checkpoint_v1', 'observation schema')
    need(observation['folder'] == str(OLD.relative_to(ROOT)), 'observed source folder')
    need(observation['final_acceptance_or_manifest_sealing'] is False, 'observation is not endpoint acceptance')
    need(not (OLD / 'MANIFEST.json').exists(), 'observed source is not a finally sealed packet')
    actual = inventory(OLD)
    need(actual == observation['files'], 'entire observed source membership and bytes')
    need(len(actual) == observation['file_count'] == 34, 'all34 observed source files')
    need(sum(r['bytes'] for r in actual.values()) == observation['payload_bytes'] == 611657, 'whole observed byte count')
    required_files = {
        str(OBSERVATION.relative_to(ROOT)),
        'reviews/round16-common-name-centering-observed-checkpoint.md',
    } | {str(OLD.relative_to(ROOT)) + '/' + name for name in actual}
    for name, seal in SEALS.items():
        folder = ROOT / name
        manifest = folder / 'MANIFEST.json'
        need(meta(manifest)['sha256'] == seal, 'parent manifest ' + name)
        declared = get(manifest)['files']
        measured = inventory(folder, manifest)
        need(set(measured) == set(declared), 'complete parent member names ' + name)
        required_files.add(name + '/MANIFEST.json')
        required_files.update(name + '/' + member for member in measured)
        for member, record in measured.items():
            expected = declared[member]
            need(expected == (record if isinstance(expected, dict) else record['sha256']), 'parent member ' + name + '/' + member)
    need(set(pins['files']) == required_files, 'exact complete observed and three-parent input closure')
    return pins, observation


def safe_output(path):
    path = path.absolute()
    need(not any(p.is_symlink() for p in [path, *path.parents]), 'no symlink output path')
    path = path.resolve()
    need(not path.is_relative_to(REPOSITORY), 'all receipts outside the whole repository')
    need(not path.exists() or path.is_file(), 'ordinary receipt file')
    return path


def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def differential_controls(A, helper, original_sub):
    # Handwritten small exact polynomials. These supplement the universal proof.
    fixtures = [
        ('empty', [], 0, [[1, [1]], [-2, []]], [], False),
        ('constant', [[-5, []]], 0, [[3, [1]]], [[-5, []]], False),
        ('absent_index', [[3, [1, 1]], [-2, [2]], [5, []]], 0, [[1, [0, 2]]], [[3, [1, 1]], [-2, [2]], [5, []]], False),
        ('unit', [[1, [0]]], 0, [[2, [1]], [-3, []]], [[2, [1]], [-3, []]], False),
        ('zero_replacement', [[7, [0, 0, 1]], [-3, [0]], [4, [2]]], 0, [], [[4, [2]]], False),
        ('negative_constant', [[2, [0, 0]], [-3, [0, 1]], [-8, []]], 0, [[-2, []]], [[6, [1]]], False),
        ('square_cancellation', [[1, [0, 0]], [-2, [0]], [1, []]], 0, [[1, [1]], [1, []]], [[1, [1, 1]]], False),
        ('replacement_contains_index', [[1, [0, 0]], [-1, [0, 1]]], 0, [[1, [0]], [1, [2]]], [[1, [0, 0]], [2, [0, 2]], [1, [2, 2]], [-1, [0, 1]], [-1, [1, 2]]], False),
        ('quartic_cross_terms', [[3, [0, 0, 0, 0]], [-2, [0, 0, 1]], [5, [2]]], 0, [[1, [3]], [-2, []]], [[3, [3, 3, 3, 3]], [-24, [3, 3, 3]], [72, [3, 3]], [-96, [3]], [48, []], [-2, [1, 3, 3]], [8, [1, 3]], [-8, [1]], [5, [2]]], False),
        ('nonlinear_replacement', [[1, [0, 0]], [-1, [0]]], 0, [[1, [1, 1]], [2, [2]]], [[1, [1, 1, 1, 1]], [4, [1, 1, 2]], [4, [2, 2]], [-1, [1, 1]], [-2, [2]]], False),
        ('cancel_then_reappear', [[1, [0]], [-1, [1]], [1, [0, 1]]], 0, [[1, [1]], [1, []]], [[1, []], [1, [1, 1]], [1, [1]]], False),
        ('aliased_inputs', [[1, [0]], [1, []]], 0, [], [[1, [0]], [2, []]], True),
    ]
    passed = []
    order_difference = False
    for label, pterms, index, rterms, expected_terms, alias in fixtures:
        p = A.norm(pterms)
        r = p if alias else A.norm(rterms)
        before = (list(p.items()), list(r.items()))
        slow = original_sub(p, index, r)
        fast = helper.substitute(p, index, r, con=A.con, mul=A.mul, v=A.v)
        need(slow == fast == A.norm(expected_terms), 'exact small substitution ' + label)
        need(A.terms(slow) == A.terms(fast), 'same sorted terms ' + label)
        need((list(p.items()), list(r.items())) == before, 'no input mutation ' + label)
        need(fast is not p and fast is not r and fast is not slow, 'fresh independent result ' + label)
        need(all(tuple(sorted(m)) == m and type(c) is int and c != 0 for m, c in fast.items()), 'canonical integer result ' + label)
        if label == 'cancel_then_reappear':
            order_difference = list(slow) != list(fast)
            need(order_difference, 'fixture covers the documented insertion-order distinction')
        passed.append(label)
    return dict(passed_cases=passed, cases=len(passed), extensional_equality=True,
                sorted_term_equality=True, no_input_mutation=True, fresh_result=True,
                insertion_order_equality_claimed=False, cancellation_order_difference_observed=order_difference)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', required=True, type=Path)
    parser.add_argument('--old-output', required=True, type=Path)
    args = parser.parse_args()
    pins, observation = authenticate()
    output, old_output = safe_output(args.output), safe_output(args.old_output)
    need(output != old_output, 'distinct outer and original receipts')
    # No nonstdlib module is loaded until every observed/core/parent byte authenticates.
    helper = load('reviewed_accumulator_substitution', HERE / 'substitution.py')
    old = load('observed_fixed58_verifier', OLD / 'check.py')
    original_support = old.support
    adapter_calls = []

    def patched_support():
        need(not adapter_calls, 'exactly one original support load')
        A = original_support()
        before = dict(A.__dict__)
        controls = differential_controls(A, helper, A.sub)
        A.sub = lambda p, i, r: helper.substitute(p, i, r, con=A.con, mul=A.mul, v=A.v)
        need(set(A.__dict__) == set(before), 'no new vendor module attribute')
        need(all(A.__dict__[k] is value for k, value in before.items() if k != 'sub'), 'only vendor A.sub replaced')
        adapter_calls.append(controls)
        return A

    # A loader adapter is explicit: old.main() itself and every old check remain unchanged.
    old.support = patched_support
    previous_argv = sys.argv
    captured = io.StringIO()
    try:
        sys.argv = [str(OLD / 'check.py'), '--output', str(old_output)]
        with contextlib.redirect_stdout(captured):
            old.main()
    finally:
        old.support = original_support
        sys.argv = previous_argv
    need(len(adapter_calls) == 1, 'patched vendor used by the original full main pipeline')
    expected_name = 'CHECK_OPTIMIZED.json' if sys.flags.optimize else 'CHECK.json'
    old_bytes = old_output.read_bytes()
    expected_bytes = (OLD / expected_name).read_bytes()
    need(old_bytes == expected_bytes == captured.getvalue().encode(), 'entire original report and stdout byte equality')
    need((json.dumps(json.loads(old_bytes), sort_keys=True, indent=2) + '\n').encode() == old_bytes, 'original exact JSON serialization')
    authenticate()
    report = dict(
        schema='separate_fast_sparse_substitution_overlay_v1', status='PASS',
        optimized_python=bool(sys.flags.optimize), original_verifier_report=json.loads(old_bytes),
        original_verifier_report_bytes=meta(OLD / expected_name),
        original_complete_report_and_stdout_byte_identical=True,
        differential_controls=adapter_calls[0],
        overlay_provenance=dict(
            source_pins=meta(HERE / 'SOURCE_PINS.json'), held_inventory=meta(HERE / 'HOLD_INVENTORY.json'),
            core=pins['core'], observation_record=meta(OBSERVATION),
            observed_source_files=observation['file_count'], observed_source_bytes=observation['payload_bytes'],
            observed_source_is_accepted_final_endpoint=False, closed_dependencies=SEALS,
            old_main_invoked=True, old_support_loader_adapter_calls=1,
            only_vendor_arithmetic_attribute_replaced='sub',
            original_optimized_interruption=observation['fresh_ROOT_optimized_check'],
            prior_interruption_relabelled=False, separate_overlay_run=True,
            inherited_source_calibration='Unchanged original report and accepted sealed parent contracts; no new calibration or source/native application replay.'))
    data = (json.dumps(report, sort_keys=True, indent=2) + '\n').encode()
    need(not output.exists() or output.read_bytes() == data, 'refuse changed outer receipt overwrite')
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_bytes(data)
    print(data.decode(), end='')


if __name__ == '__main__':
    main()
