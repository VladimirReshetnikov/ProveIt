"""Reproduce finite syntax, inference, translation, CLI, and fuel evidence."""
from pathlib import Path
import copy
import json
import subprocess
import sys
import audit

ROOT = Path(__file__).resolve().parent
CONTEXT = [([], [1, 1])]


def translated(p, length=1, explicit=False, repair=False):
    if not isinstance(p, list) or not p:
        return copy.deepcopy(p)
    if p[0] == 'u':
        _, j, t, q = p
        return ['u', j, t, translated(q, length, explicit, repair)]
    if p[0] == 'i':
        _, q = p
        suffix = [translated(q, length + 1, explicit, repair)]
        return ['i', 1 - length, *suffix] if explicit else ['i', *suffix]
    _, body, template, s, t, major, eq, branch = p
    if repair:
        template = audit.primary['walk'](template, lambda i, d:
                                          i if -length <= i <= d + 1 else 0)
    return ['e', body, template, s, t,
            translated(major, length, explicit, repair),
            translated(eq, length + 1, explicit, repair),
            translated(branch, length + 1, explicit, repair)]


def rejected_examples():
    U, REF, ONE, DUMMY, TRUTH = audit.U, audit.REF, audit.ONE, audit.DUMMY, audit.TRUTH
    cases = {
        'false_equation': [[0, ONE], REF(0)],
        'boolean_goal': [[False, False], REF(0)],
        'float_goal': [[0.0, 0.0], REF(0)],
        'escaped_free_goal': [[-1, -1], REF(-1)],
        'loose_bound_goal': [[1, 1], REF(0)],
        'wrong_term_arity': [[[0, 0], [0, 0]], REF(0)],
        'erased_ill_scoped_goal_body': [[[0, 0, 99], ONE], REF(ONE)],
        'unavailable_use_parameter': [TRUTH, U(0, -1)],
        'unavailable_clause': [TRUTH, U(1)],
        'boolean_clause_index': [TRUTH, U(True)],
        'negative_clause_index': [TRUTH, U(-1)],
        'unknown_opcode': [TRUTH, ['z']],
        'supplied_intro_witness': [[TRUTH], ['i', 0, REF(0)]],
        'forged_equality_premise': [TRUTH,
            ['e', TRUTH, TRUTH, 0, ONE, DUMMY, REF(0), REF(0)]],
        'malformed_major_matrix': [TRUTH,
            ['e', 0, TRUTH, 0, 0, DUMMY, REF(0), REF(0)]],
        'erased_malformed_template_body': [[ONE, ONE],
            ['e', TRUTH, [[1, 0, [0, 0]], ONE], 0, 0, DUMMY, REF(0), REF(ONE)]],
        'erased_boolean_template_body': [[ONE, ONE],
            ['e', TRUTH, [[1, 0, True], ONE], 0, 0, DUMMY, REF(0), REF(ONE)]],
        'active_extra_template_variable': [TRUTH,
            ['e', TRUTH, [-99, -99], 0, 0, DUMMY, REF(0), REF(0)]],
        'fresh_witness_export': [TRUTH,
            ['e', TRUTH, [1, 1], -1, -1, DUMMY, REF(-1), REF(-1)]],
        'term_used_as_template_formula': [TRUTH,
            ['e', TRUTH, ONE, 0, 0, DUMMY, REF(0), REF(0)]],
        'noncanonical_use_term': [TRUTH, U(0, [ONE, 0, 2])],
        'nonreflexive_base_as_progress': [[[[1, 0, 1], 0]], ['i', U(1)]],
    }
    bad = audit.naming_proof(ONE)
    bad[-1][-1] = REF(0)
    cases['wrong_conditional_antecedent'] = [audit.naming(ONE), bad]
    return cases


def cli(program, payload, optimized=False):
    command = [sys.executable, '-I', '-S', '-B']
    if optimized:
        command.append('-O')
    result = subprocess.run(command + [str(ROOT / program)],
                            input=json.dumps(payload).encode(),
                            stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                            timeout=20)
    return result.returncode == 0 and result.stdout == b'ACCEPT\n'


def main():
    positive = audit.examples()
    negative = rejected_examples()
    controls = {
        'explicit': audit.module('control_explicit_witness.py'),
        'validated': audit.module('control_template_validation.py')}
    fuel = audit.module('checker_fuel.py')
    counts = dict(positive=0, negative=0, explicit_translations=0,
                  repaired_translations=0, cli_runs=0, fuel_boundaries=0,
                  malformed_budgets=0)
    budgets = {}
    for name, (goal, proof) in positive.items():
        audit.primary['prove'](goal, proof, CONTEXT)
        controls['explicit']['prove'](goal, translated(proof, explicit=True), CONTEXT)
        controls['validated']['prove'](goal, translated(proof, repair=True), CONTEXT)
        counts['positive'] += 1
        counts['explicit_translations'] += 1
        counts['repaired_translations'] += 1
        fuel['fuel'] = 10 ** 8
        fuel['prove'](goal, proof, CONTEXT)
        used = 10 ** 8 - fuel['fuel']
        budgets[name] = used
        for supplied, expected in [(used, True), (used - 1, False)]:
            fuel['fuel'] = supplied
            try:
                fuel['prove'](goal, proof, CONTEXT)
                accepted = True
            except Exception:
                accepted = False
            assert accepted == expected, (name, supplied, used)
            counts['fuel_boundaries'] += 1
        for optimized in (False, True):
            assert cli('checker.py', [goal, proof], optimized), name
            assert cli('checker_fuel.py', [goal, proof, used], optimized), name
            assert not cli('checker_fuel.py', [goal, proof, used - 1], optimized), name
            counts['cli_runs'] += 3
        directory = ROOT / 'examples'
        directory.mkdir(exist_ok=True)
        (directory / (name + '.json')).write_text(json.dumps([goal, proof]) + '\n')
    for name, payload in negative.items():
        try:
            audit.primary['prove'](*payload, CONTEXT)
        except Exception:
            pass
        else:
            raise AssertionError(name)
        for optimized in (False, True):
            assert not cli('checker.py', payload, optimized), name
            counts['cli_runs'] += 1
        counts['negative'] += 1
        directory = ROOT / 'reject_examples'
        directory.mkdir(exist_ok=True)
        (directory / (name + '.json')).write_text(json.dumps(payload) + '\n')
    for budget in (-1, True, False, 1.0, '1000', None, [], {}):
        for optimized in (False, True):
            assert not cli('checker_fuel.py', [audit.TRUTH, audit.REF(0), budget], optimized)
            counts['cli_runs'] += 1
        counts['malformed_budgets'] += 1
    result = {'counts': counts, 'exact_fuel': budgets,
              'normalization': audit.normalization_audit(),
              'claim': 'Finite implementation evidence; no proof-assistant verification.'}
    (ROOT / 'verification_results.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
