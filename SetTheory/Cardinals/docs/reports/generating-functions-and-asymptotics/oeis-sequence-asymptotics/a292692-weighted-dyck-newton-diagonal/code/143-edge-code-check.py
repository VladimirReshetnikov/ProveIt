#!/usr/bin/env python3
"""Closed-fixture exact companion. Stdlib only; use Python -I [-O] -B.

check: regenerate all values and print a compact machine-readable verdict.
replay: regenerate, validate, and print the complete frozen fixture.
selftest: exercise real entrypoints and disposable mutations under -O too.

There is no fixture-update, input-path, or output-path option. Computation
entrypoints write only to stdout/stderr. selftest alone creates temporary
copies, which are removed when it finishes. No network access is used.
"""
import sys
if not sys.flags.isolated:
    sys.stderr.write('REJECTED: isolated Python (-I) is required before any imports\n')
    raise SystemExit(2)
sys.dont_write_bytecode = True

import hashlib
import json
from pathlib import Path
import runpy


ROOT = Path(__file__).resolve().parent.parent
SCHEMA = 'report143-exact-v2'
SCOPE = ('Exact finite checks; analytic remainders and ceiling-safe bounds '
         'are proved in Report143.')


class Invalid(RuntimeError):
    """Malformed structure or disagreement with regenerated mathematics."""


def need(condition, message):
    if not condition:
        raise Invalid(message)


def fixed_file(relative):
    path = ROOT / relative
    need(not path.is_symlink() and not path.parent.is_symlink(),
         'PATH: symlinked companion input: '+relative)
    need(path.is_file(), 'PATH: missing companion input: '+relative)
    return path


def no_duplicates(pairs):
    result = {}
    for key, value in pairs:
        need(key not in result, 'JSON: duplicate key: '+key)
        result[key] = value
    return result


def no_constant(value):
    raise Invalid('JSON: non-finite constant: '+value)


def equal_closed(actual, expected, path='$'):
    """Exact JSON types, closed key sets, lengths and values, not coercion.

    In particular bool is not int; rational strings cannot be replaced by
    numbers or noncanonical equivalents. Every fixture leaf is checked.
    The schema is the full independently regenerated finite result shape.
    """
    need(type(actual) is type(expected), 'TYPE: '+path)
    if type(expected) is dict:
        need(set(actual) == set(expected), 'FIELDS: '+path)
        for key in sorted(expected):
            equal_closed(actual[key], expected[key], path+'.'+key)
    elif type(expected) is list:
        need(len(actual) == len(expected), 'LENGTH: '+path)
        for i, (left, right) in enumerate(zip(actual, expected)):
            equal_closed(left, right, path+'['+str(i)+']')
    else:
        need(actual == expected, 'VALUE: '+path)


def regenerate():
    edge = runpy.run_path(str(fixed_file('code/edge.py')))['run']()
    profile = runpy.run_path(str(fixed_file('code/profile.py')))['compute'](8)
    return {'schema':SCHEMA, 'scope':SCOPE, 'status':'PASS',
            'edge':edge, 'profile':profile}


def verify():
    raw = fixed_file('checks/fixtures.json').read_bytes()
    fixture = json.loads(raw, object_pairs_hook=no_duplicates,
                         parse_constant=no_constant)
    expected = regenerate()
    equal_closed(fixture, expected)
    return expected, hashlib.sha256(raw).hexdigest()


def summary(expected, digest):
    edge, profile = expected['edge'], expected['profile']
    return {'schema':'report143-check-v1', 'status':'PASS',
            'fixture_schema':SCHEMA, 'fixture_sha256':digest,
            'ranges':{'maximum_n':edge['maximum_n'],
                      'maximum_a':edge['maximum_a'],
                      'top_polynomial_order':edge['polynomial_order'],
                      'profile_order':profile['order']},
            'edge_checks':edge['counts'], 'profile_checks':profile['checks'],
            'scope':SCOPE}


def main():
    need(len(sys.argv) <= 2, 'CLI: expected check, replay, or selftest')
    mode = sys.argv[1] if len(sys.argv) == 2 else 'check'
    need(mode in ('check','replay','selftest'), 'CLI: unknown command')
    if mode == 'selftest':
        result = runpy.run_path(str(fixed_file('code/selftest.py')))['run']()
    else:
        expected, digest = verify()
        result = expected if mode == 'replay' else summary(expected, digest)
    print(json.dumps(result, sort_keys=True, indent=2))


if __name__ == '__main__':
    try:
        main()
    except (RuntimeError, OSError, ValueError, UnicodeError) as exc:
        print(json.dumps({'status':'FAIL', 'error':str(exc)}, sort_keys=True),
              file=sys.stderr)
        raise SystemExit(1)
