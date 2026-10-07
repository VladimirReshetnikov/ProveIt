#!/usr/bin/env python3
"""Exact-input corruption tests; explicit exceptions remain active under -O."""
from __future__ import annotations
import ast
from copy import deepcopy
from fractions import Fraction as Q
import json
from pathlib import Path
import subprocess
import sys
import tempfile
from unittest import mock
sys.dont_write_bytecode = True
ROOT = Path(__file__).absolute().parent.parent
sys.path[:0] = [str(ROOT), str(ROOT / 'code')]
import verify_exact as kernel
import verify_manifest as manifest


def run_tests():
    accepted, rejected = [], []
    def good(name, condition):
        kernel.require(condition, name)
        accepted.append(name)
    def bad(name, operation):
        try:
            operation()
        except (ArithmeticError, ValueError, TypeError, OSError, KeyError):
            rejected.append(name)
            return
        raise ArithmeticError('corruption escaped guard: ' + name)
    values = kernel.exact_values(kernel.EXACT_MAX_N)
    kernel.check_values(values)
    accepted.append('valid exact values')
    kernel.check_fixture(ROOT / 'data/fixture21.json', values)
    accepted.append('valid fixture')
    good('valid rational certificate', kernel.rational_tail_certificate()['tail_bound'] == '359101/26730899')
    for N in (-1, 1.5, '60', True):
        bad('invalid exact limit ' + repr(N), lambda N=N: kernel.exact_values(N))
    for k in (0, -1, 1.5, '1', True):
        bad('invalid divisor input ' + repr(k), lambda k=k: kernel.odd_sigma(k))
    for key, value in [('e_upper', Q(87,32)), ('pi_lower', Q(22,7)),
                       ('exponent', Q(6)), ('r', Q(1,100)), ('tail_limit', Q(1,100))]:
        bad('altered rational ' + key, lambda key=key,value=value: kernel.rational_tail_certificate(**{key:value}))
    bad('too few exact values', lambda: kernel.check_values(values[:-1]))
    altered = values.copy(); altered[20] += 1
    bad('altered exact prefix', lambda: kernel.check_values(altered))
    altered = values.copy(); altered[300] = 0
    bad('altered positivity', lambda: kernel.check_values(altered))
    altered = values.copy(); altered[300] = 299 * altered[299]
    bad('altered strict inequality', lambda: kernel.check_values(altered))
    altered = values.copy(); altered[300] = float(1)
    bad('noninteger exact value', lambda: kernel.check_values(altered))
    bad('nonzero polynomial constant', lambda: kernel.composed_coefficients([Q(1)]*4,3))
    bad('wrong polynomial size', lambda: kernel.composed_coefficients([Q(0)],3))
    fixture = manifest.load_json((ROOT/'data/fixture21.json').read_text())
    with tempfile.TemporaryDirectory(prefix='report185-math-guards-') as temporary:
        path = Path(temporary)/'fixture.json'
        variants = []
        for name, alter in [('wrong term', lambda d: d['values'].__setitem__(20,d['values'][20]+1)),
                            ('short prefix', lambda d: d['values'].pop()),
                            ('wrong sequence', lambda d: d.__setitem__('sequence','A330498')),
                            ('wrong offset', lambda d: d.__setitem__('offset',1)),
                            ('bool offset', lambda d: d.__setitem__('offset',False)),
                            ('bool coefficient', lambda d: d['values'].__setitem__(1,True)),
                            ('extra field', lambda d: d.__setitem__('extra',0))]:
            data = deepcopy(fixture); alter(data)
            variants.append((name,json.dumps(data)))
        variants += [('duplicate key', '{"sequence":"A330498","sequence":"A330499","offset":0,"values":[]}'),
                     ('nonfinite', '{"sequence":"A330499","offset":0,"values":[NaN]}')]
        for name, content in variants:
            path.write_text(content)
            bad('fixture ' + name, lambda: kernel.check_fixture(path,values))
        data = deepcopy(fixture); data['values'][20] += 1
        path.write_text(json.dumps(data))
        for optimized in (False,True):
            command = [sys.executable,'-I','-S','-B'] + (['-O'] if optimized else [])
            command += [str(ROOT/'code/verify_exact.py'),'--fixture',str(path)]
            result = subprocess.run(command,capture_output=True,text=True,timeout=120,shell=False)
            good('CLI wrong fixture rejected ' + ('optimized' if optimized else 'normal'),
                 result.returncode != 0 and 'frozen OEIS fixture differs' in result.stderr)
        with mock.patch.object(kernel,'direct_q',lambda k: Q(0)):
            bad('q identity implementation corruption',lambda: kernel.run())
        with mock.patch.object(kernel,'composed_coefficients',lambda B,N: [Q(0)]*(N+1)):
            bad('composition implementation corruption',lambda: kernel.run())
    for name in ('code/verify_exact.py','code/test_exact_guards.py','verify_manifest.py'):
        tree = ast.parse((ROOT/name).read_text())
        good('no removable asserts in '+name,not any(isinstance(node,ast.Assert) for node in ast.walk(tree)))
    return {'status':'PASS','positive_tests':len(accepted),'negative_tests':len(rejected),
            'corrupted_fixture_cli_modes':['normal','optimized'],'assertions_required':False,
            'network_required':False}


def main():
    try:
        print(json.dumps(run_tests(),sort_keys=True))
    except (ArithmeticError,ValueError,TypeError,OSError,subprocess.TimeoutExpired) as exc:
        print(json.dumps({'status':'FAIL','error':str(exc)},sort_keys=True),file=sys.stderr)
        return 1
    return 0

if __name__ == '__main__':
    sys.exit(main())
