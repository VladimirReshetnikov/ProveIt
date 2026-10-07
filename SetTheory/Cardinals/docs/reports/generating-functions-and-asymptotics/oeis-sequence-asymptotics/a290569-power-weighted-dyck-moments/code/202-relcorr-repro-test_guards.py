#!/usr/bin/env python3
"""Adversarial input, consistency and optimized-runtime tests; standard library only."""
from __future__ import annotations
import argparse
import ast
import copy
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import check


def require(condition, message):
    if not condition: raise RuntimeError(message)


def rejected(action, name):
    try:
        action()
    except check.CheckError:
        return name
    raise RuntimeError('Guard failed to reject: '+name)


def refresh_manifest(root):
    names = sorted(x.name for x in root.iterdir() if x.name != 'manifest.json')
    records = [{'path': name, 'bytes': len((root/name).read_bytes()), 'sha256': check.sha256((root/name).read_bytes())} for name in names]
    (root/'manifest.json').write_bytes(check.canonical_bytes({'schema': 'report202-generated-manifest-v1', 'files': records}))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--diagnostics", action="store_true", help="also run mpmath and rehashed-diagnostic guards")
    args = parser.parse_args()
    passed = []
    for name, action in [
        ('false explicit require', lambda:check.require(False, 'test')),
        ('boolean maximum', lambda:check.moments([0,1], True)),
        ('negative maximum', lambda:check.moments([0], -1)),
        ('excessive maximum', lambda:check.moments([0], 1025)),
        ('insufficient weights', lambda:check.moments([0], 1)),
        ('boolean weight', lambda:check.moments([0,True], 1)),
        ('floating weight', lambda:check.moments([0,1.0], 1)),
        ('negative weight', lambda:check.moments([0,-1], 1)),
        ('zero positive-height weight', lambda:check.moments([0,0], 1)),
        ('nonzero zero-height placeholder', lambda:check.moments([1,1], 1)),
        ('unknown law', lambda:check.weight('unsupported',1)),
        ('negative height', lambda:check.weight('quadratic',-1)),
        ('boolean exact config', lambda:check.exact_results(True)),
        ('small exact config', lambda:check.exact_results(15)),
        ('excessive exact config', lambda:check.exact_results(257)),
    ]:
        passed.append(rejected(action,name))
    for value in ('', '01', '-0', '1/0', '2/4', '1/1', '1/-2', '1.0', 'NaN', '+1', ' 1', True, 1, None):
        passed.append(rejected(lambda value=value:check.parse_rational(value), 'malformed rational '+repr(value)))
    with tempfile.TemporaryDirectory(prefix='report202-guards-') as temp:
        temp = Path(temp)
        raw = temp/'input.json'
        for name, payload in [('duplicate key',b'{"x":1,"x":2}'), ('NaN',b'{"x":NaN}'),
                              ('Infinity',b'{"x":Infinity}'), ('truncated',b'{"x":'),
                              ('trailing content',b'{}{}'), ('invalid UTF8',b'\xff')]:
            raw.write_bytes(payload)
            passed.append(rejected(lambda:check.strict_json(raw), 'malformed JSON '+name))
        with raw.open('wb') as stream: stream.truncate(check.MAX_BYTES+1)
        passed.append(rejected(lambda:check.strict_json(raw), 'oversized JSON'))
        raw.unlink()
        raw.symlink_to(HERE/'data/fixtures.json')
        passed.append(rejected(lambda:check.strict_json(raw), 'symlink JSON'))
        raw.unlink()
        fixtures = check.load_fixtures(HERE/'data/fixtures.json')
        fixture_cases = [
            ('fixture schema',lambda x:x.update(schema='wrong')),
            ('fixture extra field',lambda x:x.update(extra=0)),
            ('fixture missing sequence',lambda x:x['sequences'].pop()),
            ('fixture reordered sequence',lambda x:x['sequences'].reverse()),
            ('fixture unknown law',lambda x:x['sequences'][0].update(law='bad')),
            ('fixture false integer',lambda x:x['sequences'][0]['moments_n0_through_n6'].__setitem__(3,'16')),
            ('fixture wrong secant anchor',lambda x:x['sequences'][1]['moments_n0_through_n6'].__setitem__(6,'2702766')),
            ('fixture false rational',lambda x:x['sequences'][-1]['moments_n0_through_n6'].__setitem__(1,'7/6')),
            ('fixture missing degree',lambda x:x['sequences'][0]['moments_n0_through_n6'].pop()),
            ('fixture wrong parity coefficient',lambda x:x['oscillatory_coefficients'].update(even='-1/6')),
        ]
        for name, mutate in fixture_cases:
            fixture = copy.deepcopy(fixtures)
            mutate(fixture)
            raw.write_bytes(check.canonical_bytes(fixture))
            passed.append(rejected(lambda:check.load_fixtures(raw), name))
        raw.write_bytes(check.canonical_bytes(fixtures)+b'\n')
        passed.append(rejected(lambda:check.load_fixtures(raw), 'noncanonical fixture bytes'))
        values = check.exact_results(16)
        base = temp/'base'
        check.write_results(base,values)
        require(check.validate_generated(base)['status'] == 'PASS', 'Valid generated fixture rejected')
        passed.append('valid generated fixture accepted')
        counter = 0
        def generated_case(name, mutation):
            nonlocal counter
            counter += 1
            root = temp/('case-'+str(counter))
            shutil.copytree(base,root)
            mutation(root)
            passed.append(rejected(lambda:check.validate_generated(root),name))
        generated_case('missing generated member', lambda r:(r/'exact_data.json').unlink())
        generated_case('extra generated member', lambda r:(r/'extra.json').write_text('{}'))
        generated_case('extra generated directory', lambda r:(r/'extra').mkdir())
        generated_case('symlink generated member', lambda r:((r/'exact_data.json').unlink(),(r/'exact_data.json').symlink_to(base/'exact_data.json')))
        generated_case('corrupt generated bytes', lambda r:(r/'exact_data.json').write_bytes(b'{}\n'))
        def edit_manifest(root, mutate):
            manifest = check.strict_json(root/'manifest.json')
            mutate(manifest)
            (root/'manifest.json').write_bytes(check.canonical_bytes(manifest))
        for name, mutate in [
            ('wrong manifest schema',lambda x:x.update(schema='wrong')),
            ('extra manifest key',lambda x:x.update(extra=0)),
            ('missing manifest member',lambda x:x['files'].pop()),
            ('duplicate manifest member',lambda x:x['files'].__setitem__(1,x['files'][0])),
            ('reversed manifest',lambda x:x['files'].reverse()),
            ('manifest path traversal',lambda x:x['files'][0].update(path='../exact_checks.json')),
            ('absolute manifest path',lambda x:x['files'][0].update(path='/exact_checks.json')),
            ('noncanonical manifest path',lambda x:x['files'][0].update(path='./exact_checks.json')),
            ('boolean manifest length',lambda x:x['files'][0].update(bytes=True)),
            ('floating manifest length',lambda x:x['files'][0].update(bytes=1.0)),
            ('negative manifest length',lambda x:x['files'][0].update(bytes=-1)),
            ('oversized manifest length',lambda x:x['files'][0].update(bytes=check.MAX_BYTES+1)),
            ('uppercase hash',lambda x:x['files'][0].update(sha256='A'*64)),
            ('wrong hash',lambda x:x['files'][0].update(sha256='0'*64)),
            ('short hash',lambda x:x['files'][0].update(sha256='0'*63)),
            ('extra manifest record key',lambda x:x['files'][0].update(extra=0)),
        ]:
            generated_case(name, lambda root,mutate=mutate:edit_manifest(root,mutate))
        generated_case('noncanonical manifest bytes',lambda r:(r/'manifest.json').write_bytes((r/'manifest.json').read_bytes()+b'\n'))
        def altered_and_rehashed(root,name,mutate):
            value = check.strict_json(root/name)
            mutate(value)
            (root/name).write_bytes(check.canonical_bytes(value))
            refresh_manifest(root)
        for name, file, mutate in [
            ('rehashed incorrect moment','exact_data.json',lambda x:x['integer_moments']['quartic'].__setitem__(16,'1')),
            ('rehashed wrong occupation','exact_data.json',lambda x:x['exact_occupation_at_n8'][0]['occupation_masses'].__setitem__(0,'1')),
            ('rehashed false PASS summary','exact_checks.json',lambda x:x.update(total_exact_predicates=1)),
            ('rehashed inconsistent count','exact_checks.json',lambda x:x['counts'].update(integer_dp_vs_continuant=1)),
            ('rehashed boolean config','exact_checks.json',lambda x:x.update(max_n=True)),
            ('rehashed changed fixture digest','exact_checks.json',lambda x:x.update(fixture_sha256='0'*64)),
        ]:
            generated_case(name,lambda root,file=file,mutate=mutate:altered_and_rehashed(root,file,mutate))
        generated_case('rehashed noncanonical data',lambda r:((r/'exact_data.json').write_bytes((r/'exact_data.json').read_bytes()+b'\n'),refresh_manifest(r)))
        passed.append(rejected(lambda:check.write_results(base,values),'existing output never overwritten'))
        dangling = temp/'dangling'
        dangling.symlink_to(temp/'uncreated')
        passed.append(rejected(lambda:check.write_results(dangling,values),'dangling output symlink'))
        require(not (temp/'uncreated').exists(),'Rejected output wrote a target')
        source = temp/'relocated'
        source.mkdir()
        (source/'data').mkdir()
        shutil.copyfile(HERE/'check.py',source/'check.py')
        shutil.copyfile(HERE/'data/fixtures.json',source/'data/fixtures.json')
        before = {p.relative_to(source).as_posix():p.read_bytes() for p in source.rglob('*') if p.is_file()}
        env = dict(os.environ)
        env.pop('PYTHONDONTWRITEBYTECODE',None)
        env.pop('PYTHONPYCACHEPREFIX',None)
        hashes = []
        for optimized in (False,True):
            output = temp/('optimized' if optimized else 'ordinary')
            cmd = [sys.executable]+(['-O'] if optimized else [])+['-S',str(source/'check.py'),'--max-n','16','--out',str(output)]
            completed = subprocess.run(cmd,env=env,capture_output=True,text=True,timeout=120)
            require(completed.returncode == 0,'Standalone exact replay failed: '+completed.stderr)
            hashes.append({p.name:p.read_bytes() for p in output.iterdir()})
        require(hashes[0] == hashes[1],'Normal/-O output bytes differ')
        passed.append('normal and optimized exact bytes are identical')
        after = {p.relative_to(source).as_posix():p.read_bytes() for p in source.rglob('*') if p.is_file()}
        require(before == after and not list(source.rglob('__pycache__')),'Direct exact replay changed its source')
        passed.append('standalone exact mode works under -S without source mutation')
        probe = "import sys;sys.path.insert(0,sys.argv[1]);import check\ntry: check.require(False,'runtime probe')\nexcept check.CheckError: print('ACTIVE')\nelse: raise SystemExit(9)\n"
        result = subprocess.run([sys.executable,'-O','-S','-c',probe,str(source)],capture_output=True,text=True,timeout=30)
        require(result.returncode == 0 and result.stdout.strip() == 'ACTIVE','Explicit check inactive under -O')
        passed.append('false runtime predicate is rejected under -O')
        # A deliberately weakened guard demonstrates that the above probe detects disabled assertions.
        mutated = (source/'check.py').read_text().replace("if not condition:\n        raise CheckError(message)","assert condition, message",1)
        require(mutated != (source/'check.py').read_text(),'Failed to construct assertion mutant')
        (source/'check.py').write_text(mutated)
        result = subprocess.run([sys.executable,'-O','-S','-c',probe,str(source)],capture_output=True,text=True,timeout=30)
        require(result.returncode == 9,'Disabled-assert mutation escaped the guard probe')
        passed.append('disabled-assert mutation is detected by the runtime probe')
    if args.diagnostics:
        import diagnostics
        import mpmath as mp
        for name, action in [
            ('boolean diagnostic maximum',lambda:diagnostics.diagnostic_results(True)),
            ('small diagnostic maximum',lambda:diagnostics.diagnostic_results(63)),
            ('excessive diagnostic maximum',lambda:diagnostics.diagnostic_results(513)),
            ('unsupported diagnostic precision',lambda:diagnostics.diagnostic_results(64,50)),
            ('bulk q at lower boundary',lambda:diagnostics.J(2,1)),
            ('bulk q at critical boundary',lambda:diagnostics.J(2,3)),
            ('inverse nonmonotone tail',lambda:diagnostics.inverse([0,1,0],mp.mpf('0.5'))),
            ('inverse below early prefix',lambda:diagnostics.inverse([2,0,3],mp.mpf(1))),
            ('inverse outside range',lambda:diagnostics.inverse([0,1,2],mp.mpf(3))),
        ]:
            passed.append(rejected(action,name))
        numeric = diagnostics.diagnostic_results(64,90)
        for name, mutate in [
            ('wrong numeric schema',lambda x:x.update(schema='wrong')),
            ('missing numerical warning',lambda x:x.update(warning='PASS')),
            ('wrong numeric version',lambda x:x.update(mpmath_version='uncontrolled')),
            ('boolean numeric precision',lambda x:x.update(decimal_precision=True)),
            ('wrong numerical total',lambda x:x.update(numerical_predicate_total=0)),
            ('inconsistent numeric count inventory',lambda x:(x['numerical_predicate_counts'].update(numerical_inverse_residual=1),x.update(numerical_predicate_total=sum(x['numerical_predicate_counts'].values())))),
            ('missing numeric family',lambda x:x['bulk'].pop()),
            ('missing numerical degree row',lambda x:x['bulk'][0]['rows'].pop()),
            ('nonfinite numerical row',lambda x:x['bulk'][0]['rows'][0].update(scaled_log_ratio='NaN')),
            ('floating numeric row value',lambda x:x['bulk'][0]['rows'][0].update(scaled_log_ratio=1.0)),
            ('boolean inverse ceiling',lambda x:x['inverse_displacement'][0]['rows'][0].update(base_ceiling=True)),
            ('missing exact-base normalization',lambda x:x['inverse_displacement'][0].update(exact_base_interpolation=False)),
            ('wrong inverse family order',lambda x:x['inverse_displacement'].reverse()),
        ]:
            value = copy.deepcopy(numeric)
            mutate(value)
            passed.append(rejected(lambda value=value:diagnostics.validate_diagnostics(value),name))
        with tempfile.TemporaryDirectory(prefix='report202-numeric-guards-') as temp:
            root = Path(temp)/'generated'
            values = check.exact_results(16)
            values['numerical_diagnostics.json'] = numeric
            check.write_results(root,values)
            changed = copy.deepcopy(numeric)
            changed['bulk'][0]['rows'][0]['scaled_log_ratio'] = '12345.0'
            (root/'numerical_diagnostics.json').write_bytes(check.canonical_bytes(changed))
            refresh_manifest(root)
            passed.append(rejected(lambda:check.validate_generated(root,verify_diagnostics=True),
                                   'rehashed plausible but false numerical data fails full replay'))
    for name in ('check.py','diagnostics.py','test_guards.py'):
        tree = ast.parse((HERE/name).read_text())
        require(not any(isinstance(node,ast.Assert) for node in ast.walk(tree)), 'Production source contains a disableable assertion')
        passed.append('no disableable assert statements in '+name)
    print(json.dumps({'schema':'report202-guard-tests-v1','status':'PASS','guard_checks':len(passed),'checks':passed},sort_keys=True,indent=2))


if __name__ == '__main__':
    main()
