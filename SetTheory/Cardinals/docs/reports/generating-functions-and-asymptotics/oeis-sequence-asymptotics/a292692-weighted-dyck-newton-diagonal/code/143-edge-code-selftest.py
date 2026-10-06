#!/usr/bin/env python3
"""Disposable entrypoint and semantic mutations, in normal and optimized Python.

Called by check.py selftest. Every mutant is tested through the real fixed-path
checker in a temporary copy; original inputs are never modified. The verifier
does not rely on a fixture hash, so value mutations reach semantic validation.
Only temporary files are written. This is not a hostile-code sandbox test.
"""
import sys
if not sys.flags.isolated:
    sys.stderr.write('REJECTED: isolated Python (-I) is required before any imports\n')
    raise SystemExit(2)
sys.dont_write_bytecode = True

import copy
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import tempfile


ROOT = Path(__file__).resolve().parent.parent
FILES = ('code/check.py','code/edge.py','code/profile.py','code/selftest.py',
         'checks/fixtures.json')


def need(condition, message):
    if not condition:
        raise RuntimeError(message)


def fingerprint(root):
    return {name:hashlib.sha256((root/name).read_bytes()).hexdigest()
            for name in FILES}


def invoke(root, optimized, command='check', arguments=(), isolated=True):
    flags = (['-I'] if isolated else [])+(['-O'] if optimized else [])+['-B']
    return subprocess.run([sys.executable]+flags+
                          [str(root/'code/check.py'),command]+list(arguments),
                          cwd=root, capture_output=True, text=True, timeout=120)


def rejected(result, marker, name):
    need(result.returncode==1, name+': expected verifier rejection')
    need(not result.stdout, name+': rejected run wrote success output')
    payload=json.loads(result.stderr)
    need(payload.get('status')=='FAIL' and marker in payload.get('error',''),
         name+': wrong failure reason: '+result.stderr)


def changed(fixture, path, value):
    item=copy.deepcopy(fixture)
    target=item
    for key in path[:-1]:
        target=target[key]
    target[path[-1]]=value
    return item


def run():
    original=fingerprint(ROOT)
    raw=(ROOT/'checks/fixtures.json').read_bytes()
    fixture=json.loads(raw)
    # Structural mutations are intentionally distinct from value mutations.
    variants=[]
    missing=copy.deepcopy(fixture); del missing['edge']['counts']['top_sandwich']
    variants.append(('missing_field',missing,'FIELDS:'))
    extra=copy.deepcopy(fixture); extra['profile']['unrecognized']=0
    variants.append(('extra_field',extra,'FIELDS:'))
    variants += [
        ('boolean_integer_alias',changed(fixture,('edge','top_polynomials',0,'degree'),False),'TYPE:'),
        ('floating_integer_alias',changed(fixture,('edge','maximum_n'),60.0),'TYPE:'),
        ('numeric_rational_alias',changed(fixture,('profile','profile',0),1),'TYPE:'),
        ('noncanonical_rational',changed(fixture,('profile','profile',1),'-14/32'),'VALUE:'),
        ('invalid_rational',changed(fixture,('profile','profile',1),'1/0'),'VALUE:'),
        ('truncated_coefficients',changed(fixture,('profile','profile'),fixture['profile']['profile'][:-1]),'LENGTH:'),
        ('truncated_moment',changed(fixture,('profile','central_moments',16),['0']),'LENGTH:'),
        ('top_coefficient',changed(fixture,('edge','top_polynomials',7,'coefficients',14),'1'),'VALUE:'),
        ('ordinary_sample',changed(fixture,('edge','rows',7,'ordinary',0),'1'),'VALUE:'),
        ('newton_sample',changed(fixture,('edge','rows',7,'newton',1),'1'),'VALUE:'),
        ('auxiliary_sample',changed(fixture,('edge','rows',7,'auxiliary_newton',1),'1'),'VALUE:'),
        ('profile_order_eight',changed(fixture,('profile','profile',8),'0'),'VALUE:'),
        ('inverse_order_seven',changed(fixture,('profile','inverse',7),'0'),'VALUE:'),
        ('nonzero_inverse_residual',changed(fixture,('profile','inverse_residual',7),'1'),'VALUE:'),
        ('underreported_coverage',changed(fixture,('edge','counts','top_sandwich'),1),'VALUE:'),
        ('false_schema',changed(fixture,('schema',),'report143-exact-v1'),'VALUE:'),
        ('false_verdict',changed(fixture,('status',),'SKIP'),'VALUE:')]
    results={}
    with tempfile.TemporaryDirectory(prefix='report143-check-') as directory:
        root=Path(directory)
        for name in FILES:
            (root/name).parent.mkdir(parents=True,exist_ok=True)
            shutil.copyfile(ROOT/name,root/name)
        fixture_path=root/'checks/fixtures.json'
        for optimized in (False,True):
            mode='optimized' if optimized else 'normal'
            baseline=invoke(root,optimized)
            need(baseline.returncode==0, mode+': baseline: '+baseline.stderr)
            need(json.loads(baseline.stdout)['status']=='PASS',mode+': verdict')
            replay=invoke(root,optimized,'replay')
            need(replay.returncode==0 and replay.stdout.encode()==raw,
                 mode+': replay differs from frozen fixture')
            names=[]
            for name,mutant,marker in variants:
                fixture_path.write_text(json.dumps(mutant,sort_keys=True,indent=2)+'\n')
                rejected(invoke(root,optimized),marker,mode+': '+name)
                names.append(name)
            malformed=[
                ('duplicate_json_key','{"schema":"duplicate",'+raw.decode()[1:],'JSON: duplicate key:'),
                ('nonfinite_json_number',raw.decode().replace('"maximum_n": 60','"maximum_n": NaN'),'JSON: non-finite constant:')]
            for name,mutant,marker in malformed:
                fixture_path.write_text(mutant)
                rejected(invoke(root,optimized),marker,mode+': '+name)
                names.append(name)
            fixture_path.write_bytes(raw)
            for command,args in [('check',('--fixture','elsewhere.json')),
                                 ('check',('--output','elsewhere.json')),
                                 ('update',())]:
                rejected(invoke(root,optimized,command,args),'CLI:',mode+': closed CLI')
            # Mathematical guard mutations must fail before fixture comparison.
            for filename,old,new,marker in [
                ('edge.py','V.append((4*a-2)*V[-1]', 'V.append((4*a-1)*V[-1]',
                 'L and V recurrence identity'),
                ('profile.py','h=mul(nu,exp_series(logh,order),order)',
                 'h=mul(nu,exp_series(logh,order),order); h[1]+=1',
                 'independent connected-factorial h-series agreement')]:
                path=root/'code'/filename
                source=path.read_text()
                need(source.count(old)==1,'guard mutation location changed: '+filename)
                path.write_text(source.replace(old,new))
                rejected(invoke(root,optimized),marker,mode+': runtime guard '+filename)
                path.write_text(source)
            # Probe every public guard directly; -O must never disable need().
            for filename in ('edge.py','profile.py','check.py','selftest.py'):
                flags=['-I']+(['-O'] if optimized else [])+['-B']
                source=('import runpy; f=runpy.run_path('+repr(str(root/'code'/filename))+
                        ')["need"]; f(False,"guard sentinel")')
                probe=subprocess.run([sys.executable]+flags+['-c',source],cwd=root,
                                     capture_output=True,text=True,timeout=120)
                need(probe.returncode!=0 and 'guard sentinel' in probe.stderr,
                     mode+': guard disabled: '+filename)
            # Local import shadows and PYTHONPATH do not override stdlib in -I.
            shadow=root/'fractions.py'
            shadow.write_text('raise RuntimeError("cwd import shadow executed")\n')
            safe=invoke(root,optimized)
            need(safe.returncode==0,mode+': isolated shadow import: '+safe.stderr)
            shadow.unlink()
            need(fingerprint(root)==original,mode+': disposable inputs not restored')
            need(not list(root.rglob('__pycache__')),mode+': bytecode output leaked')
            results[mode]={'baseline':'PASS','exact_replay':'PASS',
                           'fixture_mutations_rejected':names,
                           'closed_cli_rejections':3,'arithmetic_guard_mutations':2,
                           'runtime_guards':4,'isolated_cwd_shadow':'PASS',
                           'no_bytecode_files':'PASS'}
        # Fail closed before any non-stdlib import when isolation was omitted.
        nonisolated=invoke(root,False,isolated=False)
        need(nonisolated.returncode==2 and not nonisolated.stdout
             and 'isolated Python (-I)' in nonisolated.stderr,
             'non-isolated entrypoint was not rejected')
    need(fingerprint(ROOT)==original,'selftest changed original companion inputs')
    return {'schema':'report143-selftest-v1','status':'PASS','modes':results,
            'nonisolated_entrypoint':'REJECTED','original_inputs_unchanged':True,
            'scope':'Mutations test validation, not analytic asymptotic claims.'}


if __name__=='__main__':
    print(json.dumps(run(),sort_keys=True,indent=2))
