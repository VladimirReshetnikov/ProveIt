#!/usr/bin/env python3
"""Normal/-O positive runs, named negative controls, hashes, clean-directory replay.

Runs only local files, in temporary directories. Mutants pass only on the precise
expected diagnostic and exit code 2; a crash or unrelated failure is a failure.
The exact checker needs SymPy; this harness and manifest checker use stdlib.
"""
import argparse
import copy
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile

ROOT=Path(__file__).resolve().parent
class ValidationError(Exception): pass

def need(ok,msg):
    if not ok: raise ValidationError(msg)

def run(command,cwd):
    return subprocess.run(command,cwd=cwd,text=True,capture_output=True,timeout=180)

def fingerprint(root):
    return {p.relative_to(root).as_posix():hashlib.sha256(p.read_bytes()).hexdigest()
            for p in sorted(root.rglob('*')) if p.is_file() and p.name not in {'validation_results.json','MANIFEST.json'}}

def success(p,label):
    need(p.returncode==0,f'{label}: exit {p.returncode}\n{p.stdout}\n{p.stderr}')

def reject(p,code,label,prefix='CHECK_FAILED'):
    expected=f'{prefix} {code}:'
    need(p.returncode==2 and p.stderr.startswith(expected) and 'Traceback' not in p.stderr,
         f'{label}: expected exit 2 and {expected!r}, got exit {p.returncode}, stdout={p.stdout!r}, stderr={p.stderr!r}')

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--output',type=Path)
    ap.add_argument('--with-numerics',action='store_true',help='also replay optional exploratory mpmath fits normally and under -O')
    args=ap.parse_args()
    before=fingerprint(ROOT)
    report={'status':'PASS','baseline_runs':[],'fixture_mutations':[],'manifest_mutations':[]}
    with tempfile.TemporaryDirectory(prefix='report113-replay-') as tmp:
        temp=Path(tmp)
        fresh=temp/'fresh-checks'
        shutil.copytree(ROOT,fresh)
        for cache in fresh.rglob('__pycache__'):shutil.rmtree(cache)
        # Each baseline runs from an unrelated CWD. Stored result is checked too.
        expected=json.loads((ROOT/'exact_results.json').read_text())
        for optimized in [False,True]:
            command=[sys.executable]+(['-O'] if optimized else [])+[str(fresh/'exact_check.py')]
            p=run(command,temp);success(p,'fresh exact run')
            need(json.loads(p.stdout)==expected,'fresh exact output differs from delivered exact_results.json')
            report['baseline_runs'].append({'optimized':optimized,'exit_code':p.returncode,'matches_frozen_exact_result':True})
        if args.with_numerics:
            numerical_expected=json.loads((ROOT/'exploratory_results.json').read_text())
            report['exploratory_replay']=[]
            for optimized in [False,True]:
                command=[sys.executable]+(['-O'] if optimized else [])+[str(fresh/'exploratory_fit.py')]
                p=run(command,temp);success(p,'exploratory numerical replay')
                need(json.loads(p.stdout)==numerical_expected,'exploratory numerical output differs from frozen results')
                report['exploratory_replay'].append({'optimized':optimized,'matches_frozen_exploratory_result':True,'certified':False})
        fixture=json.loads((fresh/'fixtures.json').read_text())
        mutations=[
            ('unknown_key','SCHEMA_KEYS',lambda f:f.update(extra='1')),
            ('boolean_version','SCHEMA_PARAMETER',lambda f:f.update(schema_version=True)),
            ('wrong_term_count','SCHEMA_LENGTH',lambda f:f['display_terms'].pop()),
            ('noncanonical_rational','SCHEMA_RATIONAL',lambda f:f.update(catalan_M='240/2366')),
            ('wrong_initial_value','INITIAL_VALUES',lambda f:f['initial_values'].__setitem__(0,'2')),
            ('changed_display_term','OEIS_DISPLAY',lambda f:f['display_terms'].__setitem__(28,'10415453732637697')),
            ('wrong_pole_coefficient','POLE_COEFFICIENT',lambda f:f.update(pole_coefficient='61')),
            ('factorial_60_instead_of_30','FACTORIAL_COEFFICIENT',lambda f:f.update(factorial_coefficient='60')),
            ('wrong_normalized_flow','NORMALIZED_FLOW',lambda f:f['normalized_flow'].__setitem__(0,'5/3')),
            ('lyapunov_sign_flip','LYAPUNOV_IDENTITY',lambda f:f['lyapunov_coefficients'].__setitem__(2,'20/9')),
            ('wrong_alpha','ALPHA_ROOT',lambda f:f['alpha'].__setitem__(0,'7')),
            ('wrong_fowler_coefficient','FOWLER_ODE',lambda f:f['fowler_coefficients'].__setitem__(2,'48')),
            ('wrong_indicial_constant','INDICIAL_POLYNOMIAL',lambda f:f['D_coefficients_ascending'].__setitem__(0,'-59')),
            ('weakened_denominator_fixture','DENOMINATOR_BOUND',lambda f:f.update(denominator_lower_bound='591')),
            ('wrong_catalan_constant','CATALAN_CONSTANT',lambda f:f.update(catalan_M='121/1183')),
            ('wrong_a20_imaginary_sign','PSI_A20',lambda f:f['a20'].__setitem__(1,'-57/17978')),
            ('wrong_mixed_sector','PSI_A11',lambda f:f['a11'].__setitem__(0,'1/7')),
            ('lost_relative_factor_two','TRANSFER_MULTIPLIER',lambda f:f.update(transfer_relative_multiplier='1')),
            ('wrong_first_stirling','STIRLING_CORRECTION',lambda f:f['stirling_correction_ascending'].__setitem__(1,'-3/2')),
            ('wrong_second_stirling','SECOND_STIRLING_CORRECTION',lambda f:f['second_stirling_correction_ascending'].__setitem__(1,'35/12')),
            ('wrong_lambert_bernoulli_sign','LAMBERT_SECOND_CORRECTION',lambda f:f['lambert_second_correction'].__setitem__(2,'-1/12')),
        ]
        for label,code,mutate in mutations:
            altered=copy.deepcopy(fixture);mutate(altered)
            fn=temp/(label+'.json');fn.write_text(json.dumps(altered))
            p=run([sys.executable,'-O',str(fresh/'exact_check.py'),'--fixture',str(fn)],temp)
            reject(p,code,label)
            report['fixture_mutations'].append({'name':label,'expected_diagnostic':code,'exit_code':p.returncode,'optimized':True})
        dupe=temp/'duplicate.json';dupe.write_text((fresh/'fixtures.json').read_text().replace('"schema_version": 1','"schema_version": 1, "schema_version": 1'))
        p=run([sys.executable,'-O',str(fresh/'exact_check.py'),'--fixture',str(dupe)],temp)
        reject(p,'SCHEMA_DUPLICATE','duplicate_fixture_key')
        report['fixture_mutations'].append({'name':'duplicate_fixture_key','expected_diagnostic':'SCHEMA_DUPLICATE','exit_code':2,'optimized':True})
        # Mutate a large term outside the externally supplied OEIS prefix.
        lines=(fresh/'recurrence_terms_0_500.txt').read_text().splitlines()
        n,last=lines[-1].split();lines[-1]=f'{n} {int(last)+1}'
        changed=temp/'changed_terms.txt';changed.write_text('\n'.join(lines)+'\n')
        p=run([sys.executable,'-O',str(fresh/'exact_check.py'),'--terms-file',str(changed)],temp)
        reject(p,'RECURRENCE_TERMS','changed_term_500')
        report['fixture_mutations'].append({'name':'changed_term_500','expected_diagnostic':'RECURRENCE_TERMS','exit_code':2,'optimized':True})
        manifest_script=fresh/'check_manifest.py'
        simple=temp/'manifest-controls';simple.mkdir();(simple/'payload.txt').write_text('abc\n')
        success(run([sys.executable,str(manifest_script),str(simple),'--write'],temp),'manifest generation')
        base=json.loads((simple/'MANIFEST.json').read_text())
        mm=[
            ('unknown_manifest_key','MANIFEST_SCHEMA',lambda f:f.update(extra=0)),
            ('boolean_manifest_version','MANIFEST_VERSION',lambda f:f.update(schema_version=True)),
            ('duplicate_manifest_path','MANIFEST_DUPLICATE_PATH',lambda f:f['files'].append(copy.deepcopy(f['files'][0]))),
            ('parent_path','MANIFEST_PATH',lambda f:f['files'][0].update(path='../payload.txt')),
            ('absolute_path','MANIFEST_PATH',lambda f:f['files'][0].update(path='/payload.txt')),
            ('backslash_path','MANIFEST_PATH',lambda f:f['files'][0].update(path='dir\\payload.txt')),
            ('self_manifest_path','MANIFEST_PATH',lambda f:f['files'][0].update(path='MANIFEST.json')),
            ('boolean_size','MANIFEST_BYTES',lambda f:f['files'][0].update(bytes=True)),
            ('invalid_digest','MANIFEST_HASH_FORMAT',lambda f:f['files'][0].update(sha256='xyz')),
            ('changed_size','MANIFEST_SIZE',lambda f:f['files'][0].update(bytes=5)),
            ('changed_digest','MANIFEST_HASH',lambda f:f['files'][0].update(sha256='0'*64)),
        ]
        for label,code,mutate in mm:
            altered=copy.deepcopy(base);mutate(altered)
            (simple/'MANIFEST.json').write_text(json.dumps(altered))
            p=run([sys.executable,'-O',str(manifest_script),str(simple)],temp)
            reject(p,code,label,'MANIFEST_FAILED')
            report['manifest_mutations'].append({'name':label,'expected_diagnostic':code,'exit_code':2,'optimized':True})
        # Structural filesystem and duplicate-key controls.
        for label,code in [('extra_file','MANIFEST_INVENTORY'),('missing_file','MANIFEST_INVENTORY'),('symlink','MANIFEST_SYMLINK'),('duplicate_manifest_key','MANIFEST_DUPLICATE_KEY')]:
            (simple/'MANIFEST.json').write_text(json.dumps(base))
            (simple/'payload.txt').write_text('abc\n')
            if label=='extra_file':(simple/'extra.txt').write_text('x')
            if label=='missing_file':(simple/'payload.txt').unlink()
            if label=='symlink':(simple/'link.txt').symlink_to(simple/'payload.txt')
            if label=='duplicate_manifest_key':(simple/'MANIFEST.json').write_text(json.dumps(base).replace('"schema_version": 1','"schema_version": 1, "schema_version": 1'))
            p=run([sys.executable,'-O',str(manifest_script),str(simple)],temp)
            reject(p,code,label,'MANIFEST_FAILED')
            report['manifest_mutations'].append({'name':label,'expected_diagnostic':code,'exit_code':2,'optimized':True})
            for artifact in ['extra.txt','link.txt']:
                if (simple/artifact).exists() or (simple/artifact).is_symlink():(simple/artifact).unlink()
        # Fresh inventory excludes no delivered source file; all are hashed.
        success(run([sys.executable,str(manifest_script),str(fresh),'--write'],temp),'fresh manifest creation')
        success(run([sys.executable,'-O',str(manifest_script),str(fresh)],temp),'fresh manifest optimized validation')
        report['fresh_directory_replay']={'copied_all_delivered_files':True,'unrelated_working_directory':True,'exact_result_matches':True,'strict_manifest_pass':True}
    after=fingerprint(ROOT)
    need(before==after,'source bytes changed during validation')
    report['source_checks_unchanged']=True
    report['before_sha256']=before
    report['after_sha256']=after
    report['hash_scope_exclusions']=['MANIFEST.json','validation_results.json']
    report['limitations']=['Negative controls validate specific rejection paths; they do not establish general security or formal verification.',
                          'The checkers use exceptions under -O, not removable assertions.',
                          'Fresh-directory replay requires installed Python dependencies; it does not provision a clean operating system.',
                          'Exploratory fits are separate and are not converted into certified bounds by this harness.']
    data=json.dumps(report,indent=2)+'\n'
    if args.output:args.output.write_text(data)
    print(data,end='')
if __name__=='__main__':
    try:main()
    except ValidationError as exc:
        print(f'VALIDATION_FAILED {exc}',file=sys.stderr);sys.exit(2)
