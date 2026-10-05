#!/usr/bin/env python3
"""Replay, integrity, optimization-mode and named-mutation tests for the checks."""
from __future__ import annotations
import argparse
from hashlib import sha256
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
sys.dont_write_bytecode=True
from check import CheckFailure, exact_json, need
ROOT=Path(__file__).resolve().parent

def hashes(root):
    return {p.relative_to(root).as_posix():sha256(p.read_bytes()).hexdigest()
            for p in sorted(root.rglob('*')) if p.is_file() and '__pycache__' not in p.parts}

def seal(root):
    files=hashes(root); files.pop('MANIFEST.json',None)
    (root/'MANIFEST.json').write_text(json.dumps({'format':1,'files':files},indent=2,sort_keys=True)+'\n')

def invoke(root,optimized=False,script='check.py'):
    env=dict(os.environ);env['PYTHONDONTWRITEBYTECODE']='1'
    command=[sys.executable]+(['-O'] if optimized else [])+[str(root/script)]
    completed=subprocess.run(command,cwd=root,env=env,capture_output=True,text=True,timeout=180)
    try: obj=json.loads(completed.stdout)
    except (ValueError,TypeError):
        raise CheckFailure('HARNESS_NONJSON',f'{script}: exit {completed.returncode}; stdout {completed.stdout[:300]!r}; stderr {completed.stderr[:300]!r}') from None
    need(completed.stderr=='','HARNESS_STDERR',completed.stderr[:500])
    return completed.returncode,obj

def change_json(root,rel,key,value):
    p=root/rel;obj=exact_json(p,'HARNESS_JSON');obj[key]=value
    p.write_text(json.dumps(obj,indent=2)+'\n')

def package_manifest_tests(temp):
    base=Path(temp)/'package-manifest-base';base.mkdir()
    (base/'alpha.txt').write_text('alpha\n');(base/'nested').mkdir();(base/'nested/beta.txt').write_text('beta\n')
    def call(root,mode=False,write=False):
        command=[sys.executable,'-B']+(['-O'] if mode else [])+[str(ROOT/'check_manifest.py'),str(root)]+(['--write'] if write else [])
        process=subprocess.run(command,capture_output=True,text=True,timeout=30)
        try:obj=json.loads(process.stdout)
        except ValueError:raise CheckFailure('PACKAGE_MANIFEST_NONJSON',process.stdout[:300]) from None
        need(process.stderr=='','PACKAGE_MANIFEST_STDERR',process.stderr[:300])
        return process.returncode,obj
    rc,obj=call(base,write=True)
    need(rc==0 and obj.get('status')=='PASS','PACKAGE_MANIFEST_WRITE',str(obj))
    first=(base/'CHECKSUMS.sha256').read_bytes()
    rc,obj=call(base,write=True)
    need(rc==0 and (base/'CHECKSUMS.sha256').read_bytes()==first,'PACKAGE_MANIFEST_DETERMINISM','rewrite differs')
    for mode in [False,True]:
        rc,obj=call(base,mode)
        need(rc==0 and obj.get('status')=='PASS','PACKAGE_MANIFEST_BASELINE',str(obj))
    def duplicate(root):
        p=root/'CHECKSUMS.sha256';text=p.read_text();p.write_text(text+text.splitlines()[0]+'\n')
    def unsafe(root):
        p=root/'CHECKSUMS.sha256';text=p.read_text();p.write_text(text.replace('alpha.txt','../alpha.txt'))
    def bad_digest(root):
        p=root/'CHECKSUMS.sha256';text=p.read_text();p.write_text('x'+text[1:])
    def cache(root):
        (root/'__pycache__').mkdir();(root/'__pycache__/extra.pyc').write_bytes(b'extra')
    cases=[
        ('package_changed_file','MANIFEST_HASH',lambda r:(r/'alpha.txt').write_text('changed\n')),
        ('package_unlisted_file','MANIFEST_UNLISTED',lambda r:(r/'extra.txt').write_text('extra\n')),
        ('package_missing_file','MANIFEST_FILE_MISSING',lambda r:(r/'alpha.txt').unlink()),
        ('package_duplicate_entry','MANIFEST_DUPLICATE',duplicate),
        ('package_unsafe_path','MANIFEST_PATH',unsafe),
        ('package_invalid_digest','MANIFEST_FORMAT',bad_digest),
        ('package_unlisted_cache','MANIFEST_UNLISTED',cache),
        ('package_symlink','MANIFEST_SYMLINK',lambda r:(r/'link.txt').symlink_to('alpha.txt')),
        ('package_missing_manifest','MANIFEST_MISSING',lambda r:(r/'CHECKSUMS.sha256').unlink()),
        ('package_special_file','MANIFEST_SPECIAL_FILE',lambda r:os.mkfifo(r/'unexpected.fifo')),
    ]
    reports=[]
    for label,expected,mutate in cases:
        target=Path(temp)/label;shutil.copytree(base,target);mutate(target)
        for mode in [False,True]:
            rc,obj=call(target,mode)
            need(rc==1 and obj.get('status')=='FAIL' and obj.get('diagnostic')==expected,
                 'PACKAGE_MANIFEST_MUTATION',f'{label}, optimized={mode}: {obj}')
        reports.append({'name':label,'expected_diagnostic':expected,'normal_and_optimized':'PASS'})
    return {'status':'PASS','write_deterministic':True,'strict_cache_inventory':True,'mutations':reports,'mutation_runs':20}

def run(with_exploratory=False):
    before=hashes(ROOT)
    rc,normal=invoke(ROOT)
    need(rc==0 and normal.get('status')=='PASS','BASELINE_NORMAL',str(normal))
    rc,optimized=invoke(ROOT,True)
    need(rc==0 and optimized==normal,'BASELINE_OPTIMIZED','-O output differs or failed')
    mutations=[]
    with tempfile.TemporaryDirectory(prefix='order7-reader-replay-') as temp:
        package_manifest=package_manifest_tests(temp)
        fresh=Path(temp)/'fresh-copy'
        shutil.copytree(ROOT,fresh,ignore=shutil.ignore_patterns('__pycache__'))
        fresh_before=hashes(fresh)
        rc,replayed=invoke(fresh)
        need(rc==0 and replayed==normal,'FRESH_REPLAY','fresh-directory result differs')
        need(hashes(fresh)==fresh_before,'FRESH_REPLAY_MUTATED','fresh replay changed source')
        formula='fixtures/reference_formulas.json'
        prefix='fixtures/oeis_A336009_prefix.json'
        terms='fixtures/recurrence_terms_0_500.txt'
        def bad_term(root):
            p=root/terms; rows=p.read_text().splitlines(); rows[200]='200 '+str(int(rows[200].split()[1])+1)
            p.write_text('\n'.join(rows)+'\n')
        def short_terms(root):
            p=root/terms;p.write_text('\n'.join(p.read_text().splitlines()[:-1])+'\n')
        def bad_prefix(root):
            obj=exact_json(root/prefix,'HARNESS_JSON');obj['terms'][30]+=1
            (root/prefix).write_text(json.dumps(obj)+'\n')
        def bool_prefix(root):
            obj=exact_json(root/prefix,'HARNESS_JSON');obj['terms'][0]=True
            (root/prefix).write_text(json.dumps(obj)+'\n')
        def bad_psi(root):
            obj=exact_json(root/formula,'HARNESS_JSON');obj['psi_degree2']['0,1,1']=['-1','0']
            (root/formula).write_text(json.dumps(obj)+'\n')
        def duplicate_key(root):
            p=root/formula;text=p.read_text();p.write_text(text.replace('{','{"pole":"840",',1))
        cases=[
            ('wrong_generated_term','TERMS_METHODS_FIXTURE',bad_term,True),
            ('missing_generated_term','TERMS_COUNT',short_terms,True),
            ('wrong_external_prefix','OEIS_PREFIX_REFERENCE',bad_prefix,True),
            ('boolean_external_integer','OEIS_PREFIX_SCHEMA',bool_prefix,True),
            ('wrong_pole_constant','CONSTANT_POLE_BALANCE',lambda r:change_json(r,formula,'pole','841'),True),
            ('wrong_egf_constant','CONSTANT_EGF',lambda r:change_json(r,formula,'egf','141'),True),
            ('wrong_energy_coefficient','ENERGY_COEFFICIENT',lambda r:change_json(r,formula,'energy_coefficient','-3008678401'),True),
            ('wrong_nonvanishing_ratio','REAL_MODE_RATIO',lambda r:change_json(r,formula,'ratio_bound','168/175'),True),
            ('wrong_surface_coefficient','PSI_COEFFICIENTS',bad_psi,True),
            ('wrong_inverse_shift','INVERSE_SCALE_SHIFT',lambda r:change_json(r,formula,'inverse_shift','4'),True),
            ('duplicate_formula_key','FORMULA_JSON',duplicate_key,True),
            ('invalid_formula_json','FORMULA_JSON',lambda r:(r/formula).write_text('{bad json\n'),True),
            ('modified_unresealed_source','INTEGRITY_HASH',lambda r:(r/'README.md').write_text('changed\n'),False),
            ('missing_sealed_file','INTEGRITY_MISSING',lambda r:(r/formula).unlink(),False),
            ('unlisted_file','INTEGRITY_UNLISTED',lambda r:(r/'unexpected.txt').write_text('extra\n'),False),
        ]
        for label,expected,mutate,reseal in cases:
            target=Path(temp)/label
            shutil.copytree(ROOT,target,ignore=shutil.ignore_patterns('__pycache__'))
            mutate(target)
            if reseal: seal(target)
            observations=[]
            for mode in [False,True]:
                rc,obj=invoke(target,mode)
                need(rc==1 and obj.get('status')=='FAIL' and obj.get('diagnostic')==expected,
                     'MUTATION_DIAGNOSTIC',f'{label}, optimized={mode}: expected {expected}; got rc={rc}, {obj}')
                observations.append({'optimized':mode,'exit_code':rc,'diagnostic':obj['diagnostic']})
            mutations.append({'name':label,'expected_diagnostic':expected,'observations':observations,
                              'fixture_manifest_resealed':reseal})
    exploratory={'run':False,'status':'NOT_RUN'}
    if with_exploratory:
        rc,computed=invoke(ROOT,script='exploratory_fit.py')
        reference=exact_json(ROOT/'fixtures/exploratory_reference.json','EXPLORATORY_REFERENCE_JSON')
        need(rc==0 and computed.get('status')=='EXPLORATORY_ONLY','EXPLORATORY_RUN','fit did not finish as exploratory')
        need(computed==reference,'EXPLORATORY_REPRODUCTION','point-fit output differs; this is not an interval validation')
        exploratory={'run':True,'status':'EXPLORATORY_REPRODUCED','working_decimal_digits':100,
                     'certified_digits':False,'in_fit_residuals_marked':True}
    after=hashes(ROOT)
    need(before==after,'SOURCE_MUTATED','before/after source hashes differ')
    return {'status':'PASS','kind':'READER_SUITE_SELF_TEST','normal_equals_optimized':True,
            'fresh_directory_replay':{'status':'PASS','sources_unchanged':True},
            'exact_baseline':normal,'package_manifest_tests':package_manifest,'named_mutations':mutations,'mutation_runs':2*len(mutations),
            'source_hashes_before':before,'source_hashes_after':after,
            'exploratory_reproduction':exploratory,
            'scope':'A finite test-suite audit, not certification of the analytic proof or infinite monodromy.'}

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--with-exploratory',action='store_true')
    parser.add_argument('--output',type=Path,help='optional JSON destination outside this sealed checks directory')
    args=parser.parse_args()
    try:
        if args.output:
            need(not args.output.resolve().is_relative_to(ROOT),'OUTPUT_LOCATION','write outside the sealed checks directory')
        result=run(args.with_exploratory);text=json.dumps(result,indent=2,sort_keys=True)+'\n'
        if args.output: args.output.write_text(text)
        else: print(text,end='')
    except CheckFailure as e:
        print(json.dumps({'status':'FAIL','diagnostic':e.name,'detail':e.detail},indent=2));return 1
    except Exception as e:
        print(json.dumps({'status':'ERROR','diagnostic':'HARNESS_EXCEPTION','detail':f'{type(e).__name__}: {e}'},indent=2));return 2
    return 0
if __name__=='__main__':sys.exit(main())
