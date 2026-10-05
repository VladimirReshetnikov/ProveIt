#!/usr/bin/env python3
"""Bounded normal/-O replay, strict manifests, and semantic mutation tests."""
from __future__ import annotations
import argparse
from copy import deepcopy
from fractions import Fraction as F
from hashlib import sha256
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import time
sys.dont_write_bytecode=True
from check import CheckFailure, exact_json, inventory, need
ROOT=Path(__file__).resolve().parent
FIXTURE='fixtures/certificate.json'
PER_PROCESS_SECONDS=15
TOTAL_SECONDS=180

def seal(root):
    files=inventory(root); files.pop('MANIFEST.json',None)
    (root/'MANIFEST.json').write_text(json.dumps({'format':1,'files':files},indent=2,sort_keys=True)+'\n',encoding='utf-8')

def invoke(command,cwd,deadline):
    remaining=deadline-time.monotonic()
    need(remaining>0,'HARNESS_DEADLINE','180-second total replay bound reached')
    env=dict(os.environ);env['PYTHONDONTWRITEBYTECODE']='1';env['PYTHONHASHSEED']='0'
    try:
        result=subprocess.run(command,cwd=cwd,env=env,capture_output=True,text=True,
                              timeout=min(PER_PROCESS_SECONDS,remaining))
    except subprocess.TimeoutExpired:
        raise CheckFailure('HARNESS_TIMEOUT','bounded subprocess did not finish') from None
    need(result.stderr=='','HARNESS_STDERR',result.stderr[:300])
    need(len(result.stdout)<=MAX_OUTPUT,'HARNESS_OUTPUT_LIMIT','subprocess output exceeded limit')
    try: obj=json.loads(result.stdout)
    except (ValueError,TypeError): raise CheckFailure('HARNESS_NONJSON',result.stdout[:300]) from None
    return result.returncode,obj
MAX_OUTPUT=256*1024

def check_call(root,mode,deadline):
    return invoke([sys.executable,'-B']+(['-O'] if mode else [])+[str(root/'check.py')],root,deadline)

def replace_path(root,path,value):
    obj=exact_json(root/FIXTURE,'HARNESS_FIXTURE')
    target=obj
    for key in path[:-1]: target=target[key]
    target[path[-1]]=value
    (root/FIXTURE).write_text(json.dumps(obj,indent=2)+'\n',encoding='utf-8')

def fixture_paths(obj,path=()):
    if type(obj) is dict:
        for key,value in obj.items(): yield from fixture_paths(value,path+(key,))
    elif type(obj) is list:
        for key,value in enumerate(obj): yield from fixture_paths(value,path+(key,))
    else: yield path,obj

def semantic_cases(original):
    result=[]
    for path,value in fixture_paths(original):
        key=path[-1]; group=path[0]
        if path==('schema_version',): changed=2; diagnostic='FIXTURE_VERSION'
        elif group=='model': changed=value+1; diagnostic='MODEL_'+key.upper()
        elif group=='phase':
            changed=str(F(value)+F(1,10)) if key in ('phase_upper','phase_upper_at_10') else str(F(value)+1)
            diagnostic='PHASE_INPUT' if key in ('q','upper_omega') else 'PHASE_FIELD_'+key.upper()
        elif group=='algebra':
            parent=path[1]
            if parent in ('characteristic_ascending','quotient_ascending','real_roots'):
                changed=str(int(value)+1)
            elif parent=='coefficient_multiplier': changed=str(int(value)+1)
            elif parent=='routh_signs': changed=-value
            else: changed=value+1
            diagnostic={'characteristic_ascending':'CHARACTERISTIC_FIXTURE','quotient_ascending':'QUOTIENT_FIXTURE',
                        'routh_signs':'ROUTH_SIGNS_FIXTURE','coefficient_multiplier':'COEFFICIENT_MULTIPLIER',
                        'real_roots':'REAL_ROOT_INDEX','unstable_winding_indices':'UNSTABLE_WINDING_INDEX',
                        'stable_winding_indices':'STABLE_WINDING_INDEX'}.get(parent,'COUNT_'+parent.upper())
        else: raise CheckFailure('HARNESS_COVERAGE','unknown fixture field')
        label='field_'+'.'.join(map(str,path))
        result.append((label,diagnostic,lambda r,p=path,v=changed:replace_path(r,p,v),True,path))
    return result

def extra_cases(original):
    A=int(original['phase']['A']); S=int(original['phase']['S'])
    result=[]
    for name,key,value in [('REAL_POSITIVE','R','0'),('IMAG_POSITIVE','I','0'),
                           ('MODULUS_Q','R',str(2*S)),('PHASE_Q_LOWER','phase_lower','6'),
                           ('PHASE_Q_UPPER','phase_upper','7'),('MODULUS_10','modulus_squared_at_10',str(4*A*A)),
                           ('PHASE_10_UPPER','phase_upper_at_10','8')]:
        result.append(('boundary_'+name,'INEQUALITY_'+name,lambda r,k=key,v=value:replace_path(r,('phase',k),v),True,None))
    def object_edit(root,path,remove=False):
        obj=exact_json(root/FIXTURE,'HARNESS_FIXTURE'); target=obj
        for key in path: target=target[key]
        if remove: target.pop(next(iter(target)))
        else: target['unexpected_field']=0
        (root/FIXTURE).write_text(json.dumps(obj)+'\n')
    for path,diagnostic in [((),'FIXTURE_SCHEMA'),(('model',),'MODEL_SCHEMA'),(('phase',),'PHASE_SCHEMA'),(('algebra',),'ALGEBRA_SCHEMA')]:
        for missing in (False,True):
            result.append(('schema_'+('.'.join(path) or 'root')+('_missing' if missing else '_extra'),diagnostic,
                           lambda r,p=path,m=missing:object_edit(r,p,m),True,None))
    def duplicate(root):
        p=root/FIXTURE;p.write_text(p.read_text().replace('{','{"schema_version":1,',1))
    def unlisted(root): (root/'unexpected.txt').write_text('unlisted\n')
    def cache(root):
        (root/'__pycache__').mkdir();(root/'__pycache__/unexpected.pyc').write_bytes(b'cache')
    def invalid_manifest(root):
        p=root/'MANIFEST.json';obj=exact_json(p,'HARNESS_MANIFEST');obj['format']=True;p.write_text(json.dumps(obj))
    def unsafe_manifest(root):
        p=root/'MANIFEST.json';obj=exact_json(p,'HARNESS_MANIFEST');obj['files']['../escape']='0'*64;p.write_text(json.dumps(obj))
    result.extend([
        ('boolean_order','MODEL_DERIVATIVE_ORDER',lambda r:replace_path(r,('model','derivative_order'),True),True,None),
        ('boolean_count','ALGEBRA_COUNT_SCHEMA',lambda r:replace_path(r,('algebra','full_right'),True),True,None),
        ('float_rational','FIXTURE_JSON',lambda r:replace_path(r,('phase','q'),9.11),True,None),
        ('noncanonical_rational','PHASE_VALUE_SCHEMA',lambda r:replace_path(r,('phase','q'),'1822/200'),True,None),
        ('zero_denominator','PHASE_VALUE_SCHEMA',lambda r:replace_path(r,('phase','q'),'911/0'),True,None),
        ('nonintegral_integer','PHASE_VALUE_SCHEMA',lambda r:replace_path(r,('phase','R'),'1/2'),True,None),
        ('oversized_rational','PHASE_VALUE_SCHEMA',lambda r:replace_path(r,('phase','q'),'1'*1025),True,None),
        ('short_polynomial','ALGEBRA_ARRAY_SCHEMA',lambda r:replace_path(r,('algebra','characteristic_ascending'),['1']),True,None),
        ('boolean_polynomial','ALGEBRA_VALUE_SCHEMA',lambda r:replace_path(r,('algebra','characteristic_ascending',0),True),True,None),
        ('boolean_sign','ALGEBRA_ARRAY_SCHEMA',lambda r:replace_path(r,('algebra','routh_signs',0),True),True,None),
        ('duplicate_json_key','FIXTURE_JSON',duplicate,True,None),
        ('invalid_json','FIXTURE_JSON',lambda r:(r/FIXTURE).write_text('{invalid\n'),True,None),
        ('nonfinite_json','FIXTURE_JSON',lambda r:(r/FIXTURE).write_text('{"schema_version":NaN}\n'),True,None),
        ('oversized_json_integer','FIXTURE_JSON',lambda r:(r/FIXTURE).write_text('{"schema_version":123456789012}\n'),True,None),
        ('changed_unsealed_file','INTEGRITY_HASH',lambda r:(r/'README.md').write_text('modified\n'),False,None),
        ('missing_sealed_file','INTEGRITY_MISSING',lambda r:(r/FIXTURE).unlink(),False,None),
        ('missing_manifest','INTEGRITY_MISSING',lambda r:(r/'MANIFEST.json').unlink(),False,None),
        ('unlisted_file','INTEGRITY_UNLISTED',unlisted,False,None),
        ('unlisted_bytecode','INTEGRITY_UNLISTED',cache,False,None),
        ('symlink','INTEGRITY_SYMLINK',lambda r:(r/'unexpected-link').symlink_to('README.md'),False,None),
        ('special_file','INTEGRITY_SPECIAL_FILE',lambda r:os.mkfifo(r/'unexpected.fifo'),False,None),
        ('boolean_manifest_format','INTEGRITY_MANIFEST',invalid_manifest,False,None),
        ('unsafe_manifest_path','INTEGRITY_MANIFEST',unsafe_manifest,False,None),
    ])
    return result

def package_manifest_tests(temp,deadline):
    base=temp/'package-manifest-base';base.mkdir();(base/'alpha.txt').write_text('alpha\n')
    (base/'nested').mkdir();(base/'nested/beta.txt').write_text('beta\n')
    def call(root,mode=False,write=False):
        return invoke([sys.executable,'-B']+(['-O'] if mode else [])+[str(ROOT/'check_manifest.py'),str(root)]+(['--write'] if write else []),root,deadline)
    rc,obj=call(base,write=True);need(rc==0 and obj.get('status')=='PASS','PACKAGE_BASELINE',obj)
    first=(base/'CHECKSUMS.sha256').read_bytes();rc,obj=call(base,write=True)
    need(rc==0 and (base/'CHECKSUMS.sha256').read_bytes()==first,'PACKAGE_DETERMINISM',obj)
    for mode in (False,True):
        rc,obj=call(base,mode);need(rc==0 and obj.get('status')=='PASS','PACKAGE_BASELINE',obj)
    def duplicate(r):
        p=r/'CHECKSUMS.sha256';text=p.read_text();p.write_text(text+text.splitlines()[0]+'\n')
    def unsafe(r):
        p=r/'CHECKSUMS.sha256';p.write_text(p.read_text().replace('alpha.txt','../alpha.txt'))
    def invalid_digest(r):
        p=r/'CHECKSUMS.sha256';p.write_text('x'+p.read_text()[1:])
    def cache(r):
        (r/'__pycache__').mkdir();(r/'__pycache__/extra.pyc').write_bytes(b'extra')
    cases=[('changed','MANIFEST_HASH',lambda r:(r/'alpha.txt').write_text('changed')),
           ('missing','MANIFEST_FILE_MISSING',lambda r:(r/'alpha.txt').unlink()),
           ('unlisted','MANIFEST_UNLISTED',lambda r:(r/'extra.txt').write_text('extra')),
           ('duplicate','MANIFEST_DUPLICATE',duplicate),('unsafe','MANIFEST_PATH',unsafe),
           ('bad_digest','MANIFEST_FORMAT',invalid_digest),('cache','MANIFEST_UNLISTED',cache),
           ('symlink','MANIFEST_SYMLINK',lambda r:(r/'link').symlink_to('alpha.txt')),
           ('special','MANIFEST_SPECIAL_FILE',lambda r:os.mkfifo(r/'extra.fifo')),
           ('no_manifest','MANIFEST_MISSING',lambda r:(r/'CHECKSUMS.sha256').unlink())]
    reports=[]
    for name,expected,mutate in cases:
        target=temp/('package_'+name);shutil.copytree(base,target);mutate(target)
        for mode in (False,True):
            rc,obj=call(target,mode)
            need(rc==1 and obj.get('status')=='FAIL' and obj.get('diagnostic')==expected,'PACKAGE_MUTATION',f'{name}, optimized={mode}: {obj}')
        reports.append({'name':name,'diagnostic':expected,'normal_and_optimized':'PASS'})
    return {'status':'PASS','write_deterministic':True,'mutations':reports,'mutation_runs':len(reports)*2}

def run():
    deadline=time.monotonic()+TOTAL_SECONDS
    before=inventory(ROOT)
    rc,normal=check_call(ROOT,False,deadline);need(rc==0 and normal.get('status')=='PASS','BASELINE_NORMAL',normal)
    rc,optimized=check_call(ROOT,True,deadline);need(rc==0 and optimized==normal,'BASELINE_OPTIMIZED',optimized)
    original=exact_json(ROOT/FIXTURE,'HARNESS_FIXTURE')
    semantic=semantic_cases(original);extra=extra_cases(original)
    covered={path for _,_,_,_,path in semantic}
    expected={path for path,_ in fixture_paths(original)}
    need(covered==expected and len(semantic)==len(expected),'HARNESS_COVERAGE','not every fixture scalar/array entry is mutated')
    reports=[]
    with tempfile.TemporaryDirectory(prefix='btree-report117-replay-') as temporary:
        temp=Path(temporary)
        fresh=temp/'fresh';shutil.copytree(ROOT,fresh);fresh_before=inventory(fresh)
        for mode in (False,True):
            rc,obj=check_call(fresh,mode,deadline);need(rc==0 and obj==normal,'FRESH_REPLAY',obj)
        need(inventory(fresh)==fresh_before,'FRESH_MUTATED','replay changed files')
        for index,(label,diagnostic,mutate,reseal,path) in enumerate(semantic+extra):
            target=temp/f'mutation-{index:03d}';shutil.copytree(ROOT,target);mutate(target)
            if reseal: seal(target)
            for mode in (False,True):
                rc,obj=check_call(target,mode,deadline)
                need(rc==1 and obj.get('status')=='FAIL' and obj.get('diagnostic')==diagnostic,
                     'MUTATION_DIAGNOSTIC',f'{label}, optimized={mode}; expected {diagnostic}, rc={rc}; {obj}')
            reports.append({'name':label,'diagnostic':diagnostic,'fixture_manifest_resealed':reseal,'normal_and_optimized':'PASS'})
            shutil.rmtree(target)
        package=package_manifest_tests(temp,deadline)
    after=inventory(ROOT);need(before==after,'SOURCE_MUTATED','before/after hashes differ')
    return {'status':'PASS','kind':'BOUNDED_READER_REPLAY','normal_equals_optimized':True,
            'fresh_replay_normal_and_optimized':True,'sources_unchanged':True,
            'exact_baseline':normal,'fixture_scalar_fields_and_array_entries_mutated':len(covered),
            'all_fixture_leaf_values_covered':True,'named_mutations':reports,'mutation_runs':len(reports)*2,
            'package_manifest_tests':package,'source_hashes_before':before,'source_hashes_after':after,
            'bounds':{'subprocess_seconds':PER_PROCESS_SECONDS,'total_seconds':TOTAL_SECONDS,'input_file_bytes':256*1024,
                      'subprocess_output_bytes':MAX_OUTPUT,'fixed_derivative_order':30},
            'scope':'Finite exact replay and negative tests. Does not formally verify the analytic proof or establish priority.'}

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path,help='optional JSON destination outside this sealed checks directory')
    args=parser.parse_args()
    try:
        if args.output: need(not args.output.resolve().is_relative_to(ROOT),'OUTPUT_LOCATION','output must be outside checks directory')
        result=run();text=json.dumps(result,indent=2,sort_keys=True)+'\n'
        if args.output: args.output.write_text(text,encoding='utf-8')
        else: print(text,end='')
    except CheckFailure as error:
        print(json.dumps({'status':'FAIL','diagnostic':error.name,'detail':error.detail},indent=2));return 1
    except Exception as error:
        print(json.dumps({'status':'ERROR','diagnostic':'HARNESS_EXCEPTION','detail':f'{type(error).__name__}: {error}'},indent=2));return 2
    return 0
if __name__=='__main__':sys.exit(main())
