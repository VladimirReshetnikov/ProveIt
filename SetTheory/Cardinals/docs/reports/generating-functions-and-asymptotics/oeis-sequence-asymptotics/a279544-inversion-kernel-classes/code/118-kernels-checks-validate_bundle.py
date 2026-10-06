#!/usr/bin/env python3
"""Bounded normal/-O replay, fresh-directory checks and semantic mutation tests."""
import argparse
from concurrent.futures import ThreadPoolExecutor, as_completed
from copy import deepcopy
from fractions import Fraction as F
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import time
sys.dont_write_bytecode=True
from check import CheckFailure, exact_json, inventory, need, decimal_outward
ROOT=Path(__file__).resolve().parent
FIXTURE='fixtures/certificate.json'
PROCESS_SECONDS=45
TOTAL_SECONDS=1200
WORKERS=4

def seal(root):
    files=inventory(root);files.pop('MANIFEST.json',None)
    (root/'MANIFEST.json').write_text(json.dumps({'format':1,'files':files},indent=2,sort_keys=True)+'\n')

def invoke(root,optimized,deadline,script='check.py'):
    remaining=deadline-time.monotonic();need(remaining>0,'HARNESS_DEADLINE')
    env=dict(os.environ);env['PYTHONDONTWRITEBYTECODE']='1';env['PYTHONHASHSEED']='0'
    command=[sys.executable,'-B']+(['-O'] if optimized else [])+[str(root/script)]
    try:r=subprocess.run(command,cwd=root,env=env,capture_output=True,text=True,timeout=min(PROCESS_SECONDS,remaining))
    except subprocess.TimeoutExpired:raise CheckFailure('HARNESS_TIMEOUT',script) from None
    need(not r.stderr,'HARNESS_STDERR',r.stderr[:200])
    need(len(r.stdout)<=262144,'HARNESS_OUTPUT_LIMIT')
    try:obj=json.loads(r.stdout)
    except ValueError:raise CheckFailure('HARNESS_NONJSON',r.stdout[:200]) from None
    return r.returncode,obj

def paths(value,path=()):
    if type(value) is dict:
        for key,v in value.items():yield from paths(v,path+(key,))
    elif type(value) is list:
        for key,v in enumerate(value):yield from paths(v,path+(key,))
    else:yield path,value

def set_value(root,path,value):
    f=exact_json(root/FIXTURE,'HARNESS_FIXTURE');target=f
    for key in path[:-1]:target=target[key]
    target[path[-1]]=value
    (root/FIXTURE).write_text(json.dumps(f,indent=2)+'\n')

def semantic_cases(f):
    cases=[]
    for path,value in paths(f):
        changed=value+1 if type(value) is int else value+' changed'
        group=path[0]
        if group=='schema_version':diagnostic='FIXTURE_VERSION'
        elif group in ('provenance','ranges','tails'):
            diagnostic={'provenance':'PROVENANCE','ranges':'RANGE','tails':'TAIL'}[group]+'_'+str(path[1]).upper()
        elif group=='sequences':diagnostic='EXTERNAL_PREFIX' if path[1]=='external_prefix' else 'INTERNAL_TERMS'
        elif group=='gamma':
            changed=str(F(value)+1);diagnostic='GAMMA_'+path[1].upper()
        elif group=='limitations':diagnostic='LIMITATIONS'
        elif group=='enclosures':
            places=52 if path[1]=='C' else 24
            changed=decimal_outward(F(value)+(-1 if path[-1]=='lower' else 1)*F(1,10**places),places)
            diagnostic={'C':'C_ENCLOSURE','h':'H_JET_ENCLOSURES','c1':'C1_ENCLOSURE','c2':'C2_ENCLOSURE'}[path[1]]
        elif group=='companion':
            key=path[1]
            if key in ('provenance','parameters'):diagnostic='COMPANION_'+key.upper()+'_'+str(path[2]).upper()
            elif key in ('external_prefix','internal_terms'):diagnostic='COMPANION_'+key.upper()
            elif key in ('F_derivative','C'):
                item=f['companion'][key];mid=(F(item['lower'])+F(item['upper']))/2
                changed=decimal_outward(mid,16)
                diagnostic='COMPANION_DERIVATIVE_ENCLOSURE' if key=='F_derivative' else 'COMPANION_C_ENCLOSURE'
            elif key=='refined':
                if path[2]=='parameters':diagnostic='COMPANION_REFINED_PARAMETER_'+str(path[3]).upper()
                else:
                    places={'C':33,'c1':31,'c2':29}[path[2]]
                    changed=decimal_outward(F(value)+(-1 if path[-1]=='lower' else 1)*F(1,10**places),places)
                    diagnostic='COMPANION_REFINED_'+path[2].upper()
            else:raise CheckFailure('HARNESS_COVERAGE',path)
        else:raise CheckFailure('HARNESS_COVERAGE',path)
        cases.append(('field_'+'.'.join(map(str,path)),diagnostic,lambda r,p=path,v=changed:set_value(r,p,v),True,path))
    return cases

def extra_cases(f):
    cases=[]
    def edit_object(root,path,missing):
        obj=exact_json(root/FIXTURE,'HARNESS_FIXTURE');target=obj
        for k in path:target=target[k]
        if missing:target.pop(next(iter(target)))
        else:target['unexpected']=0
        (root/FIXTURE).write_text(json.dumps(obj)+'\n')
    objects=[((),'FIXTURE_SCHEMA'),(('provenance',),'PROVENANCE_SCHEMA'),(('ranges',),'RANGE_SCHEMA'),(('sequences',),'SEQUENCE_SCHEMA'),(('tails',),'TAIL_SCHEMA'),(('enclosures',),'ENCLOSURE_SCHEMA'),(('gamma',),'GAMMA_SCHEMA'),(('companion',),'COMPANION_SCHEMA'),(('companion','parameters'),'COMPANION_PARAMETERS_SCHEMA'),(('companion','refined'),'COMPANION_REFINED_SCHEMA')]
    for path,diag in objects:
        for missing in (True,False):cases.append(('schema_'+('.'.join(path) or 'root')+('_missing' if missing else '_extra'),diag,lambda r,p=path,m=missing:edit_object(r,p,m),True,None))
    def duplicate(root):
        p=root/FIXTURE;p.write_text(p.read_text().replace('{','{"schema_version":1,',1))
    def cache(root):(root/'__pycache__').mkdir();(root/'__pycache__/extra.pyc').write_bytes(b'cache')
    def manifest_edit(root,key,value):
        p=root/'MANIFEST.json';m=exact_json(p,'HARNESS_MANIFEST');m[key]=value;p.write_text(json.dumps(m))
    cases += [
        ('boolean_range','RANGE_COEFFICIENT_N_MAX',lambda r:set_value(r,('ranges','coefficient_n_max'),True),True,None),
        ('boolean_term','SEQUENCE_INTEGER',lambda r:set_value(r,('sequences','external_prefix',0),True),True,None),
        ('boolean_companion_term','COMPANION_SEQUENCE_INTEGER',lambda r:set_value(r,('companion','external_prefix',0),True),True,None),
        ('float_number','FIXTURE_JSON',lambda r:set_value(r,('ranges','coefficient_n_max'),80.0),True,None),
        ('noncanonical_rational','GAMMA_VALUE',lambda r:set_value(r,('gamma','g_half',1),'6/16'),True,None),
        ('zero_denominator','GAMMA_VALUE',lambda r:set_value(r,('gamma','g_half',1),'3/0'),True,None),
        ('short_sequence','SEQUENCE_LENGTH',lambda r:set_value(r,('sequences','internal_terms'),[1]),True,None),
        ('short_companion_sequence','COMPANION_SEQUENCE_LENGTH',lambda r:set_value(r,('companion','internal_terms'),[1]),True,None),
        ('short_jet','ENCLOSURE_LENGTH',lambda r:set_value(r,('enclosures','h'),[]),True,None),
        ('invalid_decimal','ENCLOSURE_VALUE',lambda r:set_value(r,('enclosures','C','lower'),'nan'),True,None),
        ('reversed_interval','ENCLOSURE_VALUE',lambda r:set_value(r,('enclosures','C','lower'),f['enclosures']['C']['upper']),True,None),
        ('duplicate_key','FIXTURE_JSON',duplicate,True,None),
        ('malformed_json','FIXTURE_JSON',lambda r:(r/FIXTURE).write_text('{invalid'),True,None),
        ('nonfinite_json','FIXTURE_JSON',lambda r:(r/FIXTURE).write_text('{"schema_version":NaN}'),True,None),
        ('oversized_integer','FIXTURE_JSON',lambda r:(r/FIXTURE).write_text('{"schema_version":'+('1'*101)+'}'),True,None),
        ('changed_unsealed','INTEGRITY_HASH',lambda r:(r/'README.md').write_text('changed'),False,None),
        ('missing_fixture','INTEGRITY_MISSING',lambda r:(r/FIXTURE).unlink(),False,None),
        ('missing_manifest','INTEGRITY_MISSING',lambda r:(r/'MANIFEST.json').unlink(),False,None),
        ('unlisted_file','INTEGRITY_UNLISTED',lambda r:(r/'extra.txt').write_text('unlisted'),False,None),
        ('unlisted_bytecode','INTEGRITY_UNLISTED',cache,False,None),
        ('symlink','INTEGRITY_SYMLINK',lambda r:(r/'link').symlink_to('README.md'),False,None),
        ('fifo','INTEGRITY_SPECIAL_FILE',lambda r:os.mkfifo(r/'extra.fifo'),False,None),
        ('oversized_file','INTEGRITY_SIZE',lambda r:(r/FIXTURE).write_text(' '*262145),False,None),
        ('duplicate_manifest_key','INTEGRITY_MANIFEST',lambda r:(r/'MANIFEST.json').write_text('{"format":1,"format":1,"files":{}}'),False,None),
        ('manifest_boolean','INTEGRITY_MANIFEST',lambda r:manifest_edit(r,'format',True),False,None),
        ('manifest_unsafe_path','INTEGRITY_MANIFEST',lambda r:manifest_edit(r,'files',{'../escape':'0'*64}),False,None),
    ]
    def replace(root,file,old,new):
        p=root/file;text=p.read_text();need(text.count(old)==1,'HARNESS_SOURCE_MATCH',old);p.write_text(text.replace(old,new))
    for label,file,old,new,diag in [
        ('root_recurrence','check.py','r[n]=(2*r[n-1]','r[n]=(3*r[n-1]','SMALL_ROOT_CATALAN'),
        ('kernel_b','check.py','b=pmul(x,padd(one,ps(z,-1),ps(pmul(z,x),-1)))','b=pmul(x,padd(one,ps(z,-2),ps(pmul(z,x),-1)))','FUNCTIONAL_G'),
        ('inverse_e3','check.py','m(-1,-2,0,2,0,0)','m(-2,-2,0,2,0,0)','INVERSE_E3'),
        ('derivative_bound','check.py','Q=F(9,8); V=','Q=F(8,8); V=','DERIVATIVE_V_BOUND'),
        ('Machin_angle','check.py','(t4-F(1,239))/(1+t4/F(239))==1','(t4-F(1,239))/(1+t4/F(239))==2','MACHIN_TANGENT_IDENTITY'),
        ('jet_tail','check.py','40000*5==200000','40000*5==200001','JET_H_TAIL_BOUND'),
        ('companion_scalar','companion.py','e=-2*x*(z*x+z-1)/(x-1)\n    A=','e=-3*x*(z*x+z-1)/(x-1)\n    A=','COMPANION_SCALAR_IDENTITY'),
        ('zero_series_divisor','check.py','    Q=F(9,8); V=','    unused=inv([0,1])\n    Q=F(9,8); V=','SERIES_INVERSE_ZERO'),
        ('negative_interval_sqrt','companion.py','    bound=denominator_bounds()\n    sqrt2=Interval(2).sqrt()','    bound=denominator_bounds()\n    sqrt2=Interval(-2).sqrt()','COMPANION_NEGATIVE_SQRT'),
        ('zero_interval_divisor','companion.py','    bound=denominator_bounds()\n    sqrt2=Interval(2).sqrt()','    bound=denominator_bounds()\n    unused=1/Interval(-1,1)\n    sqrt2=Interval(2).sqrt()','COMPANION_INTERVAL_ZERO_DIVISOR'),
        ('companion_quotient_tail','companion.py','4*Y+8*Y*12<100','4*Y+8*Y*12<1','COMPANION_QUOTIENT_TAIL')]:
        cases.append(('corrupted_math_'+label,diag,lambda r,fi=file,a=old,b=new:replace(r,fi,a,b),True,None))
    return cases

def negative_one(base,temp,index,case,deadline):
    label,diagnostic,mutate,reseal,path=case
    root=temp/('case-'+str(index));shutil.copytree(base,root);mutate(root)
    if reseal:seal(root)
    for mode in (False,True):
        rc,obj=invoke(root,mode,deadline)
        need(rc==1 and obj.get('status')=='FAIL' and obj.get('diagnostic')==diagnostic,
             'MUTATION_DIAGNOSTIC',f'{label}, optimized={mode}, expected={diagnostic}, rc={rc}, got={obj}')
    shutil.rmtree(root)
    return {'name':label,'diagnostic':diagnostic,'manifest_resealed':reseal,'normal_and_optimized':'PASS'}

def run():
    deadline=time.monotonic()+TOTAL_SECONDS;before=inventory(ROOT)
    rc,normal=invoke(ROOT,False,deadline);need(rc==0 and normal.get('status')=='PASS','BASELINE_NORMAL',normal)
    rc,optimized=invoke(ROOT,True,deadline);need(rc==0 and optimized==normal,'BASELINE_OPTIMIZED',optimized)
    f=exact_json(ROOT/FIXTURE,'HARNESS_FIXTURE');semantic=semantic_cases(f);extra=extra_cases(f)
    covered={p for *_,p in semantic};need(covered=={p for p,_ in paths(f)},'HARNESS_COVERAGE')
    reports=[]
    with tempfile.TemporaryDirectory(prefix='report118-exact-replay-') as tempname:
        temp=Path(tempname);fresh=temp/'fresh';shutil.copytree(ROOT,fresh);fresh_before=inventory(fresh)
        for mode in (False,True):
            rc,obj=invoke(fresh,mode,deadline);need(rc==0 and obj==normal,'FRESH_REPLAY',obj)
        need(inventory(fresh)==fresh_before,'FRESH_MUTATED')
        cases=semantic+extra
        with ThreadPoolExecutor(max_workers=WORKERS) as pool:
            futures={pool.submit(negative_one,ROOT,temp,j,c,deadline):j for j,c in enumerate(cases)}
            for future in as_completed(futures):reports.append((futures[future],future.result()))
    after=inventory(ROOT);need(before==after,'SOURCE_MUTATED')
    return {'status':'PASS','kind':'BOUNDED_READER_REPLAY','normal_equals_optimized':True,
            'fresh_normal_and_optimized':True,'source_unchanged':True,'baseline':normal,
            'fixture_leaf_values_mutated':len(semantic),'all_fixture_leaves_covered':True,
            'named_mutations':[r for _,r in sorted(reports)],'mutation_runs':2*len(reports),
            'source_hashes_before':before,'source_hashes_after':after,
            'bounds':{'subprocess_seconds':PROCESS_SECONDS,'total_seconds':TOTAL_SECONDS,
                      'max_parallel_subprocesses':WORKERS,'input_file_bytes':262144},
            'scope':'Finite exact arithmetic, strict input/inventory validation, and negative testing. Analytic hypotheses are proved in the report.'}

def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--output',type=Path);args=ap.parse_args()
    try:
        if args.output:need(not args.output.resolve().is_relative_to(ROOT),'OUTPUT_LOCATION')
        result=run();text=json.dumps(result,indent=2,sort_keys=True)+'\n'
        if args.output:args.output.write_text(text)
        else:print(text,end='')
    except CheckFailure as e:
        print(json.dumps({'status':'FAIL','diagnostic':e.name,'detail':e.detail},indent=2));return 1
    except Exception as e:
        print(json.dumps({'status':'ERROR','diagnostic':'HARNESS_EXCEPTION','detail':type(e).__name__+': '+str(e)},indent=2));return 2
    return 0
if __name__=='__main__':sys.exit(main())
