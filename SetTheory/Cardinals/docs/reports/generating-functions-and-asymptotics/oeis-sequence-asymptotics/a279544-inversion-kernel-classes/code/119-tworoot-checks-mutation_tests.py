#!/usr/bin/env python3
"""Bounded exact normal/-O replay and exhaustive fixture-leaf negative testing."""
import argparse
from concurrent.futures import ThreadPoolExecutor, as_completed
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
from support import CheckFailure, exact_json, inventory, need
from exact_math import decimal_outward
ROOT=Path(__file__).resolve().parent
PROCESS_SECONDS=90
TOTAL_SECONDS=1200
WORKERS=4

def seal(root):
    files=inventory(root);files.pop('MANIFEST.json',None)
    (root/'MANIFEST.json').write_text(json.dumps({'format':1,'files':files},indent=2,sort_keys=True)+'\n')

def invoke(root,optimized,deadline):
    remaining=deadline-time.monotonic();need(remaining>0,'HARNESS_DEADLINE')
    env=dict(os.environ);env['PYTHONDONTWRITEBYTECODE']='1';env['PYTHONHASHSEED']='0'
    command=[sys.executable,'-B']+(['-O'] if optimized else [])+[str(root/'run_checks.py')]
    try:r=subprocess.run(command,cwd=root,env=env,capture_output=True,text=True,timeout=min(PROCESS_SECONDS,remaining))
    except subprocess.TimeoutExpired:raise CheckFailure('HARNESS_TIMEOUT','run_checks.py') from None
    need(not r.stderr,'HARNESS_STDERR',r.stderr[:200]);need(len(r.stdout)<=262144,'HARNESS_OUTPUT_LIMIT')
    try:obj=json.loads(r.stdout)
    except ValueError:raise CheckFailure('HARNESS_NONJSON',r.stdout[:200]) from None
    return r.returncode,obj

def leaves(value,path=()):
    if type(value) is dict:
        for k,v in value.items():yield from leaves(v,path+(k,))
    elif type(value) is list:
        for k,v in enumerate(value):yield from leaves(v,path+(k,))
    else:yield path,value

def set_value(root,path,value):
    f=exact_json(root/'fixtures.json','HARNESS_FIXTURE');target=f
    for key in path[:-1]:target=target[key]
    target[path[-1]]=value
    (root/'fixtures.json').write_text(json.dumps(f,indent=2)+'\n')

def semantic_cases(f):
    cases=[]
    for path,value in leaves(f):
        changed=value+1 if type(value) is int else value+' changed';group=path[0]
        if group=='schema_version':diag='FIXTURE_VERSION'
        elif group in ['provenance','ranges','tails']:
            diag={'provenance':'PROVENANCE','ranges':'RANGE','tails':'TAIL'}[group]+'_'+path[1].upper()
        elif group=='sequences':diag='EXTERNAL_PREFIX' if path[1]=='external_prefix' else 'INTERNAL_TERMS'
        elif group=='enclosures':
            changed=decimal_outward(F(value)+(-1 if path[-1]=='lower' else 1)*F(1,10**55),55)
            diag='ENCLOSURE_'+path[1].upper()
        elif group=='gamma':
            changed=str(F(value)+1)
            diag='GAMMA_TRANSFER_COEFFICIENTS' if path[1]=='transfer_coefficients' else 'GAMMA_RATIOS'
        elif group=='corrections':
            if path[1]=='parameters':diag='JET_PARAMETER_'+path[2].upper()
            elif path[1]=='root_jets':changed=str(F(value)+1);diag='JET_ROOT_'+path[2].upper()
            elif path[1]=='enclosures':
                changed=decimal_outward(F(value)+(-1 if path[-1]=='lower' else 1)*F(1,10**80),80)
                diag='JET_ENCLOSURE_'+path[2].upper()
            elif path[1]=='rectangle':
                if path[2]=='N_norm1_upper':changed=str(F(value)+1);diag='JET_RECTANGLE_N_NORM1_FIXTURE'
                else:
                    changed=decimal_outward(F(value)+(-1 if path[-1]=='lower' else 1)*F(1,10**12),12)
                    diag='JET_RECTANGLE_'+path[2].upper()+'_FIXTURE'
            else:raise CheckFailure('HARNESS_COVERAGE',path)
        elif group=='limitations':diag='LIMITATIONS'
        else:raise CheckFailure('HARNESS_COVERAGE',path)
        cases.append(('semantic.'+'.'.join(map(str,path)),diag,lambda r,p=path,v=changed:set_value(r,p,v),True,path))
    return cases

def extra_cases(f):
    cases=[]
    def edit_object(root,path,missing):
        obj=exact_json(root/'fixtures.json','HARNESS_FIXTURE');target=obj
        for k in path:target=target[k]
        if missing:target.pop(next(iter(target)))
        else:target['unexpected']=0
        (root/'fixtures.json').write_text(json.dumps(obj)+'\n')
    objects=[((),'FIXTURE_SCHEMA'),(('provenance',),'PROVENANCE_SCHEMA'),(('ranges',),'RANGE_SCHEMA'),
        (('tails',),'TAIL_SCHEMA'),(('sequences',),'SEQUENCE_SCHEMA'),(('enclosures',),'ENCLOSURE_SCHEMA'),
        (('gamma',),'GAMMA_SCHEMA'),(('gamma','transfer_coefficients'),'GAMMA_TRANSFER_SCHEMA'),
        (('corrections',),'JET_SCHEMA'),(('corrections','parameters'),'JET_PARAMETER_SCHEMA'),
        (('corrections','root_jets'),'JET_ROOT_SCHEMA'),(('corrections','rectangle'),'JET_RECTANGLE_SCHEMA'),
        (('corrections','enclosures'),'JET_ENCLOSURE_SCHEMA')]
    objects += [(('enclosures',key),'ENCLOSURE_VALUE') for key in f['enclosures']]
    objects += [(('corrections','enclosures',key),'JET_ENCLOSURE_VALUE') for key in f['corrections']['enclosures']]
    objects += [(('corrections','rectangle',key),'JET_RECTANGLE_VALUE') for key in ['D_real','D_imag']]
    for path,diag in objects:
        for missing in [False,True]:cases.append(('schema.'+('.'.join(path) or 'root')+('.missing' if missing else '.extra'),diag,lambda r,p=path,m=missing:edit_object(r,p,m),True,None))
    cases += [
      ('schema.boolean_range','RANGE_TREE_N_MAX',lambda r:set_value(r,('ranges','tree_n_max'),True),True,None),
      ('schema.boolean_term','SEQUENCE_INTEGER',lambda r:set_value(r,('sequences','external_prefix',0),True),True,None),
      ('schema.float','FIXTURE_JSON',lambda r:set_value(r,('ranges','tree_n_max'),60.0),True,None),
      ('schema.noncanonical_rational','GAMMA_VALUE',lambda r:set_value(r,('gamma','gamma_ratios',1),'-6/4'),True,None),
      ('schema.zero_denominator','GAMMA_VALUE',lambda r:set_value(r,('gamma','gamma_ratios',1),'-3/0'),True,None),
      ('schema.short_sequence','SEQUENCE_LENGTH',lambda r:set_value(r,('sequences','internal_terms'),[1]),True,None),
      ('schema.short_gamma','GAMMA_LENGTH',lambda r:set_value(r,('gamma','gamma_ratios'),[]),True,None),
      ('schema.short_root','JET_ROOT_LENGTH',lambda r:set_value(r,('corrections','root_jets','plus'),[]),True,None),
      ('schema.short_root_pair','JET_ROOT_PAIR',lambda r:set_value(r,('corrections','root_jets','plus',0),['3']),True,None),
      ('schema.invalid_core_decimal','ENCLOSURE_VALUE',lambda r:set_value(r,('enclosures','C','lower'),'nan'),True,None),
      ('schema.reversed_jet_interval','JET_ENCLOSURE_VALUE',lambda r:set_value(r,('corrections','enclosures','C','lower'),f['corrections']['enclosures']['C']['upper']),True,None),
      ('schema.invalid_rectangle','JET_RECTANGLE_VALUE',lambda r:set_value(r,('corrections','rectangle','N_norm1_upper'),'3/0'),True,None),
      ('schema.duplicate_key','FIXTURE_JSON',lambda r:(r/'fixtures.json').write_text('{"schema_version":1,"schema_version":1}'),True,None),
      ('schema.malformed_json','FIXTURE_JSON',lambda r:(r/'fixtures.json').write_text('{invalid'),True,None),
      ('schema.nonfinite_json','FIXTURE_JSON',lambda r:(r/'fixtures.json').write_text('{"schema_version":NaN}'),True,None),
      ('schema.oversized_integer','FIXTURE_JSON',lambda r:(r/'fixtures.json').write_text('{"schema_version":'+('1'*101)+'}'),True,None),
      ('file.changed_unsealed','INTEGRITY_HASH',lambda r:(r/'README.md').write_text('changed'),False,None),
      ('file.missing_fixture','INTEGRITY_MISSING',lambda r:(r/'fixtures.json').unlink(),False,None),
      ('file.missing_manifest','INTEGRITY_MISSING',lambda r:(r/'MANIFEST.json').unlink(),False,None),
      ('file.unlisted','INTEGRITY_UNLISTED',lambda r:(r/'extra.txt').write_text('unlisted'),False,None),
      ('file.unlisted_directory','INTEGRITY_UNLISTED_DIRECTORY',lambda r:(r/'extra').mkdir(),False,None),
      ('file.symlink','INTEGRITY_SYMLINK',lambda r:(r/'link').symlink_to('README.md'),False,None),
      ('file.fifo','INTEGRITY_SPECIAL_FILE',lambda r:os.mkfifo(r/'extra.fifo'),False,None),
      ('file.oversized','INTEGRITY_SIZE',lambda r:(r/'fixtures.json').write_text(' '*262145),False,None),
      ('file.duplicate_manifest','INTEGRITY_MANIFEST',lambda r:(r/'MANIFEST.json').write_text('{"format":1,"format":1,"files":{}}'),False,None),
    ]
    def manifest_edit(root,key,value):
        p=root/'MANIFEST.json';m=exact_json(p,'HARNESS_MANIFEST');m[key]=value;p.write_text(json.dumps(m))
    cases += [
      ('file.manifest_boolean','INTEGRITY_MANIFEST',lambda r:manifest_edit(r,'format',True),False,None),
      ('file.manifest_wrong_inventory','INTEGRITY_MANIFEST_FILES',lambda r:manifest_edit(r,'files',{'../escape':'0'*64}),False,None),
    ]
    def replace(root,file,old,new):
        p=root/file;s=p.read_text();need(s.count(old)==1,'HARNESS_SOURCE_MATCH',old);p.write_text(s.replace(old,new))
    math_cases=[
      ('scalar_c','exact_math.py','c=K/(1-x);d=x-f;','c=K/(1-x)+1;d=x-f;','SOURCE_SCALAR_C'),
      ('scalar_d','exact_math.py','c=K/(1-x);d=x-f;','c=K/(1-x);d=x-2*f;','SOURCE_SCALAR_D'),
      ('scalar_e','exact_math.py','d=x-f;e=1+z*x*x/(1-x)','d=x-f;e=1+2*z*x*x/(1-x)','SOURCE_SCALAR_E'),
      ('critical_slope','exact_math.py','(2-6*rho*3)*F(12,2)','(2-6*rho*3)*F(13,2)','CRITICAL_SQRT_SLOPE'),
      ('inverse_eta3','exact_math.py','-l1*l1*lam**(-2)','-2*l1*l1*lam**(-2)','INVERSE_ETA3'),
      ('source_rule','exact_math.py','range(p+1-newp)','range(p+2-newp)','EXTERNAL_PREFIX'),
      ('formal_root','exact_math.py','binomial(F(3*n,2),n-1)/n','binomial(F(4*n,2),n-1)/n','FORMAL_KERNEL_ROOT'),
      ('tail_contraction','exact_math.py',"rho/(1-rho*M)**2<q,'TAIL_CONTRACTION'","rho/(1-rho*M)**2<q/2,'TAIL_CONTRACTION'",'TAIL_CONTRACTION'),
      ('tail_product','exact_math.py',"3**145<Pbound,'TAIL_PRODUCT_POWER'","3**146<Pbound,'TAIL_PRODUCT_POWER'",'TAIL_PRODUCT_POWER'),
      ('tail_derivative','exact_math.py','v.widen(1000*E) for v in [dqp,drp]','v.widen(10000000000000*E) for v in [dqp,drp]','CRITICAL_INTERVAL_WIDTH'),
      ('Machin_angle','exact_math.py',"==1,'MACHIN_TANGENT_IDENTITY'","==2,'MACHIN_TANGENT_IDENTITY'",'MACHIN_TANGENT_IDENTITY'),
      ('gamma_bernoulli','exact_math.py','(-1)**(m+1)*(poly(m+1,-alpha)','(-1)**m*(poly(m+1,-alpha)','GAMMA_BERNOULLI_AGREEMENT'),
      ('root_plus_jet','jet_certificate.py','Q3(3),Q3(0,-2)','Q3(3),Q3(0,-3)','ROOT_PLUS_RESIDUAL'),
      ('jet_contraction','jet_certificate.py',"R/(1-R*M)**2<q,'JET_CONTRACTION'","R/(1-R*M)**2<q/2,'JET_CONTRACTION'",'JET_CONTRACTION'),
      ('jet_tail_factor','jet_certificate.py','==12<16,','==12<11,','JET_QUOTIENT_TAIL_FACTOR'),
      ('jet_denominator','jet_certificate.py','den.re.hi<-SCALE','den.re.hi<-2*SCALE','JET_RECTANGLE_DENOMINATOR'),
      ('jet_numerator','jet_certificate.py',"num.norm1()<2,'JET_RECTANGLE_NUMERATOR'","num.norm1()<1,'JET_RECTANGLE_NUMERATOR'",'JET_RECTANGLE_NUMERATOR'),
      ('zero_series_guard','exact_math.py','    size=2*N+3;one=unit(size)','    inv([0,1])\n    size=2*N+3;one=unit(size)','SERIES_ZERO_DIVISOR'),
      ('zero_interval_guard','exact_math.py','    E=analytic_bound_arithmetic()','    I(-1,1).reciprocal()\n    E=analytic_bound_arithmetic()','INTERVAL_ZERO_DIVISOR'),
      ('negative_sqrt_guard','exact_math.py','    E=analytic_bound_arithmetic()','    I(-1).sqrt()\n    E=analytic_bound_arithmetic()','INTERVAL_NEGATIVE_SQRT'),
      ('complex_zero_guard','jet_certificate.py','    E,h=bounds();rho=F(4,27)','    Box(0).reciprocal()\n    E,h=bounds();rho=F(4,27)','COMPLEX_BOX_ZERO_DIVISOR'),
      ('quadratic_zero_guard','jet_certificate.py','    n=7;one=unit(n,Q3(1))','    Q3(1)/Q3(0)\n    n=7;one=unit(n,Q3(1))','ROOT_FIELD_ZERO_DIVISOR'),
    ]
    for label,file,a,b,diag in math_cases:
        cases.append(('math.'+label,diag,lambda r,fi=file,x=a,y=b:replace(r,fi,x,y),True,None))
    return cases

def negative_one(base,temp,index,case,deadline):
    name,diag,mutate,reseal,path=case;root=temp/('case-'+str(index));shutil.copytree(base,root);mutate(root)
    if reseal:seal(root)
    for optimized in [False,True]:
        rc,obj=invoke(root,optimized,deadline)
        need(rc==1 and obj.get('status')=='FAIL' and obj.get('diagnostic')==diag,'MUTATION_DIAGNOSTIC',
             f'{name}, optimized={optimized}, expected={diag}, rc={rc}, got={obj}')
    shutil.rmtree(root)
    return {'name':name,'diagnostic':diag,'manifest_resealed':reseal,'normal_and_optimized':'PASS'}

def run():
    deadline=time.monotonic()+TOTAL_SECONDS;before=inventory(ROOT)
    rc,baseline=invoke(ROOT,False,deadline);need(rc==0 and baseline.get('status')=='PASS','BASELINE_NORMAL',baseline)
    rc,optimized=invoke(ROOT,True,deadline);need(rc==0 and optimized==baseline,'BASELINE_OPTIMIZED',optimized)
    f=exact_json(ROOT/'fixtures.json','HARNESS_FIXTURE');semantic=semantic_cases(f);extra=extra_cases(f)
    need({path for *_,path in semantic}=={path for path,_ in leaves(f)},'HARNESS_COVERAGE')
    reports=[]
    with tempfile.TemporaryDirectory(prefix='report119-exact-replay-') as name:
        temp=Path(name);fresh=temp/'fresh';shutil.copytree(ROOT,fresh);fresh_before=inventory(fresh)
        for mode in [False,True]:
            rc,obj=invoke(fresh,mode,deadline);need(rc==0 and obj==baseline,'FRESH_REPLAY',obj)
        need(inventory(fresh)==fresh_before,'FRESH_MUTATED')
        cases=semantic+extra
        with ThreadPoolExecutor(max_workers=WORKERS) as pool:
            futures={pool.submit(negative_one,ROOT,temp,j,c,deadline):j for j,c in enumerate(cases)}
            for future in as_completed(futures):reports.append((futures[future],future.result()))
    need(before==inventory(ROOT),'SOURCE_MUTATED')
    return {'status':'PASS','kind':'BOUNDED_READER_REPLAY','normal_equals_optimized':True,
            'fresh_normal_and_optimized':True,'source_unchanged':True,'baseline':baseline,
            'fixture_leaf_values_mutated':len(semantic),'all_fixture_leaves_covered':True,
            'named_mutations':[r for _,r in sorted(reports)],'mutation_runs':2*len(reports),
            'source_hashes_before':before,'source_hashes_after':inventory(ROOT),
            'bounds':{'subprocess_seconds':PROCESS_SECONDS,'total_seconds':TOTAL_SECONDS,'max_parallel_subprocesses':WORKERS,'input_file_bytes':262144},
            'scope':'Exact finite arithmetic, strict schema/inventory validation, negative tests. Analytic hypotheses are proved in report119.'}

def main():
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--output',type=Path);args=parser.parse_args()
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
