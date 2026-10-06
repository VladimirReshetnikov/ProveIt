#!/usr/bin/env python3
"""Bounded exact normal/-O replay and exhaustive fixture-leaf negative testing."""
import argparse
from concurrent.futures import ThreadPoolExecutor, as_completed
from fractions import Fraction as F
from hashlib import sha256
import json
import os
from pathlib import Path
import shutil
import stat
import subprocess
import sys
import tempfile
import time
sys.dont_write_bytecode=True
from support import CheckFailure, exact_json, inventory, need
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
    need(type(obj) is dict,'HARNESS_JSON_OBJECT')
    return r.returncode,obj

def snapshot(root):
    """Hash ordinary contents without opening deliberate symlinks or special files."""
    out={}
    for path in sorted(root.rglob('*')):
        name=path.relative_to(root).as_posix();mode=path.lstat().st_mode
        if stat.S_ISLNK(mode):out[name]=['symlink',os.readlink(path)]
        elif stat.S_ISREG(mode):out[name]=['file',sha256(path.read_bytes()).hexdigest()]
        elif stat.S_ISDIR(mode):out[name]=['directory']
        else:out[name]=['special',stat.S_IFMT(mode)]
    return out

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

def shifted_decimal(value,direction):
    """Move an endpoint outwards by one exact decimal unit, without floats."""
    places=len(value.split('.')[1]);scale=10**places
    numerator=F(value)*scale+direction
    need(numerator.denominator==1,'HARNESS_DECIMAL_SHIFT',value)
    whole=abs(numerator.numerator)
    return ('-' if numerator<0 else '')+str(whole//scale)+'.'+str(whole%scale).zfill(places)

def replace_source(root,file,old,new):
    path=root/file;source=path.read_text()
    need(source.count(old)==1,'HARNESS_SOURCE_MATCH',file+': '+old)
    path.write_text(source.replace(old,new))

def semantic_cases(f):
    """Every supplied scalar is changed independently, with its named rejection."""
    cases=[]
    for path,value in leaves(f):
        changed=value+1 if type(value) is int else value+' changed';group=path[0]
        if group=='schema_version':diag='FIXTURE_VERSION'
        elif group in ('provenance','ranges'):
            diag={'provenance':'PROVENANCE','ranges':'RANGE'}[group]+'_'+path[1].upper()
        elif group=='external_prefix':diag='EXTERNAL_PREFIX'
        elif group=='small_z':diag='MATRIX_POLYNOMIAL'
        elif group=='stirling':
            changed=str(F(value)+1)
            diag={'contributions':'STIRLING_CONTRIBUTIONS','ratio_inverse_N':'STIRLING_RATIO',
                  'even_logarithm':'STIRLING_EVEN'}[path[1]]
        elif group=='enclosures':
            changed=shifted_decimal(value,-1 if path[-1]==0 else 1)
            diag='ENCLOSURE_'+path[1].upper()
        elif group=='limitations':diag='LIMITATIONS'
        else:raise CheckFailure('HARNESS_COVERAGE',path)
        need(changed!=value,'HARNESS_UNCHANGED_LEAF',path)
        cases.append(('semantic.'+'.'.join(map(str,path)),diag,
                      lambda r,p=path,v=changed:set_value(r,p,v),True,path))
    return cases

def schema_cases(f):
    cases=[]
    def edit_object(root,path,missing):
        obj=exact_json(root/'fixtures.json','HARNESS_FIXTURE');target=obj
        for key in path:target=target[key]
        if missing:target.pop(next(iter(target)))
        else:target['unexpected']=0
        (root/'fixtures.json').write_text(json.dumps(obj)+'\n')
    objects=[((),'FIXTURE_SCHEMA'),(('provenance',),'PROVENANCE_SCHEMA'),
             (('ranges',),'RANGE_SCHEMA'),(('small_z',),'SMALL_Z_SCHEMA'),
             (('stirling',),'STIRLING_SCHEMA'),(('enclosures',),'ENCLOSURE_SCHEMA')]
    for path,diag in objects:
        for missing in (False,True):
            cases.append(('schema.'+('.'.join(path) or 'root')+('.missing' if missing else '.extra'),
                          diag,lambda r,p=path,m=missing:edit_object(r,p,m),True,None))
    arrays=[(('external_prefix',),'PREFIX_LENGTH'),
            (('stirling','contributions'),'STIRLING_LENGTH'),(('limitations',),'LIMITATIONS')]
    arrays += [(('small_z',key),'SMALL_Z_LENGTH') for key in f['small_z']]
    arrays += [(('enclosures',key),'ENCLOSURE_LENGTH') for key in f['enclosures']]
    for path,diag in arrays:
        value=f
        for key in path:value=value[key]
        for label,changed in [('short',value[:-1]),('long',value+[value[-1]]),('nonarray',{})]:
            cases.append(('schema.'+'.'.join(path)+'.'+label,diag,
                          lambda r,p=path,v=changed:set_value(r,p,v),True,None))
    cases += [
      ('schema.boolean_version','FIXTURE_VERSION',lambda r:set_value(r,('schema_version',),True),True,None),
      ('schema.boolean_range','RANGE_MATRIX_N_MAX',lambda r:set_value(r,('ranges','matrix_n_max'),True),True,None),
      ('schema.boolean_provenance','PROVENANCE_OFFSET',lambda r:set_value(r,('provenance','offset'),True),True,None),
      ('schema.boolean_prefix','PREFIX_INTEGER',lambda r:set_value(r,('external_prefix',0),True),True,None),
      ('schema.boolean_polynomial','SMALL_Z_INTEGER',lambda r:set_value(r,('small_z','1',0),False),True,None),
      ('schema.negative_prefix','PREFIX_INTEGER',lambda r:set_value(r,('external_prefix',0),-1),True,None),
      ('schema.oversized_prefix','PREFIX_INTEGER',lambda r:set_value(r,('external_prefix',0),10**26),True,None),
      ('schema.negative_polynomial','SMALL_Z_INTEGER',lambda r:set_value(r,('small_z','1',0),-1),True,None),
      ('schema.oversized_polynomial','SMALL_Z_INTEGER',lambda r:set_value(r,('small_z','1',0),10**5),True,None),
      ('schema.float','FIXTURE_JSON',lambda r:set_value(r,('ranges','matrix_n_max'),5.0),True,None),
      ('schema.noncanonical_rational','STIRLING_VALUE',lambda r:set_value(r,('stirling','contributions',0),'26/72'),True,None),
      ('schema.zero_denominator','STIRLING_VALUE',lambda r:set_value(r,('stirling','contributions',0),'13/0'),True,None),
      ('schema.boolean_rational','STIRLING_VALUE',lambda r:set_value(r,('stirling','ratio_inverse_N'),True),True,None),
      ('schema.nondecimal_enclosure','ENCLOSURE_VALUE',lambda r:set_value(r,('enclosures','p',0),'nan'),True,None),
      ('schema.numeric_enclosure','ENCLOSURE_VALUE',lambda r:set_value(r,('enclosures','p',0),0),True,None),
      ('schema.reversed_enclosure','ENCLOSURE_Q',lambda r:set_value(r,('enclosures','q'),list(reversed(f['enclosures']['q']))),True,None),
      ('schema.duplicate_key','FIXTURE_JSON',lambda r:(r/'fixtures.json').write_text('{"schema_version":1,"schema_version":1}'),True,None),
      ('schema.malformed_json','FIXTURE_JSON',lambda r:(r/'fixtures.json').write_text('{invalid'),True,None),
      ('schema.nonfinite_json','FIXTURE_JSON',lambda r:(r/'fixtures.json').write_text('{"schema_version":NaN}'),True,None),
      ('schema.oversized_integer','FIXTURE_JSON',lambda r:(r/'fixtures.json').write_text('{"schema_version":'+('1'*101)+'}'),True,None),
      ('schema.invalid_utf8','FIXTURE_JSON',lambda r:(r/'fixtures.json').write_bytes(b'\xff'),True,None),
      ('schema.root_nonobject','FIXTURE_SCHEMA',lambda r:(r/'fixtures.json').write_text('[]'),True,None),
    ]
    return cases

def math_cases():
    interval='INTERVAL_CERTIFICATE'
    changes=[
      ('short_log','interval_math.py','LOG_TERMS = 128','LOG_TERMS = 2',
       (interval,'INTERVAL: F(p_lower)-p_lower is not strictly positive')),
      ('short_exp','interval_math.py','EXP_TERMS = 80','EXP_TERMS = 1',
       (interval,'INTERVAL: F(p_lower)-p_lower is not strictly positive')),
      ('zero_log','interval_math.py','return Interval(_log_point(value.low).low, _log_point(value.high).high)',
       'return Interval.point(0)',(interval,'INTERVAL: division interval contains zero')),
      ('unit_exp','interval_math.py','return Interval(_exp_point(value.low).low, _exp_point(value.high).high)',
       'return Interval.point(1)',(interval,'INTERVAL: F(p_upper)-p_upper is not strictly negative')),
      ('wide_inverse','interval_math.py','width = (q - p) / g','width = (q - p) / g + 1',
       (interval,'INTERVAL: the continuous inverse limiting width is not in (0,1)')),
      ('endpoint_identity','interval_math.py','e2g = Fraction(27, 16)','e2g = Fraction(28, 16)',
       (interval,'INTERVAL: the exact u(b-g) logarithm argument identity failed')),
      ('log_domain_guard','interval_math.py','    log2 = log_interval(2)',
       '    log_interval(0)\n    log2 = log_interval(2)',
       (interval,'INTERVAL: logarithm interval is not strictly positive')),
      ('reciprocal_zero_guard','interval_math.py','    log2 = log_interval(2)',
       '    Interval.point(0).reciprocal()\n    log2 = log_interval(2)',
       (interval,'INTERVAL: division interval contains zero')),
      ('reversed_interval_guard','interval_math.py','    log2 = log_interval(2)',
       '    Interval(1,0)\n    log2 = log_interval(2)',
       (interval,'INTERVAL: interval endpoints are reversed')),
      ('binary_float_guard','interval_math.py','    log2 = log_interval(2)',
       '    Interval.point(0.5)\n    log2 = log_interval(2)',
       (interval,'INTERVAL: boolean and binary-floating-point inputs are forbidden')),
      ('original_weight','exact_math.py','(2 if k==0 else 3)','(3 if k==0 else 3)','EXTERNAL_PREFIX'),
      ('pfaffian_initial_value','exact_math.py','n=len(a);v=F(1)','n=len(a);v=F(2)','PFAFFIAN_RECURSIVE_AGREEMENT'),
      ('bareiss_previous_pivot','exact_math.py','sign=1;previous=F(1)','sign=1;previous=F(2)','PFAFFIAN_SQUARE'),
      ('orientation_boundary','exact_math.py','fixed=[int(j==n-1) for i,j in vertices]',
       'fixed=[2*int(j==n-1) for i,j in vertices]','ORIENTATION_HOMOGENEITY'),
      ('kernel_t_weight','exact_math.py','(t if r==s==0 else 0)','(2*t if r==s==0 else 0)','KERNEL_ORIGINAL_ENTRY'),
      ('rational_kernel_boundary','exact_math.py','K0=-u*(t+(1+u)/(1-u))',
       'K0=-2*u*(t+(1+u)/(1-u))','RATIONAL_KERNEL_DECOMPOSITION'),
      ('Mobius_numerator','exact_math.py','G=((t-4)*u*u+(4-t)*u+t-1)',
       'G=((t-4)*u*u+(5-t)*u+t-1)','RATIONAL_MOBIUS_TRANSFORM'),
      ('Jensen_convexity','exact_math.py','equals(2*u/(1+2*u)**2)',
       'equals(3*u/(1+2*u)**2)','JENSEN_CONVEXITY_IDENTITY'),
      ('upper_map_derivative','exact_math.py','equals(-1/(3*u-1))',
       'equals(-2/(3*u-1))','UPPER_MAP_DERIVATIVE_IDENTITY'),
      ('chord_parity','exact_math.py','need(((v/(2*u))*u).equals(v/2)',
       'need(((v/(2*u))*u).equals(v/3)','CHORD_PARITY_CANCELLATION'),
      ('Jensen_parameter_range','exact_math.py','(4-(4+u)/(1+u)).equals(3*u/(1+u))',
       '(4-(4+u)/(1+u)).equals(4*u/(1+u))','JENSEN_PARAMETER_RANGE'),
      ('Stirling_shift','exact_math.py','specs=[(3,-1,1),(1,0,1),(2,0,-1),(2,-1,-1)]',
       'specs=[(3,0,1),(1,0,1),(2,0,-1),(2,-1,-1)]','STIRLING_CONTRIBUTIONS'),
      ('inverse_kappa','exact_math.py','kappa=F(5,72)','kappa=F(6,72)','STIRLING_INVERSE_KAPPA'),
      ('inverse_linear_shift','exact_math.py','displacement=-cc/gg;log_shift=',
       'displacement=-2*cc/gg;log_shift=','INVERSE_LINEAR_CANCELLATION'),
      ('inverse_log_shift','exact_math.py','log_shift=kappa*LL/gg',
       'log_shift=2*kappa*LL/gg','INVERSE_LOG_CANCELLATION'),
      ('inverse_constant_residual','exact_math.py','equals(-cc**2/(2*gg))',
       'equals(-cc**2/gg)','INVERSE_CONSTANT_RESIDUAL'),
      ('inverse_ceiling_width','exact_math.py','ceil_right=-((-right.numerator)//right.denominator)',
       'ceil_right=1-((-right.numerator)//right.denominator)','INVERSE_CEILING_WIDTH'),
      ('threshold_equality','exact_math.py','F(4).denominator+1==5',
       'F(4).denominator+0==5','INVERSE_THRESHOLD_EQUALITY'),
      ('map_endpoint_bound','exact_math.py',"need(F(65,32)<F(27,16)**2,'MAP_ENDPOINT_RATIONAL_BOUND')",
       "need(F(65,16)<F(27,16)**2,'MAP_ENDPOINT_RATIONAL_BOUND')",'MAP_ENDPOINT_RATIONAL_BOUND'),
      ('banded_denominator','exact_math.py','R=[2,-3,-1,3,-1];Nt=[t-1,4-t,t-4]',
       'R=[3,-3,-1,3,-1];Nt=[t-1,4-t,t-4]','BANDED_DETERMINANT_POLYNOMIAL'),
      ('shifted_product_index','exact_math.py','F(n+i+j,2*i+j-1)',
       'F(n+i+j+1,2*i+j-1)','SHIFTED_ANDREWS_INDEXING'),
      ('even_calibration_factor','exact_math.py','val*=2*ordinary_asm(2*m)/ordinary_asm(2*m-1)',
       'val*=3*ordinary_asm(2*m)/ordinary_asm(2*m-1)','EVEN_CALIBRATION_PRODUCT'),
      ('polynomial_zero_guard','exact_math.py','    result=rational_identities();maximum=',
       '    quotient([1],[0])\n    result=rational_identities();maximum=','POLYNOMIAL_ZERO_DIVISOR'),
      ('series_zero_guard','exact_math.py','    result=rational_identities();maximum=',
       '    series([1],[0],1)\n    result=rational_identities();maximum=','SERIES_ZERO_DIVISOR'),
      ('rational_zero_guard','exact_math.py','    result=rational_identities();maximum=',
       '    Rat(1)/Rat(0)\n    result=rational_identities();maximum=','RATIONAL_ZERO_DIVISOR'),
      ('pfaffian_shape_guard','exact_math.py','    terms=[]\n',
       '    pfaffian([[0]])\n    terms=[]\n','PFAFFIAN_SHAPE'),
      ('pfaffian_skew_guard','exact_math.py','    terms=[]\n',
       '    pfaffian([[0,1],[1,0]])\n    terms=[]\n','PFAFFIAN_SKEW'),
    ]
    return [('math.'+label,diag,lambda r,fi=file,x=old,y=new:replace_source(r,fi,x,y),True,None)
            for label,file,old,new,diag in changes]

def extra_cases(f):
    return schema_cases(f)+file_cases()+math_cases()

def file_cases():
    cases = [
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
      ('file.manifest_extra_key','INTEGRITY_MANIFEST',lambda r:manifest_edit(r,'unexpected',0),False,None),
      ('file.manifest_wrong_inventory','INTEGRITY_MANIFEST_FILES',lambda r:manifest_edit(r,'files',{'../escape':'0'*64}),False,None),
    ]
    return cases

def negative_one(base,temp,index,case,deadline):
    name,expect,mutate,reseal,path=case;root=temp/('case-'+str(index));shutil.copytree(base,root);mutate(root)
    diag,detail=expect if type(expect) is tuple else (expect,None)
    if reseal:seal(root)
    mutated_before=snapshot(root)
    for optimized in [False,True]:
        rc,obj=invoke(root,optimized,deadline)
        need(rc==1 and obj.get('status')=='FAIL' and obj.get('diagnostic')==diag,'MUTATION_DIAGNOSTIC',
             f'{name}, optimized={optimized}, expected={diag}, rc={rc}, got={obj}')
        if detail is not None:
            need(obj.get('detail')==detail,'MUTATION_DETAIL',
                 f'{name}, optimized={optimized}, expected={detail}, got={obj}')
    need(snapshot(root)==mutated_before,'MUTATION_COPY_CHANGED',name)
    shutil.rmtree(root)
    return {'name':name,'diagnostic':diag,'manifest_resealed':reseal,'normal_and_optimized':'PASS','copy_unchanged':True}

def run():
    deadline=time.monotonic()+TOTAL_SECONDS;before=inventory(ROOT)
    rc,baseline=invoke(ROOT,False,deadline);need(rc==0 and baseline.get('status')=='PASS','BASELINE_NORMAL',baseline)
    rc,optimized=invoke(ROOT,True,deadline);need(rc==0 and optimized==baseline,'BASELINE_OPTIMIZED',optimized)
    f=exact_json(ROOT/'fixtures.json','HARNESS_FIXTURE');semantic=semantic_cases(f);extra=extra_cases(f)
    need({path for *_,path in semantic}=={path for path,_ in leaves(f)},'HARNESS_COVERAGE')
    reports=[]
    with tempfile.TemporaryDirectory(prefix='report120-exact-replay-') as name:
        temp=Path(name);fresh=temp/'fresh';shutil.copytree(ROOT,fresh);fresh_before=inventory(fresh)
        for mode in [False,True]:
            rc,obj=invoke(fresh,mode,deadline);need(rc==0 and obj==baseline,'FRESH_REPLAY',obj)
        need(inventory(fresh)==fresh_before,'FRESH_MUTATED')
        cases=semantic+extra
        need(len({case[0] for case in cases})==len(cases),'HARNESS_DUPLICATE_CASE')
        pool=ThreadPoolExecutor(max_workers=WORKERS)
        try:
            futures={pool.submit(negative_one,ROOT,temp,j,c,deadline):j for j,c in enumerate(cases)}
            for future in as_completed(futures):reports.append((futures[future],future.result()))
        finally:
            pool.shutdown(wait=True,cancel_futures=True)
    need(time.monotonic()<=deadline,'HARNESS_DEADLINE')
    need(before==inventory(ROOT),'SOURCE_MUTATED')
    return {'status':'PASS','kind':'BOUNDED_READER_REPLAY','normal_equals_optimized':True,
            'fresh_normal_and_optimized':True,'source_unchanged':True,'baseline':baseline,
            'fixture_leaf_values_mutated':len(semantic),'all_fixture_leaves_covered':True,
            'fixture_leaf_paths':['.'.join(map(str,path)) for path,_ in leaves(f)],
            'all_mutation_copies_unchanged':True,
            'named_mutations':[r for _,r in sorted(reports)],'mutation_runs':2*len(reports),
            'source_hashes_before':before,'source_hashes_after':inventory(ROOT),
            'bounds':{'subprocess_seconds':PROCESS_SECONDS,'total_seconds':TOTAL_SECONDS,'max_parallel_subprocesses':WORKERS,'input_file_bytes':262144},
            'scope':'Exact finite arithmetic, strict schema/inventory validation, and named negative tests for the report120 finite certificates.'}

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
