#!/usr/bin/env python3
import sys
if not sys.flags.isolated:
    sys.stderr.write('REJECTED: isolated Python (-I) is required before any imports\n')
    raise SystemExit(2)
sys.dont_write_bytecode = True

"""Report138 integrity, exact replay, adversarial tests, and external reproduction.

Run only after reviewing this executable source and establishing provenance. Hashes
are integrity checks, not a signature or a sandbox against malicious replacement.
"""
import argparse
from fractions import Fraction
import hashlib
import json
import math
import os
from pathlib import Path
import re
import stat
import subprocess
import types
import zipfile

ROOT = Path(__file__).absolute().parent
SOURCES = frozenset({'A224248.seq','A047889.seq','oF12345a','b047889_0_24.txt','independent_audit.json'})
PAYLOAD = frozenset({'README.md','SOURCES.md','Report138.tex','Report138.pdf','verify.py',
                     'checks/fixtures.json','code/exact.py','code/object_check.cpp','sources/inventory.json'}) | frozenset('sources/'+n for n in SOURCES)
DIRECTORIES = frozenset({'checks','code','sources'})
MANIFEST = 'manifest.json'
SCHEMA = 'report138-sha256-v1'

class Rejected(Exception):
    pass

def require(condition,message):
    if not condition:
        raise Rejected(message)

def no_duplicate_keys(pairs):
    result={}
    for key,value in pairs:
        require(key not in result,'duplicate JSON key: '+key)
        result[key]=value
    return result

def reject_constant(value):
    raise Rejected('nonfinite JSON token refused: '+value)

def parse_json(data):
    return json.loads(data.decode('utf-8'),object_pairs_hook=no_duplicate_keys,parse_constant=reject_constant)

def json_bytes(value):
    return (json.dumps(value,sort_keys=True,indent=2,ensure_ascii=True,allow_nan=False)+'\n').encode('ascii')

def lexical_absolute(value):
    path=Path(value)
    require('..' not in path.parts,'parent traversal is not permitted')
    return path if path.is_absolute() else Path.cwd()/path

def check_ancestors(path,leaf_may_be_absent=False):
    require('..' not in path.parts,'parent traversal is not permitted in any path')
    current=Path(path.anchor)
    for index,part in enumerate(path.parts[1:]):
        current/=part
        leaf=index==len(path.parts)-2
        try:
            mode=current.lstat().st_mode
        except FileNotFoundError:
            require(leaf and leaf_may_be_absent,'missing ancestor: '+str(current))
            return
        require(not stat.S_ISLNK(mode),'symlink component refused: '+str(current))
        if not leaf:
            require(stat.S_ISDIR(mode),'non-directory ancestor: '+str(current))

def read_regular(path):
    flags=os.O_RDONLY|getattr(os,'O_NOFOLLOW',0)|getattr(os,'O_NONBLOCK',0)
    fd=os.open(path,flags)
    with os.fdopen(fd,'rb') as stream:
        require(stat.S_ISREG(os.fstat(stream.fileno()).st_mode),'nonregular file refused')
        return stream.read()

def preflight_output(value):
    check_ancestors(ROOT)
    canonical_root=ROOT.resolve(strict=True)
    path=lexical_absolute(value)
    check_ancestors(path,leaf_may_be_absent=True)
    require(not path.exists() and not path.is_symlink(),'output already exists: '+str(path))
    path=path.resolve(strict=False)
    require(canonical_root!=path and canonical_root not in path.parents,'output must be outside the bundle')
    require(path.parent.is_dir(),'output parent must already exist')
    return path

def create_output_directory(path):
    check_ancestors(path,leaf_may_be_absent=True)
    os.mkdir(path,mode=0o700)

def create_output_file(path):
    check_ancestors(path,leaf_may_be_absent=True)
    flags=os.O_WRONLY|os.O_CREAT|os.O_EXCL|getattr(os,'O_NOFOLLOW',0)
    return os.fdopen(os.open(path,flags,0o600),'wb')

def inventory(root=ROOT,sealing=False):
    check_ancestors(root)
    require(root.is_dir(),'bundle root is not a directory')
    found={};seen_directories=set()
    for directory,subdirs,files in os.walk(root,followlinks=False):
        for name in subdirs:
            p=Path(directory)/name;rel=p.relative_to(root).as_posix()
            require(rel in DIRECTORIES and stat.S_ISDIR(p.lstat().st_mode),'unexpected directory or symlink: '+rel)
            seen_directories.add(rel)
        for name in files:
            p=Path(directory)/name
            require(stat.S_ISREG(p.lstat().st_mode),'nonregular file: '+str(p))
            found[p.relative_to(root).as_posix()]=read_regular(p)
    require(seen_directories==DIRECTORIES,'directory inventory mismatch')
    expected=PAYLOAD|{MANIFEST}
    if sealing and MANIFEST not in found:expected=PAYLOAD
    require(set(found)==expected,'closed inventory mismatch; missing='+str(sorted(expected-set(found)))+'; extra='+str(sorted(set(found)-expected)))
    return found

def keys(value,expected,label):
    require(type(value) is dict and set(value)==set(expected),label+' keys/type')

def integer(value,label,expected=None):
    require(type(value) is int,label+' must be an integer, not bool, float or string')
    if expected is not None:require(value==expected,label+' value')

def text(value,label):
    require(type(value) is str and bool(value),label+' must be a nonempty string')

def rational(value,label):
    require(type(value) is str,label+' must be a canonical rational string')
    require(str(Fraction(value))==value,label+' noncanonical rational')

def integer_list(value,length,label):
    require(type(value) is list and len(value)==length,label+' list length/type')
    for x in value:integer(x,label)

def validate_fixtures(data):
    # The exact field schema is deliberately encoded in executable code, not read
    # from a purported schema in the fixture. See fixtures_contract below.
    f=parse_json(data['checks/fixtures.json'])
    fixtures_contract(f)
    return f

def status(value,label):
    require(value=='PASS',label+' status')

def natural(value,label):
    integer(value,label);require(value>=0,label+' must be nonnegative')

def truth(value,label):
    require(type(value) is bool and value,label+' must be true')

def fixtures_contract(f):
    keys(f,{'schema','determinant_crosscheck','gl2_crosscheck','avoidance','boundary_enumeration','saturation','direct_unique','gluing','leading','normalization','status'},'fixtures')
    require(f['schema']=='report138-exact-replay-v1','fixture schema');status(f['status'],'fixtures')
    d=f['determinant_crosscheck'];keys(d,{'outer_size_max','rows_max','tests','status'},'determinant crosscheck')
    integer(d['outer_size_max'],'skew outer size',10);integer(d['rows_max'],'skew rows',4);integer(d['tests'],'skew tests',5096);status(d['status'],'skew')
    d=f['gl2_crosscheck'];keys(d,{'nu_size_max','tests','status'},'GL2 crosscheck')
    integer(d['nu_size_max'],'GL2 size',12);natural(d['tests'],'GL2 tests');status(d['status'],'GL2')
    d=f['avoidance'];keys(d,{'n_max','rsk','recurrence','source_match','status'},'avoidance')
    integer(d['n_max'],'avoidance n',24)
    for name in ('rsk','recurrence'):integer_list(d[name],25,'avoidance '+name)
    truth(d['source_match'],'avoidance source match');status(d['status'],'avoidance')
    rows=f['boundary_enumeration'];require(type(rows) is list and len(rows)==7,'boundary row list')
    for row,m,count in zip(rows,range(2,9),(1,5,15,35,70,126,210)):
        keys(row,{'m','permutations','avoiders','parameter_tests','counts','status'},'boundary row')
        integer(row['m'],'boundary m',m);integer(row['parameter_tests'],'boundary tests',count)
        for k in ('permutations','avoiders'):natural(row[k],'boundary '+k)
        require(type(row['counts']) is list and len(row['counts'])==count,'boundary count rows');status(row['status'],'boundary')
        seen=set()
        for c in row['counts']:
            keys(c,{'P','R','Q','T','direct','six_term'},'boundary count')
            for k in c:natural(c[k],'boundary '+k)
            v=tuple(c[k] for k in ('P','R','Q','T'));require(v not in seen,'duplicate boundary tuple');seen.add(v)
        supported={(P,R,Q,T) for P in range(1,m) for Q in range(1,m-P+1) for R in range(1,P+1) for T in range(1,Q+1)}
        require(seen==supported,'boundary tuple coverage')
    rows=f['saturation'];require(type(rows) is list and len(rows)==3,'saturation row list')
    for row,m in zip(rows,range(6,9)):
        keys(row,{'m','tableau_boundary_records','outer_skew_groups','multiple_initial_filling_groups','complete_filling_groups','status'},'saturation row')
        integer(row['m'],'saturation m',m)
        for k in set(row)-{'m','status'}:natural(row[k],'saturation '+k)
        status(row['status'],'saturation')
    rows=f['direct_unique'];require(type(rows) is list and len(rows)==4,'direct unique rows')
    for row,n in zip(rows,range(5,9)):
        keys(row,{'n','permutations','unique','status'},'direct unique row');integer(row['n'],'direct n',n)
        for k in ('permutations','unique'):natural(row[k],'direct '+k)
        status(row['status'],'direct unique')
    rows=f['gluing'];require(type(rows) is list and len(rows)==20,'gluing rows')
    for row,n in zip(rows,range(5,25)):
        keys(row,{'n','unique','half_states','half_mass','zero_boundary','source_match','status'},'gluing row');integer(row['n'],'gluing n',n)
        for k in ('unique','half_states','half_mass','zero_boundary'):natural(row[k],'gluing '+k)
        truth(row['source_match'],'gluing source match');status(row['status'],'gluing')
    d=f['leading'];keys(d,{'values','h0','R5_lower_bound','status'},'leading')
    for k in ('h0','R5_lower_bound'):rational(d[k],'leading '+k)
    status(d['status'],'leading');require(type(d['values']) is list and len(d['values'])==70,'leading values')
    seen=set()
    for row in d['values']:
        keys(row,{'v','h'},'leading value');integer_list(row['v'],4,'leading boundary')
        v=tuple(row['v']);require(v not in seen,'duplicate leading boundary');seen.add(v)
        rational(row['h'],'leading h');require(Fraction(row['h'])>=0,'negative finite leading h')
    require(seen=={(a,b,c,d) for a in range(5) for b in range(5-a) for c in range(5-a-b) for d in range(5-a-b-c)},'leading boundary coverage')
    d=f['normalization'];keys(d,{'dual_cauchy_monomials','dual_cauchy_status','shift_identity_tests','regev_rational_factor','h0_signed_terms','zero_boundary_tests','status'},'normalization')
    for k in ('dual_cauchy_monomials','shift_identity_tests'):natural(d[k],'normalization '+k)
    integer(d['zero_boundary_tests'],'zero boundary tests',20)
    for k in ('status','dual_cauchy_status'):status(d[k],'normalization '+k)
    rational(d['regev_rational_factor'],'Regev factor')
    require(type(d['h0_signed_terms']) is list and len(d['h0_signed_terms'])==2,'signed h0 terms')
    for x in d['h0_signed_terms']:rational(x,'signed h0 term')


def validate_manifest(data):
    m=parse_json(data[MANIFEST]);keys(m,{'schema','files'},'manifest')
    require(m['schema']==SCHEMA,'manifest schema');keys(m['files'],PAYLOAD,'manifest records')
    for name in sorted(PAYLOAD):
        rec=m['files'][name];keys(rec,{'bytes','sha256'},'manifest file record')
        integer(rec['bytes'],'manifest size',len(data[name]))
        require(type(rec['sha256']) is str and rec['sha256']==hashlib.sha256(data[name]).hexdigest(),'SHA256 mismatch: '+name)

def source_values(data):
    inv=parse_json(data['sources/inventory.json'])
    keys(inv,{'schema','files'},'source inventory')
    require(inv['schema']=='report138-source-inventory-v1','source inventory schema')
    keys(inv['files'],SOURCES,'source inventory files')
    for name,record in inv['files'].items():
        keys(record,{'url','title','retrieved','note','bytes','sha256'},'source record')
        for label in ('url','title','retrieved','note'):text(record[label],'source '+label)
        raw=data['sources/'+name];integer(record['bytes'],'source bytes',len(raw))
        require(type(record['sha256']) is str and record['sha256']==hashlib.sha256(raw).hexdigest(),'source hash mismatch: '+name)
    def oeis(name,expected):
        lines=data['sources/'+name+'.seq'].decode('utf-8').splitlines();out=[]
        for line in lines:
            if line.startswith(('%S '+name+' ','%T '+name+' ','%U '+name+' ')):
                tail=line.split(' ',2)[2].rstrip(',')
                require(re.fullmatch(r'[0-9]+(?:,[0-9]+)*',tail) is not None,'OEIS numeric syntax')
                out.extend(map(int,tail.split(',')))
        require(len(out)==expected,'OEIS source term count');return out
    unique_oeis=oeis('A224248',24);avoid_oeis=oeis('A047889',22)
    raw=data['sources/oF12345a'].decode('ascii')
    matches=re.findall(r'\[([0-9,\s]+)\]',raw)
    require(len(matches)==1,'Rutgers source must have exactly one numeric list')
    require(re.fullmatch(r'\s*[0-9]+(?:\s*,\s*[0-9]+)*\s*',matches[0]) is not None,'Rutgers numeric syntax')
    unique=[0]+[int(x.strip()) for x in matches[0].split(',')]
    require(len(unique)==41 and unique[:24]==unique_oeis,'Rutgers/OEIS offset or values mismatch')
    avoid=[]
    for line in data['sources/b047889_0_24.txt'].decode('ascii').splitlines():
        require(re.fullmatch(r'[0-9]+ [0-9]+',line) is not None,'b-file numeric syntax')
        n,value=map(int,line.split());require(n==len(avoid),'b-file nonconsecutive index');avoid.append(value)
    require(len(avoid)==25 and avoid[:22]==avoid_oeis,'avoidance source overlap mismatch')
    return unique,avoid

def validate_audit(data,result=None):
    a=parse_json(data['sources/independent_audit.json'])
    keys(a,{'determinant_vs_independent_corner_recursion','boundary_histograms','schur_saturation','elapsed_seconds'},'independent audit')
    d=a['determinant_vs_independent_corner_recursion'];keys(d,{'tests','status'},'audit determinant')
    integer(d['tests'],'audit skew tests',5096);require(d['status']=='PASS','audit status')
    elapsed=a['elapsed_seconds']
    require(type(elapsed) in (int,float) and elapsed>=0
            and (type(elapsed) is int or math.isfinite(elapsed)),
            'audit elapsed provenance must be a finite nonnegative number')
    require(type(a['boundary_histograms']) is list and len(a['boundary_histograms'])==7,'audit boundary rows')
    for row,m,count in zip(a['boundary_histograms'],range(2,9),(1,5,15,35,70,126,210)):
        keys(row,{'m','permutations','avoiders','all_supported_boundary_tests','status'},'audit boundary row')
        for k in ('m','permutations','avoiders','all_supported_boundary_tests'):integer(row[k],'audit '+k)
        require(row['m']==m and row['all_supported_boundary_tests']==count and row['status']=='PASS','audit boundary values')
    require(type(a['schur_saturation']) is list and len(a['schur_saturation'])==3,'audit saturation rows')
    for row,m in zip(a['schur_saturation'],range(6,9)):
        keys(row,{'m','tested_tableau_pairs_and_boundaries','outer_skew_groups','groups_with_multiple_initial_fillings','status'},'audit saturation row')
        for k in set(row)-{'status'}:integer(row[k],'audit '+k)
        require(row['m']==m and row['status']=='PASS','audit saturation values')
    if result is not None:
        audit_comparison(a,result)
    return a

def audit_comparison(a,result):
    require(result['determinant_crosscheck']['tests']==a['determinant_vs_independent_corner_recursion']['tests'],'independent skew audit differs')
    for row,target in zip(result['boundary_enumeration'],a['boundary_histograms']):
        for field in ('m','permutations','avoiders'):require(row[field]==target[field],'independent boundary audit differs: '+field)
        require(row['parameter_tests']==target['all_supported_boundary_tests'],'independent boundary test counts differ')
    for row,target in zip(result['saturation'],a['schur_saturation']):
        for current,old in [('m','m'),('tableau_boundary_records','tested_tableau_pairs_and_boundaries'),('outer_skew_groups','outer_skew_groups'),('multiple_initial_filling_groups','groups_with_multiple_initial_fillings')]:
            require(row[current]==target[old],'independent saturation audit differs: '+current)


def validate_payload(data):
    validate_fixtures(data);source_values(data);validate_audit(data)
    require(data['Report138.pdf'].startswith(b'%PDF-'),'Report138 is not a PDF')
    require(b'\\begin{document}' in data['Report138.tex'] and b'\\end{document}' in data['Report138.tex'],'incomplete Report138 TeX')

def verify(root=ROOT):
    data=inventory(root);validate_manifest(data);validate_payload(data);return data

def make_manifest(data):
    return {'schema':SCHEMA,'files':{name:{'bytes':len(data[name]),'sha256':hashlib.sha256(data[name]).hexdigest()} for name in sorted(PAYLOAD)}}

def replay(data):
    module=types.ModuleType('report138_exact');module.__file__=str(ROOT/'code/exact.py')
    # Only executable code bytes passing manifest verification are compiled.
    # Fixtures and downloaded sources are never executed or imported.
    exec(compile(data['code/exact.py'],'code/exact.py','exec'),module.__dict__)
    unique,avoid=source_values(data)
    result=module.run(unique,avoid)
    fixtures_contract(result)
    validate_audit(data,result)
    require(result==validate_fixtures(data),'recomputed exact results differ from the sealed fixtures')
    return result

def pack(data,destination):
    with create_output_file(destination) as stream:
        with zipfile.ZipFile(stream,'w',compression=zipfile.ZIP_STORED) as archive:
            for name in sorted(data):
                info=zipfile.ZipInfo('Report138/'+name,date_time=(1980,1,1,0,0,0))
                info.create_system=3;info.external_attr=(stat.S_IFREG|0o644)<<16;info.compress_type=zipfile.ZIP_STORED;info.flag_bits=0
                archive.writestr(info,data[name])
    return hashlib.sha256(read_regular(destination)).hexdigest()

def invoke(root,args,optimized=False,isolated=True,success=True,timeout=1200):
    command=[sys.executable]+(['-I'] if isolated else [])+['-B']+(['-O'] if optimized else [])+[str(root/'verify.py')]+args
    run=subprocess.run(command,stdout=subprocess.PIPE,stderr=subprocess.PIPE,timeout=timeout)
    require((run.returncode==0)==success,'unexpected subprocess result: '+str(args)+' '+run.stderr.decode(errors='replace'))
    return run

def selftest(data,destination):
    create_output_directory(destination);passed=[]
    def copy(label):
        root=destination/label;root.mkdir()
        for directory in sorted(DIRECTORIES):(root/directory).mkdir()
        for name,content in data.items():(root/name).write_bytes(content)
        return root
    def rehash(root,filename,content):
        (root/filename).write_bytes(content);revised=dict(data);revised[filename]=content
        (root/MANIFEST).write_bytes(json_bytes(make_manifest(revised)))
    clean=copy('clean')
    invoke(clean,['check']);invoke(clean,['check'],optimized=True);passed.append('normal_and_optimized_integrity')
    changes=[('extra_file',lambda p:(p/'extra').write_text('x')),
             ('extra_directory',lambda p:(p/'extra').mkdir()),
             ('missing_pdf',lambda p:(p/'Report138.pdf').unlink()),
             ('changed_code',lambda p:(p/'code/exact.py').write_bytes(data['code/exact.py']+b'\n')),
             ('changed_source',lambda p:(p/'sources/oF12345a').write_text('changed')),
             ('symlink_file',lambda p:(p/'extra').symlink_to(p/'README.md')),
             ('broken_symlink',lambda p:(p/'extra').symlink_to(p/'absent')),
             ('symlink_code_directory',lambda p:((p/'code').rename(p/'moved_code'),(p/'code').symlink_to(p/'moved_code',target_is_directory=True)))]
    if hasattr(os,'mkfifo'):changes.append(('nonregular_fifo',lambda p:os.mkfifo(p/'extra')))
    for label,change in changes:
        p=copy(label);change(p)
        for optimized in (False,True):invoke(p,['check'],optimized=optimized,success=False)
        passed.append(label)
    link=destination/'linked_bundle';link.symlink_to(clean,target_is_directory=True)
    invoke(link,['check'],success=False);passed.append('symlink_bundle_ancestor')
    for label,mutator in fixture_mutations():
        p=copy(label);f=parse_json(data['checks/fixtures.json']);mutator(f);rehash(p,'checks/fixtures.json',json_bytes(f))
        for optimized in (False,True):invoke(p,['check'],optimized=optimized,success=False)
        passed.append(label)
    for filename in (MANIFEST,'checks/fixtures.json','sources/inventory.json'):
        label='duplicate_keys_'+filename.replace('/','_');p=copy(label)
        content=data[filename].replace(b'{',b'{"schema":"duplicate",',1)
        if filename==MANIFEST:(p/filename).write_bytes(content)
        else:rehash(p,filename,content)
        invoke(p,['check'],optimized=True,success=False);passed.append(label)
    p=copy('nonfinite_json');rehash(p,'checks/fixtures.json',b'{"schema":NaN}')
    invoke(p,['check'],success=False);passed.append('nonfinite_json')
    # These are fully resealed source mutations, including the source inventory,
    # so rejection tests the elapsed-value schema rather than an earlier hash.
    for label,token,reason in (
            ('boolean','true',b'audit elapsed provenance'),
            ('nan','NaN',b'nonfinite JSON token'),
            ('positive_infinity','Infinity',b'nonfinite JSON token'),
            ('negative_infinity','-Infinity',b'nonfinite JSON token'),
            ('positive_exponent_overflow','1e999',b'audit elapsed provenance'),
            ('negative_exponent_overflow','-1e999',b'audit elapsed provenance'),
            ('negative','-1',b'audit elapsed provenance'),
            ('string','"1"',b'audit elapsed provenance')):
        name='audit_elapsed_'+label;p=copy(name)
        filename='sources/independent_audit.json'
        raw,count=re.subn(rb'("elapsed_seconds"\s*:\s*)[-+0-9.eE]+',
                         lambda match:match.group(1)+token.encode('ascii'),data[filename])
        require(count==1,'elapsed regression must replace exactly one source field')
        revised=dict(data);revised[filename]=raw
        source_inventory=parse_json(data['sources/inventory.json'])
        source_inventory['files']['independent_audit.json'].update(
            bytes=len(raw),sha256=hashlib.sha256(raw).hexdigest())
        revised['sources/inventory.json']=json_bytes(source_inventory)
        for changed in (filename,'sources/inventory.json'):
            (p/changed).write_bytes(revised[changed])
        (p/MANIFEST).write_bytes(json_bytes(make_manifest(revised)))
        for optimized in (False,True):
            rejected=invoke(p,['check'],optimized=optimized,success=False)
            require(reason in rejected.stderr,'elapsed regression rejected before its schema check')
        passed.append(name+'_normal_and_optimized')
    for label,change in [('missing_manifest_record',lambda m:m['files'].pop('README.md')),
                         ('extra_manifest_record',lambda m:m['files'].update(extra={'bytes':0,'sha256':'0'*64})),
                         ('boolean_manifest_size',lambda m:m['files']['README.md'].update(bytes=True)),
                         ('float_manifest_size',lambda m:m['files']['README.md'].update(bytes=float(m['files']['README.md']['bytes']))),
                         ('wrong_manifest_hash_type',lambda m:m['files']['README.md'].update(sha256=1))]:
        p=copy(label);manifest=parse_json(data[MANIFEST]);change(manifest)
        (p/MANIFEST).write_bytes(json_bytes(manifest));invoke(p,['check'],success=False);passed.append(label)
    p=copy('rehashed_false_fixture');f=parse_json(data['checks/fixtures.json']);mutate_false_fixture(f)
    rehash(p,'checks/fixtures.json',json_bytes(f))
    invoke(p,['check']) # Integrity and types cannot certify numerical truth.
    target=destination/'false-fixture-result'
    invoke(p,['replay','--output',str(target)],optimized=True,success=False)
    require(not target.exists(),'failed replay created output');passed.append('rehashed_well_typed_false_fixture_rejected_by_replay')
    p=copy('shadow_import');marker=destination/'SHADOW_MODULE_WAS_EXECUTED'
    (p/'argparse.py').write_text('open('+repr(str(marker))+',"w").write("unsafe")\nraise RuntimeError("shadow imported")\n')
    for optimized in (False,True):
        rejected=invoke(p,['check'],optimized=optimized,isolated=False,success=False)
        require(b'isolated Python (-I) is required' in rejected.stderr,'missing early isolation rejection')
        require(not marker.exists(),'unsealed shadow module executed')
    invoke(p,['check'],isolated=True,success=False)
    require(not marker.exists(),'isolated shadow module executed');passed.append('nonisolated_shadowing_blocked_before_imports')
    p=copy('direct_code_shadow_import')
    (p/'code/fractions.py').write_text('open('+repr(str(marker))+',"w").write("unsafe")\nraise RuntimeError("shadow imported")\n')
    for optimized in (False,True):
        command=[sys.executable,'-B']+(['-O'] if optimized else [])+[str(p/'code/exact.py')]
        rejected=subprocess.run(command,stdout=subprocess.PIPE,stderr=subprocess.PIPE,timeout=30)
        require(rejected.returncode==2 and b'isolated Python (-I) is required' in rejected.stderr,'missing direct-code early isolation rejection')
        require(not marker.exists(),'direct-code shadow module executed')
        command=[sys.executable,'-I','-B']+(['-O'] if optimized else [])+[str(p/'code/exact.py')]
        safe=subprocess.run(command,stdout=subprocess.PIPE,stderr=subprocess.PIPE,timeout=30)
        require(safe.returncode==0 and not marker.exists(),'isolated direct-code import failed or executed shadow')
    passed.append('direct_code_nonisolated_shadowing_blocked_before_imports')
    # A rational fixture string resembling code is data and must not execute.
    p=copy('fixture_code_injection');f=parse_json(data['checks/fixtures.json'])
    inject_fixture(f,'__import__("pathlib").Path('+repr(str(marker))+').write_text("unsafe")')
    rehash(p,'checks/fixtures.json',json_bytes(f));invoke(p,['check'],optimized=True,success=False)
    require(not marker.exists(),'fixture content executed');passed.append('fixture_code_injection_refused')
    existing=destination/'existing';existing.mkdir()
    existing_file=destination/'existing_file';existing_file.write_text('preserve')
    symlink=destination/'linked_parent';symlink.symlink_to(existing,target_is_directory=True)
    guards=[('existing_directory',existing),('existing_file',existing_file),('inside_bundle',clean/'generated'),
            ('inside_code',clean/'code/generated'),('symlink_leaf',symlink),('symlink_ancestor',symlink/'generated'),
            ('parent_traversal',existing/'..'/'generated'),('missing_parent',destination/'absent'/'generated')]
    for label,path in guards:
        for command in ('replay','pack','build','seal','selftest','reproduce','deep'):
            invoke(clean,[command,'--output',str(path)],success=False)
        passed.append(label+'_all_output_commands')
    require(existing_file.read_text()=='preserve','existing output changed')
    require(not (clean/'generated').exists() and not (existing/'generated').exists(),'preflight created files')
    normal=destination/'normal-replay';optimized=destination/'optimized-replay'
    invoke(clean,['replay','--output',str(normal)])
    invoke(clean,['replay','--output',str(optimized)],optimized=True)
    require(read_regular(normal/'replay-result.json')==read_regular(optimized/'replay-result.json'),'normal/-O replay mismatch')
    passed.append('normal_and_optimized_byte_identical_full_replay')
    traversal=clean/'..'/'clean';invoke(traversal,['check'],success=False)
    invoke(traversal,['replay','--output',str(clean/'traversal-generated')],success=False)
    require(not (clean/'traversal-generated').exists(),'script traversal escaped containment');passed.append('script_path_parent_traversal_rejected')
    if os.name=='posix':
        alias=Path('//'+str(clean).lstrip('/'))
        invoke(alias,['replay','--output',str(clean/'alias-generated')],success=False)
        invoke(clean,['replay','--output','//'+str(clean/'alias-generated').lstrip('/')],success=False)
        require(not (clean/'alias-generated').exists(),'double-leading-slash alias escaped containment');passed.append('double_leading_slash_containment')
    first=destination/'first.zip';invoke(clean,['pack','--output',str(first)])
    extracted=destination/'extracted';extracted.mkdir()
    with zipfile.ZipFile(first) as archive:
        require(all(n.startswith('Report138/') and '..' not in Path(n).parts for n in archive.namelist()),'unsafe generated ZIP name')
        archive.extractall(extracted)
    second=destination/'second.zip';invoke(extracted/'Report138',['pack','--output',str(second)])
    require(read_regular(first)==read_regular(second),'repack byte mismatch');passed.append('fresh_extraction_byte_identical_repack')
    result={'status':'PASS','tests':passed}
    with create_output_file(destination/'selftest-result.json') as stream:stream.write(json_bytes(result))
    return result

def fixture_mutations():
    return [('boolean_integer',lambda f:f['gl2_crosscheck'].update(tests=True)),
            ('float_integer',lambda f:f['gluing'][0].update(unique=1.0)),
            ('string_integer',lambda f:f['gluing'][0].update(unique='1')),
            ('extra_fixture_key',lambda f:f.update(extra=1)),
            ('extra_nested_key',lambda f:f['gluing'][0].update(extra=1)),
            ('missing_nested_key',lambda f:f['leading'].pop('h0')),
            ('wrong_row_length',lambda f:f['avoidance']['rsk'].append(1)),
            ('numeric_rational',lambda f:f['leading'].update(h0=240)),
            ('noncanonical_rational',lambda f:f['leading'].update(h0='480/2')),
            ('null_status',lambda f:f.update(status=None)),
            ('false_source_match',lambda f:f['gluing'][0].update(source_match=False)),
            ('integer_source_match',lambda f:f['gluing'][0].update(source_match=1)),
            ('duplicate_boundary_tuple',lambda f:f['boundary_enumeration'][1]['counts'].__setitem__(1,f['boundary_enumeration'][1]['counts'][0]))]

def mutate_false_fixture(f):
    f['leading']['values'][1]['h']=str(Fraction(f['leading']['values'][1]['h'])+1)

def inject_fixture(f,value):
    f['leading']['h0']=value


def build(data,destination):
    create_output_directory(destination)
    with create_output_file(destination/'Report138.tex') as stream:stream.write(data['Report138.tex'])
    environment={k:v for k,v in os.environ.items() if k in ('PATH','SYSTEMROOT','WINDIR')}
    environment.update({'SOURCE_DATE_EPOCH':'1790899200','FORCE_SOURCE_DATE':'1','TZ':'UTC','LC_ALL':'C'})
    for variable,folder in [('HOME','home'),('TEXMFHOME','texmf-home'),('TEXMFVAR','texmf-var'),('TEXMFCONFIG','texmf-config'),('TEXMFCACHE','texmf-cache'),('XDG_CACHE_HOME','xdg-cache')]:
        p=destination/folder;p.mkdir();environment[variable]=str(p)
    if Path('/usr/share/texlive/texmf-dist').is_dir():environment['TEXMF']='{/usr/share/texlive/texmf-dist,/usr/share/texmf}'
    environment['TEXFORMATS']=str(destination)+'//:'
    format_command=['pdftex','-ini','-etex','-no-shell-escape','-interaction=nonstopmode','-halt-on-error','-jobname=pdflatex','pdflatex.ini']
    source=r'\pdfmapfile{+cm.map}\pdfmapfile{+cmextra.map}\pdfmapfile{+symbols.map}\pdfmapfile{+lm.map}\input{Report138.tex}'
    command=['pdflatex','-no-shell-escape','-interaction=nonstopmode','-halt-on-error','-file-line-error',source]
    with create_output_file(destination/'build-console.txt') as log:
        subprocess.run(format_command,cwd=destination,env=environment,stdout=log,stderr=subprocess.STDOUT,check=True,timeout=180)
        for _ in range(3):subprocess.run(command,cwd=destination,env=environment,stdout=log,stderr=subprocess.STDOUT,check=True,timeout=180)
    texlog=read_regular(destination/'Report138.log').decode('utf-8',errors='replace')
    for warning in (r'Overfull \hbox',r'Overfull \vbox','undefined references','multiply defined','undefined citations','Missing character:','Label(s) may have changed'):
        require(warning not in texlog,'TeX QA warning: '+warning)
    pdf=read_regular(destination/'Report138.pdf')
    version=subprocess.run(['pdftex','--version'],env=environment,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,check=True,timeout=30).stdout.decode('utf-8',errors='replace').splitlines()[0]
    result={'pdf_sha256':hashlib.sha256(pdf).hexdigest(),'matches_frozen_pdf_bytes':pdf==data['Report138.pdf'],'source_date_epoch':1790899200,'pdftex_version':version}
    with create_output_file(destination/'build-result.json') as stream:stream.write(json_bytes(result))
    return result

def deep(data,destination):
    create_output_directory(destination)
    source=destination/'object_check.cpp'
    with create_output_file(source) as stream:stream.write(data['code/object_check.cpp'])
    binary=destination/'object_check'
    command=['c++','-std=c++17','-O2','-Wall','-Wextra','-pedantic',str(source),'-o',str(binary)]
    with create_output_file(destination/'compile-console.txt') as log:
        subprocess.run(command,stdout=log,stderr=subprocess.STDOUT,check=True,timeout=180)
    run=subprocess.run([str(binary),'10'],stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=600)
    expected=[]
    for n,count in zip(range(5,11),(1,10,81,643,5254,44751)):
        expected.append('n='+str(n)+' forward_objects='+str(count)+' inverse_objects='+str(count)+' disjoint_objects='+str(count)+' all_object_round_trips=PASS spine=PASS northern=PASS statistics=PASS')
    require(run.stdout.decode('ascii').splitlines()==expected and not run.stderr,'object-level deep check differs from independent expected counts')
    with create_output_file(destination/'object-check.txt') as stream:stream.write(run.stdout)
    version=subprocess.run(['c++','--version'],stdout=subprocess.PIPE,stderr=subprocess.STDOUT,check=True,timeout=30).stdout.decode('utf-8',errors='replace').splitlines()[0]
    result={'status':'PASS','n_min':5,'n_max':10,'northern_objects_each_direction':[1,10,81,643,5254,44751],'compiler_flags':['-std=c++17','-O2','-Wall','-Wextra','-pedantic'],'compiler_version':version}
    with create_output_file(destination/'deep-result.json') as stream:stream.write(json_bytes(result))
    return result

def reproduce(data,destination):
    create_output_directory(destination)
    tests=selftest(data,destination/'selftest')
    first=build(data,destination/'build-one');second=build(data,destination/'build-two')
    require(first['pdf_sha256']==second['pdf_sha256'],'two fresh PDF builds differ')
    require(first['matches_frozen_pdf_bytes'] and second['matches_frozen_pdf_bytes'],'fresh builds differ from frozen PDF; inspect build-result.json for toolchain/source mismatch')
    result={'status':'PASS','selftest_count':len(tests['tests']),'fresh_builds_identical':True,
            'fresh_build_matches_frozen_pdf':True,'fresh_pdf_sha256':first['pdf_sha256'],
            'archive_sha256':hashlib.sha256(read_regular(destination/'selftest/first.zip')).hexdigest()}
    with create_output_file(destination/'reproduction-result.json') as stream:stream.write(json_bytes(result))
    return result

def main():
    parser=argparse.ArgumentParser(description='Report138 offline companion; isolated Python is mandatory.')
    sub=parser.add_subparsers(dest='command',required=True);sub.add_parser('check')
    for name in ('replay','selftest','pack','build','seal','reproduce','deep'):
        p=sub.add_parser(name);p.add_argument('--output',required=True,help='absent external path with an existing real parent')
    args=parser.parse_args();output=preflight_output(args.output) if hasattr(args,'output') else None
    if args.command=='seal':
        data=inventory(sealing=True);validate_payload(data)
        with create_output_file(output) as stream:stream.write(json_bytes(make_manifest(data)))
        print('Wrote external manifest; review and install manually: '+str(output));return
    data=verify()
    if args.command=='check':print('PASS: closed inventory, SHA256, typed fixtures, source inventory and source overlaps')
    elif args.command=='replay':
        result=replay(data);create_output_directory(output)
        with create_output_file(output/'replay-result.json') as stream:stream.write(json_bytes(result))
        print('PASS: full exact replay '+str(output/'replay-result.json'))
    elif args.command=='pack':print('Packed SHA256 '+pack(data,output))
    elif args.command=='build':print(json.dumps(build(data,output),sort_keys=True))
    elif args.command=='deep':print(json.dumps(deep(data,output),sort_keys=True))
    elif args.command=='selftest':print('Selftest PASS: '+str(len(selftest(data,output)['tests']))+' tests')
    elif args.command=='reproduce':print(json.dumps(reproduce(data,output),sort_keys=True))

if __name__=='__main__':
    try:main()
    except (Rejected,ValueError,KeyError,TypeError,OSError,RuntimeError,subprocess.CalledProcessError,subprocess.TimeoutExpired) as error:
        print('REJECTED: '+str(error),file=sys.stderr);sys.exit(1)
