#!/usr/bin/env python3
import sys
if not sys.flags.isolated:
    sys.stderr.write('REJECTED: isolated Python (-I) is required before any imports\n')
    raise SystemExit(2)
sys.dont_write_bytecode = True

"""Read-only integrity checks, exact replay, external builds, and deterministic packs."""
import argparse
from fractions import Fraction
import hashlib
import json
import os
from pathlib import Path
import stat
import subprocess
import types
import zipfile

ROOT = Path(__file__).absolute().parent
CODE = ('exact_algebra.py','gaussian.py','models.py','regularized.py','inverse.py','replay.py')
OLD_BASE = frozenset({'README.md','SOURCES.md','Report135.tex','Report135.pdf',
                     'refinements.py','second_refinements.py','kernel_sympy.py','unitary_checks.py',
                     'exact_data.json','second_exact_data.json','verify.py','manifest.json'})
OLD134 = frozenset({'README.md','Report134.tex','Report134.pdf','certificate.py',
                    'independent.py','fixtures.json','verify.py','manifest.json'})
OLD135 = OLD_BASE | frozenset('companion134/'+n for n in OLD134)
PAYLOAD = frozenset({'README.md','SOURCES.md','Report137.tex','Report137.pdf','verify.py',
                     'checks/fixtures.json'}) | frozenset('code/'+n for n in CODE) | frozenset('companion135/'+n for n in OLD135)
DIRECTORIES = frozenset({'code','checks','companion135','companion135/companion134'})
MANIFEST = 'manifest.json'
SCHEMA = 'report137-sha256-v1'
OLD135_MANIFEST_SHA256 = '27499b894d1f92be6e73cc016da60a4d0b7f65b663eefa561a7fd6c811015251'
OLD134_MANIFEST_SHA256 = '87bd951e61b6a51fd8f8ec534b0bf64545535ddd7498f75013ef6656e08ed94b'

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
    # Canonicalize only after the lexical lstat walk rejected symlinks/traversal.
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
    found={}
    seen_directories=set()
    for directory,subdirs,files in os.walk(root,followlinks=False):
        for name in subdirs:
            p=Path(directory)/name
            rel=p.relative_to(root).as_posix()
            require(rel in DIRECTORIES and stat.S_ISDIR(p.lstat().st_mode),'unexpected directory or symlink: '+rel)
            seen_directories.add(rel)
        for name in files:
            p=Path(directory)/name
            require(stat.S_ISREG(p.lstat().st_mode),'nonregular file: '+str(p))
            found[p.relative_to(root).as_posix()]=read_regular(p)
    require(seen_directories==DIRECTORIES,'directory inventory mismatch')
    expected=PAYLOAD|{MANIFEST}
    if sealing and MANIFEST not in found:
        expected=PAYLOAD
    require(set(found)==expected,'closed inventory mismatch; missing='+str(sorted(expected-set(found)))+
            '; extra='+str(sorted(set(found)-expected)))
    return found


def keys(value,expected,label):
    require(type(value) is dict and set(value)==set(expected),label+' keys/type')


def integer(value,label,expected=None):
    require(type(value) is int,label+' must be an integer, not bool or float')
    if expected is not None:
        require(value==expected,label+' value')


def rational(value,label):
    require(type(value) is str,label+' must be a canonical rational string')
    require(str(Fraction(value))==value,label+' noncanonical rational')


def rational_list(value,length,label):
    require(type(value) is list and len(value)==length,label+' list length/type')
    for x in value:
        rational(x,label)


def integer_list(value,expected,label):
    require(type(value) is list and len(value)==len(expected),label+' list length/type')
    for x,y in zip(value,expected):
        integer(x,label,y)


def text(value,label):
    require(type(value) is str and bool(value),label+' must be a nonempty string')


def validate_fixtures(data):
    f=parse_json(data['checks/fixtures.json'])
    keys(f,{'schema','gaussian','singular_models_and_constants','synthetic_regularization','inverse'},'fixtures')
    require(f['schema']=='report137-replay-v1','fixture schema')
    g=f['gaussian']
    keys(g,{'normalization','avoidance','weak_composition_moment_checks','boundary_samples','half_samples_divided_by_C0','scope'},'Gaussian')
    rational(g['normalization'],'Gaussian normalization');rational_list(g['avoidance'],4,'avoidance')
    integer(g['weak_composition_moment_checks'],'composition count',1092)
    for field,labels in [('boundary_samples',{'0,0','0,1','1,1','2,0','2,2','2,3','3,2','4,0'}),
                         ('half_samples_divided_by_C0',{'0,0','0,1','1,0','1,1','2,0'})]:
        keys(g[field],labels,field)
        for label,row in g[field].items(): rational_list(row,4,field+' '+label)
    text(g['scope'],'Gaussian scope')
    m=f['singular_models_and_constants']
    keys(m,{'single_log_checks','log_square_checks','small_model_coefficients','V3_through_V6_rows',
            'single_log_c_rows','avoidance_inverse','r3_shiftweights_c0_to_c3','kappa4_shiftweight',
            'kernel_CC','kernel_CB','kappa3_in_sqrt3_over_pi_units','kappa4_in_sqrt3_over_pi_units','scope'},'models')
    integer(m['single_log_checks'],'single log count',754);integer(m['log_square_checks'],'square log count',5096)
    keys(m['small_model_coefficients'],set(map(str,range(3,7))),'small model coefficients')
    for k in range(3,7): rational_list(m['small_model_coefficients'][str(k)],k+1,'small coefficients')
    for field in ('V3_through_V6_rows','single_log_c_rows'):
        require(type(m[field]) is list and len(m[field])==4,field+' rows')
        for row in m[field]: rational_list(row,4,field)
    for field in ('avoidance_inverse','r3_shiftweights_c0_to_c3'): rational_list(m[field],4,field)
    for field in ('kappa4_shiftweight','kernel_CC','kernel_CB','kappa3_in_sqrt3_over_pi_units','kappa4_in_sqrt3_over_pi_units'):
        rational(m[field],field)
    text(m['scope'],'model scope')
    r=f['synthetic_regularization']
    keys(r,{'K','residual_rising_factor_count','singular_coefficients','exact_regularized_T0_through_T5',
            'tail_checks','vanishing_moment_orders','convolution_diagnostics','scope'},'regularization')
    integer(r['K'],'K',6);integer(r['residual_rising_factor_count'],'residual degree',8)
    keys(r['singular_coefficients'],set(map(str,range(3,7))),'synthetic singular coefficients')
    for v in r['singular_coefficients'].values(): rational(v,'synthetic singular coefficient')
    rational_list(r['exact_regularized_T0_through_T5'],6,'synthetic T values')
    require(type(r['tail_checks']) is list and len(r['tail_checks'])==16,'synthetic tail rows')
    for row,(j,N) in zip(r['tail_checks'],((j,N) for j in range(4) for N in (16,32,64,128))):
        keys(row,{'j','N','absolute_error','certified_upper_bound'},'synthetic tail row')
        integer(row['j'],'tail j',j);integer(row['N'],'tail N',N)
        rational(row['absolute_error'],'tail error');rational(row['certified_upper_bound'],'tail bound')
    integer_list(r['vanishing_moment_orders'],list(range(6)),'vanishing moments')
    require(type(r['convolution_diagnostics']) is list and len(r['convolution_diagnostics'])==3,'convolution diagnostics')
    for row,n in zip(r['convolution_diagnostics'],(32,64,128)):
        keys(row,{'n','n_power_K_plus_2_times_error'},'convolution row')
        integer(row['n'],'convolution n',n);rational(row['n_power_K_plus_2_times_error'],'scaled convolution error')
    text(r['scope'],'regularization scope')
    q=f['inverse']
    keys(q,{'symbolic_Q1_Q2','direct_log_degrees_orders_1_to_9','synthetic_samples','scope'},'inverse')
    text(q['symbolic_Q1_Q2'],'symbolic check');text(q['scope'],'inverse scope')
    integer_list(q['direct_log_degrees_orders_1_to_9'],[0,0,1,1,1,2,2,2,3],'direct log degrees')
    require(type(q['synthetic_samples']) is list and len(q['synthetic_samples'])==2,'inverse sample count')
    for row in q['synthetic_samples']:
        keys(row,{'lambda_formal_value','eta_formal_value','d_formal_value',
                  'Q1_through_Q9_ascending_coefficients','zero_residual_orders'},'inverse sample')
        for field in ('lambda_formal_value','eta_formal_value','d_formal_value'): rational(row[field],field)
        integer_list(row['zero_residual_orders'],list(range(10)),'inverse cancellation orders')
        require(type(row['Q1_through_Q9_ascending_coefficients']) is list and len(row['Q1_through_Q9_ascending_coefficients'])==9,'inverse coefficient rows')
        for j,coefficients in enumerate(row['Q1_through_Q9_ascending_coefficients'],1):
            rational_list(coefficients,j+1,'inverse polynomial coefficients')
    return f


def validate_manifest(raw,schema,payload,data,prefix=''):
    manifest=parse_json(raw)
    keys(manifest,{'schema','files'},'manifest')
    require(manifest['schema']==schema,'manifest schema')
    keys(manifest['files'],payload,'manifest records')
    for name in sorted(payload):
        rec=manifest['files'][name]
        keys(rec,{'bytes','sha256'},'manifest file record')
        content=data[prefix+name]
        integer(rec['bytes'],'manifest size',len(content))
        require(type(rec['sha256']) is str and rec['sha256']==hashlib.sha256(content).hexdigest(),'SHA256 mismatch: '+prefix+name)
    return manifest


def validate_companion(data):
    raw=data['companion135/manifest.json']
    require(hashlib.sha256(raw).hexdigest()==OLD135_MANIFEST_SHA256,'changed frozen Report135 manifest')
    validate_manifest(raw,'report135-sha256-v1',OLD135-{'manifest.json'},data,'companion135/')
    raw=data['companion135/companion134/manifest.json']
    require(hashlib.sha256(raw).hexdigest()==OLD134_MANIFEST_SHA256,'changed frozen Report134 manifest')
    validate_manifest(raw,'report134-sha256-v1',OLD134-{'manifest.json'},data,'companion135/companion134/')


def validate_payload(data):
    validate_companion(data)
    validate_fixtures(data)
    require(data['Report137.pdf'].startswith(b'%PDF-'),'Report137 is not a PDF')
    require(b'\\begin{document}' in data['Report137.tex'] and b'\\end{document}' in data['Report137.tex'],'incomplete Report137 TeX')


def verify(root=ROOT):
    data=inventory(root)
    validate_manifest(data[MANIFEST],SCHEMA,PAYLOAD,data)
    validate_payload(data)
    return data


def make_manifest(data):
    return {'schema':SCHEMA,'files':{name:{'bytes':len(data[name]),'sha256':hashlib.sha256(data[name]).hexdigest()} for name in sorted(PAYLOAD)}}


def replay(data):
    # Execute only byte strings that have passed the top-level manifest checks.
    modules={}
    for filename in CODE:
        name=filename[:-3]
        module=types.ModuleType(name)
        module.__file__=str(ROOT/'code'/filename)
        sys.modules[name]=module
        exec(compile(data['code/'+filename],'code/'+filename,'exec'),module.__dict__)
        modules[name]=module
    result=modules['replay'].run()
    require(result==validate_fixtures(data),'recomputed exact results differ from the sealed fixtures')
    return result


def pack(data,destination):
    with create_output_file(destination) as stream:
        with zipfile.ZipFile(stream,'w',compression=zipfile.ZIP_STORED) as archive:
            for name in sorted(data):
                info=zipfile.ZipInfo('Report137/'+name,date_time=(1980,1,1,0,0,0))
                info.create_system=3
                info.external_attr=(stat.S_IFREG|0o644)<<16
                info.compress_type=zipfile.ZIP_STORED
                info.flag_bits=0
                archive.writestr(info,data[name])
    return hashlib.sha256(read_regular(destination)).hexdigest()


def invoke(root,args,optimized=False,isolated=True,success=True):
    command=[sys.executable]+(['-I'] if isolated else [])+['-B']+(['-O'] if optimized else [])+[str(root/'verify.py')]+args
    run=subprocess.run(command,stdout=subprocess.PIPE,stderr=subprocess.PIPE,timeout=180)
    require((run.returncode==0)==success,'unexpected subprocess result: '+str(args)+' '+run.stderr.decode(errors='replace'))
    return run


def selftest(data,destination):
    create_output_directory(destination)
    passed=[]
    def copy(label):
        root=destination/label
        root.mkdir()
        for directory in sorted(DIRECTORIES,key=lambda s:(s.count('/'),s)):
            (root/directory).mkdir()
        for name,content in data.items():
            (root/name).write_bytes(content)
        return root
    def rehash(root,filename,content):
        (root/filename).write_bytes(content)
        revised=dict(data);revised[filename]=content
        (root/MANIFEST).write_bytes(json_bytes(make_manifest(revised)))
    clean=copy('clean')
    invoke(clean,['check']);invoke(clean,['check'],optimized=True)
    passed.append('normal_and_optimized_integrity')
    changes=[('extra_file',lambda p:(p/'extra').write_text('x')),
             ('extra_directory',lambda p:(p/'extra').mkdir()),
             ('missing_pdf',lambda p:(p/'Report137.pdf').unlink()),
             ('changed_code',lambda p:(p/'code/models.py').write_bytes(data['code/models.py']+b'\n')),
             ('changed_companion135',lambda p:(p/'companion135/README.md').write_text('changed')),
             ('changed_companion134',lambda p:(p/'companion135/companion134/README.md').write_text('changed')),
             ('symlink_file',lambda p:(p/'extra').symlink_to(p/'README.md')),
             ('broken_symlink',lambda p:(p/'extra').symlink_to(p/'absent')),
             ('symlink_code_directory',lambda p:((p/'code').rename(p/'moved_code'),(p/'code').symlink_to(p/'moved_code',target_is_directory=True)))]
    if hasattr(os,'mkfifo'):
        changes.append(('nonregular_fifo',lambda p:os.mkfifo(p/'extra')))
    for label,change in changes:
        p=copy(label);change(p);invoke(p,['check'],optimized=True,success=False);passed.append(label)
    link=destination/'linked_bundle';link.symlink_to(clean,target_is_directory=True)
    invoke(link,['check'],success=False);passed.append('symlink_bundle_ancestor')
    fixture_mutations=[('boolean_integer',lambda f:f['gaussian'].update(weak_composition_moment_checks=True)),
                       ('float_integer',lambda f:f['synthetic_regularization'].update(K=6.0)),
                       ('extra_fixture_key',lambda f:f.update(extra=1)),
                       ('extra_nested_key',lambda f:f['inverse']['synthetic_samples'][0].update(extra=1)),
                       ('missing_nested_key',lambda f:f['gaussian']['boundary_samples'].pop('2,0')),
                       ('noncanonical_fraction',lambda f:f['gaussian'].update(normalization='162/4')),
                       ('numeric_fraction',lambda f:f['gaussian'].update(normalization=40.5)),
                       ('null_scope',lambda f:f['inverse'].update(scope=None)),
                       ('wrong_row_length',lambda f:f['gaussian']['avoidance'].append('0')),
                       ('string_integer',lambda f:f['synthetic_regularization'].update(K='6'))]
    for label,change in fixture_mutations:
        p=copy(label);fixture=parse_json(data['checks/fixtures.json']);change(fixture)
        rehash(p,'checks/fixtures.json',json_bytes(fixture))
        invoke(p,['check'],optimized=True,success=False);passed.append(label)
    for label,change in [('wrong_well_typed_kappa4',lambda f:f['singular_models_and_constants'].update(kappa4_in_sqrt3_over_pi_units='123')),
                         ('wrong_well_typed_r3_weight',lambda f:f['singular_models_and_constants']['r3_shiftweights_c0_to_c3'].__setitem__(0,'7')),
                         ('wrong_well_typed_gaussian',lambda f:f['gaussian']['avoidance'].__setitem__(3,'1')),
                         ('wrong_well_typed_tail',lambda f:f['synthetic_regularization']['tail_checks'][0].update(absolute_error='1')),
                         ('wrong_well_typed_inverse',lambda f:f['inverse']['synthetic_samples'][0]['Q1_through_Q9_ascending_coefficients'][0].__setitem__(0,'1'))]:
        p=copy(label);fixture=parse_json(data['checks/fixtures.json']);change(fixture)
        rehash(p,'checks/fixtures.json',json_bytes(fixture))
        target=destination/(label+'-result')
        invoke(p,['replay','--output',str(target)],optimized=True,success=False)
        require(not target.exists(),'failed replay created output')
        passed.append(label)
    for label,change in [('missing_manifest_record',lambda m:m['files'].pop('README.md')),
                         ('extra_manifest_record',lambda m:m['files'].update(extra={'bytes':0,'sha256':'0'*64})),
                         ('boolean_manifest_size',lambda m:m['files']['README.md'].update(bytes=True)),
                         ('float_manifest_size',lambda m:m['files']['README.md'].update(bytes=float(m['files']['README.md']['bytes']))),
                         ('wrong_manifest_hash_type',lambda m:m['files']['README.md'].update(sha256=1))]:
        p=copy(label);manifest=parse_json(data[MANIFEST]);change(manifest)
        (p/MANIFEST).write_bytes(json_bytes(manifest));invoke(p,['check'],success=False);passed.append(label)
    for filename in (MANIFEST,'checks/fixtures.json'):
        label='duplicate_keys_'+filename.replace('/','_')
        p=copy(label);content=data[filename].replace(b'{',b'{"schema":"duplicate",',1)
        if filename==MANIFEST: (p/filename).write_bytes(content)
        else: rehash(p,filename,content)
        invoke(p,['check'],optimized=True,success=False);passed.append(label)
    p=copy('nonfinite_json');rehash(p,'checks/fixtures.json',data['checks/fixtures.json'].replace(b'1092',b'NaN',1))
    invoke(p,['check'],success=False);passed.append('nonfinite_json')
    for label,filename in [('reseal_changed135','companion135/README.md'),('reseal_changed134','companion135/companion134/README.md')]:
        p=copy(label);(p/filename).write_text('changed')
        target=destination/(label+'.json');invoke(p,['seal','--output',str(target)],success=False)
        require(not target.exists(),'failed seal created output');passed.append(label)
    # Even a top-level rehash cannot bless changes inside the frozen companions.
    p=copy('rehashed_changed_companion');rehash(p,'companion135/README.md',b'changed')
    invoke(p,['check'],success=False);passed.append('rehashed_changed_companion')
    # The -I guard is built-in-only and precedes argparse, pathlib, json, etc.
    # This tests both ordinary and optimized non-isolated launches.
    p=copy('shadow_import');marker=destination/'SHADOW_MODULE_WAS_EXECUTED'
    (p/'argparse.py').write_text('open('+repr(str(marker))+',"w").write("unsafe")\nraise RuntimeError("shadow imported")\n')
    for optimized in (False,True):
        rejected=invoke(p,['check'],optimized=optimized,isolated=False,success=False)
        require(b'isolated Python (-I) is required' in rejected.stderr,'missing early isolation rejection')
        require(not marker.exists(),'unsealed shadow module executed')
    invoke(p,['check'],isolated=True,success=False)
    require(not marker.exists(),'isolated shadow module executed')
    passed.append('unsealed_shadow_import_blocked_before_imports')
    existing=destination/'existing';existing.mkdir()
    existing_file=destination/'existing_file';existing_file.write_text('preserve')
    symlink=destination/'linked_parent';symlink.symlink_to(existing,target_is_directory=True)
    guards=[('existing_directory',existing),('existing_file',existing_file),('inside_bundle',clean/'generated'),
            ('inside_companion',clean/'companion135/generated'),('symlink_leaf',symlink),
            ('symlink_ancestor',symlink/'generated'),('parent_traversal',existing/'..'/'generated'),
            ('missing_parent',destination/'absent'/'generated')]
    for label,path in guards:
        for command in ('replay','pack','build','seal','selftest','reproduce'):
            invoke(clean,[command,'--output',str(path)],success=False)
        passed.append(label+'_all_output_commands')
    require(existing_file.read_text()=='preserve','existing output changed')
    require(not (clean/'generated').exists() and not (existing/'generated').exists(),'preflight created files')
    normal=destination/'normal-replay';optimized=destination/'optimized-replay'
    invoke(clean,['replay','--output',str(normal)])
    invoke(clean,['replay','--output',str(optimized)],optimized=True)
    require(read_regular(normal/'replay-result.json')==read_regular(optimized/'replay-result.json'),'normal/-O replay mismatch')
    passed.append('normal_and_optimized_byte_identical_replay')
    # Python preserves parent components in __file__; reject script-path traversal.
    traversal=clean/'..'/'clean'
    invoke(traversal,['check'],success=False)
    invoke(traversal,['replay','--output',str(clean/'traversal-generated')],success=False)
    require(not (clean/'traversal-generated').exists(),'script traversal escaped containment')
    passed.append('script_path_parent_traversal_rejected')
    # On POSIX, double-leading slash may name the same file with a different lexical anchor.
    if os.name=='posix':
        alias=Path('//'+str(clean).lstrip('/'))
        invoke(alias,['replay','--output',str(clean/'alias-generated')],success=False)
        invoke(clean,['replay','--output','//'+str(clean/'alias-generated').lstrip('/')],success=False)
        require(not (clean/'alias-generated').exists(),'double-leading-slash alias escaped containment')
        passed.append('double_leading_slash_containment')
    first=destination/'first.zip';invoke(clean,['pack','--output',str(first)])
    extracted=destination/'extracted';extracted.mkdir()
    with zipfile.ZipFile(first) as archive:
        require(all(n.startswith('Report137/') and '..' not in Path(n).parts for n in archive.namelist()),'unsafe generated ZIP name')
        archive.extractall(extracted)
    second=destination/'second.zip';invoke(extracted/'Report137',['pack','--output',str(second)])
    require(read_regular(first)==read_regular(second),'repack byte mismatch')
    passed.append('fresh_extraction_byte_identical_repack')
    result={'status':'PASS','tests':passed}
    with create_output_file(destination/'selftest-result.json') as stream: stream.write(json_bytes(result))
    return result


def build(data,destination):
    create_output_directory(destination)
    with create_output_file(destination/'Report137.tex') as stream: stream.write(data['Report137.tex'])
    environment={k:v for k,v in os.environ.items() if k in ('PATH','SYSTEMROOT','WINDIR')}
    environment.update({'SOURCE_DATE_EPOCH':'1790899200','FORCE_SOURCE_DATE':'1','TZ':'UTC','LC_ALL':'C'})
    for variable,folder in [('HOME','home'),('TEXMFHOME','texmf-home'),('TEXMFVAR','texmf-var'),
                            ('TEXMFCONFIG','texmf-config'),('TEXMFCACHE','texmf-cache'),
                            ('XDG_CACHE_HOME','xdg-cache')]:
        p=destination/folder;p.mkdir();environment[variable]=str(p)
    if Path('/usr/share/texlive/texmf-dist').is_dir():
        environment['TEXMF']='{/usr/share/texlive/texmf-dist,/usr/share/texmf}'
    environment['TEXFORMATS']=str(destination)+'//:'
    format_command=['pdftex','-ini','-etex','-no-shell-escape','-interaction=nonstopmode',
                    '-halt-on-error','-jobname=pdflatex','pdflatex.ini']
    source=r'\pdfmapfile{+cm.map}\pdfmapfile{+cmextra.map}\pdfmapfile{+symbols.map}\pdfmapfile{+lm.map}\input{Report137.tex}'
    command=['pdflatex','-no-shell-escape','-interaction=nonstopmode','-halt-on-error','-file-line-error',source]
    with create_output_file(destination/'build-console.txt') as log:
        subprocess.run(format_command,cwd=destination,env=environment,stdout=log,stderr=subprocess.STDOUT,check=True,timeout=180)
        for _ in range(2):
            subprocess.run(command,cwd=destination,env=environment,stdout=log,stderr=subprocess.STDOUT,check=True,timeout=180)
    texlog=read_regular(destination/'Report137.log').decode('utf-8',errors='replace')
    for warning in (r'Overfull \hbox',r'Overfull \vbox','undefined references','multiply defined',
                    'undefined citations','Missing character:','Label(s) may have changed'):
        require(warning not in texlog,'TeX QA warning: '+warning)
    pdf=read_regular(destination/'Report137.pdf')
    result={'pdf_sha256':hashlib.sha256(pdf).hexdigest(),'matches_frozen_pdf_bytes':pdf==data['Report137.pdf'],
            'source_date_epoch':1790899200}
    with create_output_file(destination/'build-result.json') as stream: stream.write(json_bytes(result))
    return result


def reproduce(data,destination):
    create_output_directory(destination)
    tests=selftest(data,destination/'selftest')
    first=build(data,destination/'build-one')
    second=build(data,destination/'build-two')
    require(first['pdf_sha256']==second['pdf_sha256'],'two fresh PDF builds differ')
    require(first['matches_frozen_pdf_bytes'] and second['matches_frozen_pdf_bytes'],
            'fresh builds differ from frozen PDF: use build-result.json to diagnose toolchain/source mismatch')
    result={'status':'PASS','selftest_count':len(tests['tests']),'fresh_builds_identical':True,
            'fresh_build_matches_frozen_pdf':first['matches_frozen_pdf_bytes'],
            'fresh_pdf_sha256':first['pdf_sha256'],
            'archive_sha256':hashlib.sha256(read_regular(destination/'selftest/first.zip')).hexdigest()}
    with create_output_file(destination/'reproduction-result.json') as stream: stream.write(json_bytes(result))
    return result


def main():
    parser=argparse.ArgumentParser(description='Report137 offline reproducibility companion; isolated Python is mandatory.')
    sub=parser.add_subparsers(dest='command',required=True)
    sub.add_parser('check')
    for name in ('replay','selftest','pack','build','seal','reproduce'):
        p=sub.add_parser(name);p.add_argument('--output',required=True,help='absent external path with an existing real parent')
    args=parser.parse_args()
    output=preflight_output(args.output) if hasattr(args,'output') else None
    if args.command=='seal':
        data=inventory(sealing=True);validate_payload(data)
        with create_output_file(output) as stream: stream.write(json_bytes(make_manifest(data)))
        print('Wrote external manifest; review and install manually: '+str(output));return
    data=verify()
    if args.command=='check':
        print('PASS: closed inventory, hashes, typed fixtures, unchanged Report135 and Report134')
    elif args.command=='replay':
        result=replay(data);create_output_directory(output)
        with create_output_file(output/'replay-result.json') as stream: stream.write(json_bytes(result))
        print('PASS: exact replay '+str(output/'replay-result.json'))
    elif args.command=='pack':
        print('Packed SHA256 '+pack(data,output))
    elif args.command=='build':
        print(json.dumps(build(data,output),sort_keys=True))
    elif args.command=='selftest':
        result=selftest(data,output);print('Selftest PASS: '+str(len(result['tests']))+' tests')
    elif args.command=='reproduce':
        print(json.dumps(reproduce(data,output),sort_keys=True))

if __name__=='__main__':
    try:
        main()
    except (Rejected,ValueError,KeyError,TypeError,OSError,subprocess.CalledProcessError,subprocess.TimeoutExpired) as error:
        print('REJECTED: '+str(error),file=sys.stderr);sys.exit(1)
