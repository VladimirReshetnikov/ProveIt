#!/usr/bin/env python3
import sys
if not sys.flags.isolated:
    sys.stderr.write('REJECTED: isolated Python (-I) is required before any imports\n')
    raise SystemExit(2)
sys.dont_write_bytecode = True

"""Read-only Report142 verifier and reproducible external-output workflows."""
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
CODE = ('second.py', 'finite.py')
FOUNDATION_SHA256 = {'Report141.tex':'284c974be9274ee926c5e101a12ebc1abe42efc18b99b67d2db2700d2a440824','Report141.pdf':'2cbfc7ceebca3691c23606f37e7c1e6c6fc92e8080788f9d0d54197dc664d807'}
PAYLOAD = frozenset({'README.md','SOURCES.md','Report142.tex','Report142.pdf','verify.py','checks/fixtures.json'}) | frozenset('code/'+n for n in CODE) | frozenset('foundation141/'+n for n in FOUNDATION_SHA256)
DIRECTORIES = frozenset({'code','checks','foundation141'})
MANIFEST = 'manifest.json'
SCHEMA = 'report142-sha256-v1'

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
    return json.loads(data.decode('utf-8'),object_pairs_hook=no_duplicate_keys,parse_constant=reject_constant,parse_float=reject_constant)


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


def list_length(value, length, label):
    require(type(value) is list and len(value)==length,label+' length/type')


def rational_list(value, label, length=None):
    require(type(value) is list and len(value)>=1,label+' list/type')
    if length is not None: require(len(value)==length,label+' length')
    for item in value: rational(item,label)


def quadratic(value,label): rational_list(value,label,2)


def rational_function(value,label):
    keys(value,{'numerator','denominator'},label)
    for part in value:
        rational_list(value[part],label+' '+part)
        require(len(value[part])==1 or value[part][-1]!='0',label+' trailing zero')
    require(value['denominator'][-1]=='1',label+' monic denominator')


def validate_second(f):
    keys(f, {'field_radicand','rational_functions','diagonal','checks'}, 'second')
    integer(f['field_radicand'],'field radicand',17)
    dimensions={'r1':(5,5),'r2':(11,11),'D1':(7,6),'D2':(13,11),'B1':(3,3),'B2':(5,7)}
    keys(f['rational_functions'],dimensions,'second rational functions')
    for name,(numerator,denominator) in dimensions.items():
        v=f['rational_functions'][name];rational_function(v,name)
        list_length(v['numerator'],numerator,name+' numerator')
        list_length(v['denominator'],denominator,name+' denominator')
    keys(f['diagonal'],{'b1','b2','factorial1','factorial2','ratio2','saddle2','lambda1','lambda2'},'diagonal')
    for name,v in f['diagonal'].items():
        if name.startswith('factorial'): rational(v,name)
        else: quadratic(v,name)
    expected={'target_equalities':6,'odd_gaussian_zeros':2,'kernel_zero_shift_zeros':2,
              'residual_zero_atom':1,'normalized_moments_generated':19}
    keys(f['checks'],expected,'second checks')
    for name,value in expected.items(): integer(f['checks'][name],name,value)


def validate_finite(f):
    keys(f,{'schema_version','status','arithmetic','top_coefficients','frozen_inverse','saddle'},'finite')
    integer(f['schema_version'],'finite schema',1)
    require(f['status']=='PASS' and type(f['status']) is str,'finite status')
    require(f['arithmetic']=='exact rational' and type(f['arithmetic']) is str,'finite arithmetic')
    top=f['top_coefficients']
    values={'maximum_order':7,'maximum_n':21,'degree_bound_checks':8,'boundary_zero_checks':28,
            'falling_divisibility_checks':8,'direct_recurrence_checks':176,'integer_value_checks':176}
    keys(top,set(values)|{'polynomials'},'top coefficients')
    for name,value in values.items():integer(top[name],name,value)
    list_length(top['polynomials'],8,'top polynomials')
    for order,row in enumerate(top['polynomials']):
        keys(row,{'order','degree','coefficients','falling_quotient_coefficients'},'top polynomial')
        integer(row['order'],'top order',order);integer(row['degree'],'top degree',2*order)
        rational_list(row['coefficients'],'top polynomial coefficients',2*order+1)
        rational_list(row['falling_quotient_coefficients'],'top quotient coefficients',order+1)
        require(row['coefficients'][-1]!='0' and row['falling_quotient_coefficients'][-1]!='0','top trailing zero')
    frozen=f['frozen_inverse']
    values={'maximum_degree':40,'sqrt_coefficient_checks':40,'basis_coefficient_checks':860,'direct_coefficient_checks':360}
    keys(frozen,set(values)|{'weights','samples'},'frozen inverse')
    for name,value in values.items():integer(frozen[name],name,value)
    list_length(frozen['weights'],40,'frozen weights')
    for degree,row in enumerate(frozen['weights'],1):
        keys(row,{'degree','gamma','delta'},'frozen weight');integer(row['degree'],'frozen degree',degree)
        rational(row['gamma'],'gamma');rational(row['delta'],'delta')
        require(Fraction(row['gamma'])>0 and Fraction(row['delta'])>0,'positive frozen weights')
    samples=('1/5','1/2','4/5','19/20')
    list_length(frozen['samples'],4,'frozen samples')
    for s,row in zip(samples,frozen['samples']):
        keys(row,{'s','maximum_degree','coefficient_checks','maximum_absolute_residual'},'frozen sample')
        rational(row['s'],'sample saddle');require(row['s']==s,'ordered frozen saddle')
        integer(row['maximum_degree'],'direct maximum degree',12);integer(row['coefficient_checks'],'direct coefficient checks',90)
        rational(row['maximum_absolute_residual'],'frozen residual')
        require(row['maximum_absolute_residual']=='0','nonzero frozen residual')
    saddle=f['saddle']
    values={'maximum_order':3,'sample_count':4,'shift_count':5,'first_order_formula_checks':20,
            'unshifted_second_order_formula_checks':4,'quotient_coefficient_checks':80,'zero_shift_positive_order_checks':12}
    keys(saddle,set(values)|{'cases'},'saddle')
    for name,value in values.items():integer(saddle[name],name,value)
    list_length(saddle['cases'],20,'saddle cases')
    pairs=[(s,ell,r) for s in samples for ell,r in ((0,0),(1,0),(1,1),(3,1),(4,3))]
    for row,(s,ell,r) in zip(saddle['cases'],pairs):
        keys(row,{'s','ell','r','D','V'},'saddle case')
        rational(row['s'],'saddle');require(row['s']==s,'ordered saddle')
        integer(row['ell'],'ell',ell);integer(row['r'],'r',r)
        rational_list(row['D'],'raw saddle series',4);rational_list(row['V'],'normalized saddle series',4)


def validate_fixtures(data):
    f=parse_json(data['checks/fixtures.json'])
    keys(f,{'schema','status','scope','second','finite'},'fixtures')
    require(f['schema']=='report142-exact-v1' and f['status']=='PASS','fixture schema/status')
    require(type(f['scope']) is str and f['scope']=='Exact finite checks; analytic remainder proof is in Report142.','fixture scope')
    validate_second(f['second']);validate_finite(f['finite'])
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


def validate_payload(data):
    validate_fixtures(data)
    require(data['Report142.pdf'].startswith(b'%PDF-'),'Report142 is not a PDF')
    require(b'\\begin{document}' in data['Report142.tex'] and b'\\end{document}' in data['Report142.tex'],'incomplete article')
    for name,digest in FOUNDATION_SHA256.items():
        require(hashlib.sha256(data['foundation141/'+name]).hexdigest()==digest,'foundation file differs from frozen release: '+name)
    require(data['foundation141/Report141.pdf'].startswith(b'%PDF-'),'foundation is not a PDF')


def verify(root=ROOT):
    data=inventory(root)
    validate_manifest(data[MANIFEST],SCHEMA,PAYLOAD,data)
    validate_payload(data)
    return data


def make_manifest(data):
    return {'schema':SCHEMA,'files':{name:{'bytes':len(data[name]),'sha256':hashlib.sha256(data[name]).hexdigest()} for name in sorted(PAYLOAD)}}


def recompute(data):
    modules={}
    for filename in CODE:
        name=filename[:-3]
        module=types.ModuleType(name)
        module.__file__=str(ROOT/'code'/filename)
        sys.modules[name]=module
        exec(compile(data['code/'+filename],'code/'+filename,'exec'),module.__dict__)
        modules[name]=module
    return {'schema':'report142-exact-v1','status':'PASS',
            'scope':'Exact finite checks; analytic remainder proof is in Report142.',
            'second':modules['second'].run(),'finite':modules['finite'].run()}


def replay(data):
    result=recompute(data)
    require(result==validate_fixtures(data),'recomputed exact results differ from the sealed fixtures')
    return result


def pack(data,destination):
    with create_output_file(destination) as stream:
        with zipfile.ZipFile(stream,'w',compression=zipfile.ZIP_STORED) as archive:
            for name in sorted(data):
                info=zipfile.ZipInfo('report142/'+name,date_time=(1980,1,1,0,0,0))
                info.create_system=3
                info.external_attr=(stat.S_IFREG|0o644)<<16
                info.compress_type=zipfile.ZIP_STORED
                info.flag_bits=0
                archive.writestr(info,data[name])
    return hashlib.sha256(read_regular(destination)).hexdigest()


def invoke(root,args,optimized=False,isolated=True,success=True):
    command=[sys.executable]+(['-I'] if isolated else [])+['-B']+(['-O'] if optimized else [])+[str(root/'verify.py')]+args
    run=subprocess.run(command,stdout=subprocess.PIPE,stderr=subprocess.PIPE,timeout=600)
    require((run.returncode==0)==success,'unexpected subprocess result: '+str(args)+' '+run.stderr.decode(errors='replace'))
    return run



def selftest(data, destination):
    create_output_directory(destination)
    passed=[]
    def copy(label):
        root=destination/label;root.mkdir()
        for directory in sorted(DIRECTORIES): (root/directory).mkdir()
        for name,content in data.items(): (root/name).write_bytes(content)
        return root
    def rehash(root,filename,content):
        (root/filename).write_bytes(content)
        revised=dict(data);revised[filename]=content
        (root/MANIFEST).write_bytes(json_bytes(make_manifest(revised)))
    clean=copy('clean')
    invoke(clean,['check']);invoke(clean,['check'],optimized=True)
    passed.append('normal_and_optimized_integrity')
    changes=[
        ('extra_file',lambda p:(p/'extra').write_text('x')),
        ('extra_directory',lambda p:(p/'extra').mkdir()),
        ('missing_pdf',lambda p:(p/'Report142.pdf').unlink()),
        ('changed_code',lambda p:(p/'code/second.py').write_bytes(data['code/second.py']+b'\n')),
        ('symlink_file',lambda p:(p/'extra').symlink_to(p/'README.md')),
        ('broken_symlink',lambda p:(p/'extra').symlink_to(p/'absent')),
        ('symlink_code_directory',lambda p:((p/'code').rename(p/'moved_code'),(p/'code').symlink_to(p/'moved_code',target_is_directory=True)))]
    if hasattr(os,'mkfifo'):changes.append(('nonregular_fifo',lambda p:os.mkfifo(p/'extra')))
    for label,change in changes:
        p=copy(label);change(p);invoke(p,['check'],optimized=True,success=False);passed.append(label)
    link=destination/'linked_bundle';link.symlink_to(clean,target_is_directory=True)
    invoke(link,['check'],success=False);passed.append('symlink_bundle_ancestor')
    structural=[
        ('boolean_integer',lambda f:f['second'].update(field_radicand=True)),
        ('float_integer',lambda f:f['second'].update(field_radicand=17.0)),
        ('string_integer',lambda f:f['second'].update(field_radicand='17')),
        ('extra_top_key',lambda f:f.update(extra=1)),
        ('extra_nested_key',lambda f:f['second']['diagonal'].update(extra=1)),
        ('missing_nested_key',lambda f:f['second']['diagonal'].pop('b2')),
        ('noncanonical_fraction',lambda f:f['second']['diagonal']['b2'].__setitem__(0,'2/4')),
        ('numeric_fraction',lambda f:f['second']['diagonal']['b2'].__setitem__(0,1)),
        ('boolean_fraction',lambda f:f['second']['diagonal']['b2'].__setitem__(0,True)),
        ('malformed_fraction',lambda f:f['second']['diagonal']['b2'].__setitem__(0,'1/0')),
        ('null_scope',lambda f:f.update(scope=None)),
        ('wrong_field_length',lambda f:f['second']['diagonal']['b2'].append('0')),
        ('nonmonic_denominator',lambda f:f['second']['rational_functions']['r2']['denominator'].__setitem__(-1,'2')),
        ('extra_finite_field',lambda f:f['finite'].update(extra=1)),
        ('boolean_nested_index',lambda f:f['finite']['saddle']['cases'][0].update(r=False)),
        ('extra_nested_finite_field',lambda f:f['finite']['frozen_inverse']['weights'][0].update(extra=1)),
        ('wrong_finite_series_length',lambda f:f['finite']['saddle']['cases'][0]['D'].append('0'))]
    for label,change in structural:
        p=copy(label);f=parse_json(data['checks/fixtures.json']);change(f)
        rehash(p,'checks/fixtures.json',json_bytes(f));invoke(p,['check'],optimized=True,success=False);passed.append(label)
    mathematical=[
        ('false_b2',lambda f:f['second']['diagonal']['b2'].__setitem__(0,'1')),
        ('false_r2',lambda f:f['second']['rational_functions']['r2']['numerator'].__setitem__(0,'1')),
        ('false_gaussian',lambda f:f['second']['rational_functions']['D2']['numerator'].__setitem__(0,'1')),
        ('false_inverse',lambda f:f['second']['diagonal']['lambda2'].__setitem__(0,'1')),
        ('false_top_coefficient',lambda f:f['finite']['top_coefficients']['polynomials'][2]['coefficients'].__setitem__(0,'1')),
        ('false_third_saddle',lambda f:f['finite']['saddle']['cases'][0]['D'].__setitem__(3,'1'))]
    for label,change in mathematical:
        p=copy(label);f=parse_json(data['checks/fixtures.json']);change(f)
        require(f!=parse_json(data['checks/fixtures.json']),'mutation did not apply')
        rehash(p,'checks/fixtures.json',json_bytes(f));invoke(p,['check'])
        output=destination/(label+'-result')
        invoke(p,['replay','--output',str(output)],optimized=True,success=False)
        require(not output.exists(),'failed replay created output');passed.append(label)
    manifest_mutations=[
        ('missing_manifest_record',lambda m:m['files'].pop('README.md')),
        ('extra_manifest_record',lambda m:m['files'].update(extra={'bytes':0,'sha256':'0'*64})),
        ('boolean_manifest_size',lambda m:m['files']['README.md'].update(bytes=True)),
        ('float_manifest_size',lambda m:m['files']['README.md'].update(bytes=1.0)),
        ('wrong_manifest_hash_type',lambda m:m['files']['README.md'].update(sha256=1))]
    for label,change in manifest_mutations:
        p=copy(label);m=parse_json(data[MANIFEST]);change(m)
        (p/MANIFEST).write_bytes(json_bytes(m));invoke(p,['check'],success=False);passed.append(label)
    for filename in (MANIFEST,'checks/fixtures.json'):
        label='duplicate_keys_'+filename.replace('/','_');p=copy(label)
        raw=data[filename].replace(b'{',b'{"schema":"duplicate",',1)
        if filename==MANIFEST:(p/filename).write_bytes(raw)
        else:rehash(p,filename,raw)
        invoke(p,['check'],optimized=True,success=False);passed.append(label)
    for token in (b'NaN',b'Infinity',b'-Infinity',b'1e999',b'17.0'):
        label='bad_numeric_'+token.decode();p=copy(label)
        raw=data['checks/fixtures.json'].replace(b'"field_radicand": 17',b'"field_radicand": '+token,1)
        require(raw!=data['checks/fixtures.json'],'numeric mutation did not apply')
        rehash(p,'checks/fixtures.json',raw);invoke(p,['check'],success=False);passed.append(label)
    p=copy('foundation_bytes_resealed')
    rehash(p,'foundation141/Report141.tex',data['foundation141/Report141.tex']+b'\n')
    invoke(p,['check'],success=False);passed.append('unchanged_foundation_payload_pin')
    p=copy('foundation_pdf_resealed')
    rehash(p,'foundation141/Report141.pdf',data['foundation141/Report141.pdf']+b'\n')
    invoke(p,['check'],success=False);passed.append('unchanged_foundation_pdf_pin')
    entries=('verify.py','code/second.py','code/finite.py')
    for entry in entries:
        p=copy('shadow_import_'+entry.replace('/','_'));marker=destination/('SHADOW_'+entry.replace('/','_'))
        for shadow in ('argparse.py','fractions.py','decimal.py','sympy.py','json.py'):
            (p/Path(entry).parent/shadow).write_text('open('+repr(str(marker))+',"w").write("unsafe")\nraise RuntimeError("shadow imported")\n')
        for optimized in (False,True):
            command=[sys.executable,'-B']+(['-O'] if optimized else [])+[str(p/entry)]
            rejected=subprocess.run(command,stdout=subprocess.PIPE,stderr=subprocess.PIPE,timeout=60)
            require(rejected.returncode!=0 and b'isolated Python (-I) is required' in rejected.stderr,'missing early isolation rejection')
            require(not marker.exists(),'shadow import executed before isolation check')
        invoke(p,['check'],success=False);require(not marker.exists(),'isolated shadow imported')
        passed.append('early_isolation_'+entry)
    existing=destination/'existing';existing.mkdir()
    existing_file=destination/'existing_file';existing_file.write_text('preserve')
    linked=destination/'linked_parent';linked.symlink_to(existing,target_is_directory=True)
    guards=[('existing_directory',existing),('existing_file',existing_file),
            ('inside_bundle',clean/'generated'),('symlink_leaf',linked),
            ('symlink_ancestor',linked/'generated'),('parent_traversal',existing/'..'/'generated'),
            ('missing_parent',destination/'absent'/'generated')]
    for label,path in guards:
        for command in ('replay','pack','build','seal','selftest','reproduce'):
            invoke(clean,[command,'--output',str(path)],success=False)
        passed.append(label+'_all_output_commands')
    require(existing_file.read_text()=='preserve','existing target changed')
    require(not(clean/'generated').exists() and not(existing/'generated').exists(),'preflight wrote output')
    normal,optimized=destination/'normal-replay',destination/'optimized-replay'
    invoke(clean,['replay','--output',str(normal)])
    invoke(clean,['replay','--output',str(optimized)],optimized=True)
    require(read_regular(normal/'replay-result.json')==read_regular(optimized/'replay-result.json'),'normal/-O mismatch')
    passed.append('normal_and_optimized_byte_identical_replay')
    traversal=clean/'..'/'clean'
    invoke(traversal,['check'],success=False)
    invoke(traversal,['replay','--output',str(clean/'traversal-generated')],success=False)
    require(not(clean/'traversal-generated').exists(),'script traversal escaped containment')
    passed.append('script_path_parent_traversal_rejected')
    if os.name=='posix':
        alias=Path('//'+str(clean).lstrip('/'))
        invoke(alias,['replay','--output',str(clean/'alias-generated')],success=False)
        invoke(clean,['replay','--output','//'+str(clean/'alias-generated').lstrip('/')],success=False)
        require(not(clean/'alias-generated').exists(),'double slash escaped containment')
        passed.append('double_leading_slash_containment')
    first=destination/'first.zip';invoke(clean,['pack','--output',str(first)])
    extracted=destination/'extracted';extracted.mkdir()
    with zipfile.ZipFile(first) as archive:
        require(all(n.startswith('report142/') and '..' not in Path(n).parts for n in archive.namelist()),'unsafe generated ZIP')
        archive.extractall(extracted)
    second=destination/'second.zip';invoke(extracted/'report142',['pack','--output',str(second)])
    require(read_regular(first)==read_regular(second),'fresh-extraction repack differs')
    passed.append('fresh_extraction_byte_identical_repack')
    invoke(extracted/'report142',['check'],optimized=True)
    passed.append('fresh_extraction_closed_inventory')
    extracted_result=destination/'extracted-replay'
    invoke(extracted/'report142',['replay','--output',str(extracted_result)])
    require(read_regular(extracted_result/'replay-result.json')==read_regular(normal/'replay-result.json'),'fresh-extraction replay differs')
    passed.append('fresh_extraction_byte_identical_replay')
    require(inventory()==data,'selftest mutated original bundle')
    passed.append('original_bundle_bytes_unchanged')
    result={'status':'PASS','tests':passed}
    with create_output_file(destination/'selftest-result.json') as stream:stream.write(json_bytes(result))
    return result


def build(data,destination):
    create_output_directory(destination)
    with create_output_file(destination/'Report142.tex') as stream: stream.write(data['Report142.tex'])
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
    source=r'\pdfmapfile{+cm.map}\pdfmapfile{+cmextra.map}\pdfmapfile{+symbols.map}\pdfmapfile{+lm.map}\input{Report142.tex}'
    command=['pdflatex','-no-shell-escape','-interaction=nonstopmode','-halt-on-error','-file-line-error',source]
    with create_output_file(destination/'build-console.txt') as log:
        subprocess.run(format_command,cwd=destination,env=environment,stdout=log,stderr=subprocess.STDOUT,check=True,timeout=600)
        for _ in range(2):
            subprocess.run(command,cwd=destination,env=environment,stdout=log,stderr=subprocess.STDOUT,check=True,timeout=600)
    texlog=read_regular(destination/'Report142.log').decode('utf-8',errors='replace')
    for warning in (r'Overfull \hbox',r'Overfull \vbox','undefined references','multiply defined',
                    'undefined citations','Missing character:','Label(s) may have changed'):
        require(warning not in texlog,'TeX QA warning: '+warning)
    pdf=read_regular(destination/'Report142.pdf')
    result={'pdf_sha256':hashlib.sha256(pdf).hexdigest(),'matches_frozen_pdf_bytes':pdf==data['Report142.pdf'],
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
    parser=argparse.ArgumentParser(description='Report142 offline reproducibility companion; isolated Python is mandatory.')
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
        print('PASS: closed inventory, hashes, complete typed fixtures')
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


if __name__ == '__main__':
    try:
        main()
    except (Rejected, ValueError, KeyError, TypeError, OSError, RuntimeError, ArithmeticError,
            subprocess.CalledProcessError, subprocess.TimeoutExpired, ImportError) as error:
        print('REJECTED: ' + str(error), file=sys.stderr)
        sys.exit(1)
