#!/usr/bin/env python3
import sys
if not sys.flags.isolated:
    sys.stderr.write('REJECTED: isolated Python (-I) is required before any imports\n')
    raise SystemExit(2)
sys.dont_write_bytecode = True

"""Read-only Report141 verifier and reproducible external-output workflows."""
import argparse
from decimal import Decimal
import re
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
CODE = ('exact.py', 'algebra.py', 'replay.py')
PAYLOAD = frozenset({'README.md', 'SOURCES.md', 'Report141.tex', 'Report141.pdf',
                     'verify.py', 'checks/fixtures.json'}) | frozenset('code/' + n for n in CODE)
DIRECTORIES = frozenset({'code', 'checks'})
MANIFEST = 'manifest.json'
SCHEMA = 'report141-sha256-v1'

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


def integer_list(value,expected,label):
    require(type(value) is list and len(value)==len(expected),label+' list length/type')
    for x,y in zip(value,expected):
        integer(x,label,y)


def text(value,label):
    require(type(value) is str and bool(value),label+' must be a nonempty string')


def ints(value, length, label, minimum=0):
    require(type(value) is list and len(value) == length, label + ' length/type')
    for x in value:
        integer(x, label)
        require(x >= minimum, label + ' range')


def permutation(value, size, label):
    ints(value, size, label, 1)
    require(sorted(value) == list(range(1, size + 1)), label + ' is not a permutation')


def digest(value, label):
    require(type(value) is str and len(value) == 64 and all(c in '0123456789abcdef' for c in value), label + ' digest')


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


def decimal_text(value,label):
    require(type(value) is str,label+' decimal string type')
    require(re.fullmatch(r'-?[0-9]\.[0-9]{45}E[+-][0-9]+',value) is not None,label+' decimal notation')
    require(Decimal(value).is_finite(),label+' finite decimal')


def validate_fixtures(data):
    f=parse_json(data['checks/fixtures.json'])
    keys(f,{'schema','status','scope','exact','algebra','diagnostics'},'fixture')
    require(f['schema']=='report141-exact-v1' and f['status']=='PASS','fixture schema/status')
    text(f['scope'],'scope')
    e=f['exact'];keys(e,{'bounds','counts','polynomials','prefixes','exhaustive_paths','newton','operators','source_diagonal'},'exact')
    expected_bounds={'polynomial_order':20,'prefix_length':24,'exhaustive_semilength':7,'operator_order':8}
    keys(e['bounds'],expected_bounds,'bounds')
    for k,v in expected_bounds.items():integer(e['bounds'][k],k,v)
    count_names={'catalan_path_count','coefficientwise_bound','completed_peak_prefix_recurrence','exhaustive_paths',
      'hypergeometric_product','auxiliary_differential_equation','logarithmic_derivative_convolution','monic_polynomial','newton_large_power_identity',
      'newton_operator_difference','newton_operator_on_polynomial','newton_p_difference','newton_positive_bound',
      'newton_z_difference','ordinary_positivity','public_source_diagonal','weighted_prefix_power_identity'}
    keys(e['counts'],count_names,'counts')
    for k,v in e['counts'].items():integer(v,k);require(v>0,k+' positive')
    list_length(e['polynomials'],21,'polynomials')
    for n,row in enumerate(e['polynomials']):
        keys(row,{'N','P','Z'},'polynomial');integer(row['N'],'N',n)
        rational_list(row['P'],'P',n+1);rational_list(row['Z'],'Z',n+1)
    list_length(e['prefixes'],325,'prefixes')
    pairs=[(ell,y) for ell in range(25) for y in range(ell+1)]
    for row,(ell,y) in zip(e['prefixes'],pairs):
        keys(row,{'length','height','polynomial'},'prefix')
        integer(row['length'],'length',ell);integer(row['height'],'height',y)
        rational_list(row['polynomial'],'prefix polynomial')
        require(len(row['polynomial'])<=1+ell//2,'prefix polynomial degree bound')
    list_length(e['exhaustive_paths'],8,'exhaustive paths')
    for n,row in enumerate(e['exhaustive_paths']):
        keys(row,{'n','paths','polynomial'},'path');integer(row['n'],'path n',n)
        integer(row['paths'],'paths');require(row['paths']>0,'positive path count')
        rational_list(row['polynomial'],'path polynomial',n+1)
    list_length(e['newton'],231,'newton')
    pairs=[(n,m) for m in range(21) for n in range(m,21)]
    for row,(n,m) in zip(e['newton'],pairs):
        keys(row,{'N','m','P','Q','coefficient_fh'},'newton row')
        integer(row['N'],'newton N',n);integer(row['m'],'newton m',m)
        for k in ('P','Q','coefficient_fh'):rational(row[k],k)
    list_length(e['operators'],90,'operators')
    pairs=[(ell,r,m) for ell in range(9) for r in range(ell+1) for m in (ell,ell+3)]
    for row,(ell,r,m) in zip(e['operators'],pairs):
        keys(row,{'ell','r','m','coefficient'},'operator')
        integer(row['ell'],'ell',ell);integer(row['r'],'r',r);integer(row['m'],'m',m)
        rational(row['coefficient'],'operator coefficient')
    ints(e['source_diagonal'],11,'source diagonal',1)
    a=f['algebra'];keys(a,{'field_radicand','constants','rational_functions','diagonal_correction','inverse','shifted_saddles','operator_coefficients'},'algebra')
    integer(a['field_radicand'],'field radicand',17)
    keys(a['constants'],{'s','t','B','d','pi_cubed_C_squared','b1'},'constants')
    for k,v in a['constants'].items():quadratic(v,k)
    keys(a['rational_functions'],{'E','c1','r1','scaled_L1','scaled_L2','scaled_K','scaled_J','source'},'rational functions')
    for k,v in a['rational_functions'].items():rational_function(v,k)
    correction=a['diagonal_correction'];keys(correction,{'factorial','saddle','ratio','total'},'correction')
    rational(correction['factorial'],'factorial correction')
    for k in ('saddle','ratio','total'):quadratic(correction[k],k)
    keys(a['inverse'],{'c1','cancelled_linear','cubic_inverse_log','cubic_inverse_log_squared'},'inverse')
    for k,v in a['inverse'].items():quadratic(v,k)
    list_length(a['shifted_saddles'],15,'shifted saddles')
    pairs=[(ell,r) for ell in range(5) for r in range(ell+1)]
    for row,(ell,r) in zip(a['shifted_saddles'],pairs):
        keys(row,{'ell','r','coefficient','kappa'},'shifted saddle')
        integer(row['ell'],'ell',ell);integer(row['r'],'r',r)
        rational_function(row['coefficient'],'saddle coefficient');rational_function(row['kappa'],'kappa')
    list_length(a['operator_coefficients'],90,'operator coefficients')
    pairs=[(ell,r) for ell in range(1,13) for r in range(ell+1)]
    for row,(ell,r) in zip(a['operator_coefficients'],pairs):
        keys(row,{'ell','r','polynomial','leading','next'},'operator polynomial')
        integer(row['ell'],'ell',ell);integer(row['r'],'r',r)
        rational_list(row['polynomial'],'operator polynomial',ell-r+1)
        rational(row['leading'],'leading');rational(row['next'],'next')
    d=f['diagnostics'];keys(d,{'label','decimal_precision','display_digits_after_decimal','constants','source_terms','inverse_example'},'diagnostics')
    text(d['label'],'diagnostics label');integer(d['decimal_precision'],'precision',85)
    integer(d['display_digits_after_decimal'],'display digits',45)
    keys(d['constants'],{'d','C','b1'},'decimal constants')
    for k,v in d['constants'].items():decimal_text(v,k)
    list_length(d['source_terms'],4,'source diagnostic terms')
    for row,n in zip(d['source_terms'],(40,80,160,290)):
        keys(row,{'n','a','leading_ratio','scaled_first_error','scaled_second_residual'},'source diagnostic')
        integer(row['n'],'source n',n);integer(row['a'],'source a');require(row['a']>0,'source positive')
        for k in ('leading_ratio','scaled_first_error','scaled_second_residual'):decimal_text(row[k],k)
    inv=d['inverse_example'];keys(inv,{'threshold_power_of_ten','x0','x1','smooth_residual'},'inverse diagnostic')
    integer(inv['threshold_power_of_ten'],'threshold exponent',1000)
    for k in ('x0','x1','smooth_residual'):decimal_text(inv[k],k)
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
    require(data['Report141.pdf'].startswith(b'%PDF-'), 'Report141 is not a PDF')
    require(b'\\begin{document}' in data['Report141.tex'] and b'\\end{document}' in data['Report141.tex'], 'incomplete article')


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
                info=zipfile.ZipInfo('Report141/'+name,date_time=(1980,1,1,0,0,0))
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
    passed = []
    def copy(label):
        root = destination / label
        root.mkdir()
        for directory in sorted(DIRECTORIES): (root / directory).mkdir()
        for name, content in data.items(): (root / name).write_bytes(content)
        return root
    def rehash(root, filename, content):
        (root / filename).write_bytes(content)
        revised = dict(data); revised[filename] = content
        (root / MANIFEST).write_bytes(json_bytes(make_manifest(revised)))
    clean = copy('clean')
    invoke(clean, ['check']); invoke(clean, ['check'], optimized=True)
    passed.append('normal_and_optimized_integrity')
    changes = [
        ('extra_file', lambda p: (p / 'extra').write_text('x')),
        ('extra_directory', lambda p: (p / 'extra').mkdir()),
        ('missing_pdf', lambda p: (p / 'Report141.pdf').unlink()),
        ('changed_code', lambda p: (p / 'code/exact.py').write_bytes(data['code/exact.py'] + b'\n')),
        ('symlink_file', lambda p: (p / 'extra').symlink_to(p / 'README.md')),
        ('broken_symlink', lambda p: (p / 'extra').symlink_to(p / 'absent')),
        ('symlink_code_directory', lambda p: ((p / 'code').rename(p / 'moved_code'),
                                             (p / 'code').symlink_to(p / 'moved_code', target_is_directory=True)))]
    if hasattr(os, 'mkfifo'): changes.append(('nonregular_fifo', lambda p: os.mkfifo(p / 'extra')))
    for label, change in changes:
        p = copy(label); change(p); invoke(p, ['check'], optimized=True, success=False); passed.append(label)
    link = destination / 'linked_bundle'; link.symlink_to(clean, target_is_directory=True)
    invoke(link, ['check'], success=False); passed.append('symlink_bundle_ancestor')
    structural = [
        ('boolean_integer', lambda f: f['exact']['counts'].update(exhaustive_paths=True)),
        ('float_integer', lambda f: f['exact']['counts'].update(exhaustive_paths=8.0)),
        ('string_integer', lambda f: f['exact']['counts'].update(exhaustive_paths='8')),
        ('boolean_nested_index', lambda f: f['exact']['prefixes'][0].update(height=False)),
        ('float_nested_index', lambda f: f['algebra']['shifted_saddles'][0].update(r=0.0)),
        ('extra_top_key', lambda f: f.update(extra=1)),
        ('extra_nested_key', lambda f: f['exact']['newton'][0].update(extra=1)),
        ('missing_nested_key', lambda f: f['algebra']['inverse'].pop('c1')),
        ('noncanonical_fraction', lambda f: f['algebra']['constants']['b1'].__setitem__(0,'2/4')),
        ('numeric_fraction', lambda f: f['exact']['prefixes'][0]['polynomial'].__setitem__(0,1)),
        ('boolean_fraction', lambda f: f['algebra']['constants']['s'].__setitem__(0,True)),
        ('float_fraction', lambda f: f['algebra']['constants']['s'].__setitem__(0,0.125)),
        ('null_scope', lambda f: f.update(scope=None)),
        ('wrong_row_length', lambda f: f['exact']['polynomials'][0]['P'].append('0')),
        ('missing_prefix', lambda f: f['exact']['prefixes'].pop()),
        ('duplicate_prefix', lambda f: f['exact']['prefixes'].__setitem__(0, f['exact']['prefixes'][1])),
        ('bool_source_term', lambda f: f['diagnostics']['source_terms'][0].update(a=True)),
        ('float_source_term', lambda f: f['diagnostics']['source_terms'][0].update(a=1.0)),
        ('nonnumeric_decimal', lambda f: f['diagnostics']['constants'].update(C='NaN')),
        ('numeric_decimal', lambda f: f['diagnostics']['constants'].update(C=0.28)),
        ('nonmonic_denominator', lambda f: f['algebra']['rational_functions']['E']['denominator'].__setitem__(-1,'2'))]
    for label, change in structural:
        p = copy(label); f = parse_json(data['checks/fixtures.json']); change(f)
        rehash(p, 'checks/fixtures.json', json_bytes(f))
        invoke(p, ['check'], optimized=True, success=False); passed.append(label)
    mathematical = [
        ('false_riccati_coefficient', lambda f: f['exact']['polynomials'][2]['P'].__setitem__(0,'999')),
        ('false_direct_prefix', lambda f: f['exact']['prefixes'][10]['polynomial'].__setitem__(0,'999')),
        ('false_newton_coefficient', lambda f: f['exact']['newton'][0].update(P='2')),
        ('false_source_diagonal', lambda f: f['exact']['source_diagonal'].__setitem__(1,7)),
        ('false_operator', lambda f: f['exact']['operators'][0].update(coefficient='2')),
        ('false_b1', lambda f: f['algebra']['constants']['b1'].__setitem__(0,'1')),
        ('false_correction_source', lambda f: f['algebra']['rational_functions']['source']['numerator'].__setitem__(0,'1')),
        ('false_inverse', lambda f: f['algebra']['inverse']['c1'].__setitem__(0,'1')),
        ('false_gaussian', lambda f: f['algebra']['rational_functions']['c1']['numerator'].__setitem__(0,'1')),
        ('false_diagnostic', lambda f: f['diagnostics']['constants'].update(C='1.'+'0'*45+'E+0')),
        ('false_public_bfile', lambda f: f['diagnostics']['source_terms'][0].update(a=123))]
    for label, change in mathematical:
        p = copy(label); f = parse_json(data['checks/fixtures.json']); change(f)
        require(f != parse_json(data['checks/fixtures.json']), 'mathematical mutation did not apply: ' + label)
        rehash(p, 'checks/fixtures.json', json_bytes(f))
        invoke(p, ['check'])
        target = destination / (label + '-result')
        invoke(p, ['replay', '--output', str(target)], optimized=True, success=False)
        require(not target.exists(), 'failed replay created output'); passed.append(label)
    manifest_mutations = [
        ('missing_manifest_record', lambda m: m['files'].pop('README.md')),
        ('extra_manifest_record', lambda m: m['files'].update(extra={'bytes': 0, 'sha256': '0'*64})),
        ('boolean_manifest_size', lambda m: m['files']['README.md'].update(bytes=True)),
        ('float_manifest_size', lambda m: m['files']['README.md'].update(bytes=float(m['files']['README.md']['bytes']))),
        ('wrong_manifest_hash_type', lambda m: m['files']['README.md'].update(sha256=1))]
    for label, change in manifest_mutations:
        p = copy(label); m = parse_json(data[MANIFEST]); change(m)
        (p / MANIFEST).write_bytes(json_bytes(m)); invoke(p, ['check'], success=False); passed.append(label)
    for filename in (MANIFEST, 'checks/fixtures.json'):
        label = 'duplicate_keys_' + filename.replace('/', '_')
        p = copy(label); raw = data[filename].replace(b'{', b'{"schema":"duplicate",', 1)
        if filename == MANIFEST: (p / filename).write_bytes(raw)
        else: rehash(p, filename, raw)
        invoke(p, ['check'], optimized=True, success=False); passed.append(label)
    for token in (b'NaN', b'Infinity', b'-Infinity', b'1e999', b'8.0'):
        label = 'nonfinite_' + token.decode(); p = copy(label)
        raw = data['checks/fixtures.json'].replace(b'"catalan_path_count": 8', b'"catalan_path_count": ' + token, 1)
        require(raw != data['checks/fixtures.json'], 'nonfinite mutation did not apply')
        rehash(p, 'checks/fixtures.json', raw); invoke(p, ['check'], success=False); passed.append(label)
    for entry in ('verify.py','code/exact.py','code/algebra.py','code/replay.py'):
        p = copy('shadow_import_' + entry.replace('/','_')); marker = destination / ('SHADOW_' + entry.replace('/','_'))
        for shadow in ('argparse.py','fractions.py','decimal.py'):
            (p / Path(entry).parent / shadow).write_text('open(' + repr(str(marker)) + ',"w").write("unsafe")\nraise RuntimeError("shadow imported")\n')
        for optimized in (False,True):
            command=[sys.executable,'-B']+(['-O'] if optimized else [])+[str(p/entry)]
            rejected=subprocess.run(command,stdout=subprocess.PIPE,stderr=subprocess.PIPE,timeout=60)
            require(rejected.returncode != 0 and b'isolated Python (-I) is required' in rejected.stderr,'missing early isolation rejection')
            require(not marker.exists(),'shadow import executed before isolation check')
        invoke(p,['check'],success=False);require(not marker.exists(),'isolated shadow imported')
        passed.append('early_isolation_' + entry)
    existing = destination / 'existing'; existing.mkdir()
    existing_file = destination / 'existing_file'; existing_file.write_text('preserve')
    linked = destination / 'linked_parent'; linked.symlink_to(existing, target_is_directory=True)
    guards = [('existing_directory', existing), ('existing_file', existing_file),
              ('inside_bundle', clean / 'generated'), ('symlink_leaf', linked),
              ('symlink_ancestor', linked / 'generated'), ('parent_traversal', existing / '..' / 'generated'),
              ('missing_parent', destination / 'absent' / 'generated')]
    for label, path in guards:
        for command in ('replay', 'pack', 'build', 'seal', 'selftest', 'reproduce'):
            invoke(clean, [command, '--output', str(path)], success=False)
        passed.append(label + '_all_output_commands')
    require(existing_file.read_text() == 'preserve', 'existing target changed')
    require(not (clean / 'generated').exists() and not (existing / 'generated').exists(), 'preflight wrote output')
    normal, optimized = destination / 'normal-replay', destination / 'optimized-replay'
    invoke(clean, ['replay', '--output', str(normal)])
    invoke(clean, ['replay', '--output', str(optimized)], optimized=True)
    require(read_regular(normal / 'replay-result.json') == read_regular(optimized / 'replay-result.json'), 'normal/-O mismatch')
    passed.append('normal_and_optimized_byte_identical_replay')
    traversal = clean / '..' / 'clean'
    invoke(traversal, ['check'], success=False)
    invoke(traversal, ['replay', '--output', str(clean / 'traversal-generated')], success=False)
    require(not (clean / 'traversal-generated').exists(), 'script traversal escaped containment')
    passed.append('script_path_parent_traversal_rejected')
    if os.name == 'posix':
        alias = Path('//' + str(clean).lstrip('/'))
        invoke(alias, ['replay', '--output', str(clean / 'alias-generated')], success=False)
        invoke(clean, ['replay', '--output', '//' + str(clean / 'alias-generated').lstrip('/')], success=False)
        require(not (clean / 'alias-generated').exists(), 'double slash escaped containment')
        passed.append('double_leading_slash_containment')
    first = destination / 'first.zip'; invoke(clean, ['pack', '--output', str(first)])
    extracted = destination / 'extracted'; extracted.mkdir()
    with zipfile.ZipFile(first) as archive:
        require(all(n.startswith('Report141/') and '..' not in Path(n).parts for n in archive.namelist()), 'unsafe generated ZIP')
        archive.extractall(extracted)
    second = destination / 'second.zip'; invoke(extracted / 'Report141', ['pack', '--output', str(second)])
    require(read_regular(first) == read_regular(second), 'fresh-extraction repack differs')
    passed.append('fresh_extraction_byte_identical_repack')
    require(inventory()==data,'selftest mutated original bundle')
    passed.append('original_bundle_bytes_unchanged')
    result = {'status': 'PASS', 'tests': passed}
    with create_output_file(destination / 'selftest-result.json') as stream: stream.write(json_bytes(result))
    return result



def build(data,destination):
    create_output_directory(destination)
    with create_output_file(destination/'Report141.tex') as stream: stream.write(data['Report141.tex'])
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
    source=r'\pdfmapfile{+cm.map}\pdfmapfile{+cmextra.map}\pdfmapfile{+symbols.map}\pdfmapfile{+lm.map}\input{Report141.tex}'
    command=['pdflatex','-no-shell-escape','-interaction=nonstopmode','-halt-on-error','-file-line-error',source]
    with create_output_file(destination/'build-console.txt') as log:
        subprocess.run(format_command,cwd=destination,env=environment,stdout=log,stderr=subprocess.STDOUT,check=True,timeout=600)
        for _ in range(2):
            subprocess.run(command,cwd=destination,env=environment,stdout=log,stderr=subprocess.STDOUT,check=True,timeout=600)
    texlog=read_regular(destination/'Report141.log').decode('utf-8',errors='replace')
    for warning in (r'Overfull \hbox',r'Overfull \vbox','undefined references','multiply defined',
                    'undefined citations','Missing character:','Label(s) may have changed'):
        require(warning not in texlog,'TeX QA warning: '+warning)
    pdf=read_regular(destination/'Report141.pdf')
    result={'pdf_sha256':hashlib.sha256(pdf).hexdigest(),'matches_frozen_pdf_bytes':pdf==data['Report141.pdf'],
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
    parser=argparse.ArgumentParser(description='Report141 offline reproducibility companion; isolated Python is mandatory.')
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
            subprocess.CalledProcessError, subprocess.TimeoutExpired) as error:
        print('REJECTED: ' + str(error), file=sys.stderr)
        sys.exit(1)
