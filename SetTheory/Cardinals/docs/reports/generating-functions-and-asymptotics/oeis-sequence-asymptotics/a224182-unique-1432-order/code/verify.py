#!/usr/bin/env python3
import sys
if not sys.flags.isolated:
    sys.stderr.write('REJECTED: isolated Python (-I) is required before any imports\n')
    raise SystemExit(2)
sys.dont_write_bytecode = True

"""Read-only Report139 verifier and reproducible external-output workflows."""
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
CODE = ('primary.py', 'coordinate.py', 'replay.py')
PAYLOAD = frozenset({'README.md', 'SOURCES.md', 'Report139.tex', 'Report139.pdf',
                     'verify.py', 'checks/fixtures.json'}) | frozenset('code/' + n for n in CODE)
DIRECTORIES = frozenset({'code', 'checks'})
MANIFEST = 'manifest.json'
SCHEMA = 'report139-sha256-v1'

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


def common_rows(result, label):
    rows = result['by_size']
    require(type(rows) is list and len(rows) == 5, label + ' rows')
    for n, row in zip(range(4, 9), rows):
        keys(row, {'n', 'permutations', 'unique1432', 'marked_images', 'avoiders',
                   'fixed_minima_skeletons', 'skeleton_sha256', 'minima_distribution'}, label + ' row')
        integer(row['n'], label + ' n', n)
        for field in ('permutations', 'unique1432', 'marked_images', 'avoiders', 'fixed_minima_skeletons'):
            integer(row[field], label + ' ' + field)
            require(row[field] >= 0, label + ' nonnegative count')
        digest(row['skeleton_sha256'], label)
        ints(row['minima_distribution'], n, label + ' minima distribution')
    rows = result['inverse_certificate']
    require(type(rows) is list and len(rows) == 5, label + ' inverse rows')
    for n, row in zip(range(4, 9), rows):
        keys(row, {'n', 'multiple_cores_passing_regions', 'splits_still_containing1432'}, label + ' inverse row')
        integer(row['n'], label + ' inverse n', n)
        for field in ('multiple_cores_passing_regions', 'splits_still_containing1432'):
            integer(row[field], label + ' ' + field)
            require(row[field] >= 0, label + ' nonnegative inverse count')


def validate_fixtures(data):
    f = parse_json(data['checks/fixtures.json'])
    keys(f, {'schema', 'status', 'primary', 'independent', 'obstruction_certificate', 'scope'}, 'fixture')
    require(f['schema'] == 'report139-exact-v1' and f['status'] == 'PASS', 'fixture schema/status')
    text(f['scope'], 'scope')
    p, q = f['primary'], f['independent']
    keys(p, {'by_size', 'inverse_certificate', 'pattern_counter_checks', 'inflation_cases',
             'collision', 'board', 'sole_support', 'constants'}, 'primary')
    keys(q, {'by_size', 'inverse_certificate', 'restriction_commutations',
             'small_avoider_center_checks', 'eligible_centers_by_size'}, 'independent')
    common_rows(p, 'primary'); common_rows(q, 'independent')
    for field in ('pattern_counter_checks', 'inflation_cases'):
        integer(p[field], field); require(p[field] >= 0, field + ' range')
    for field in ('restriction_commutations', 'small_avoider_center_checks'):
        integer(q[field], field); require(q[field] >= 0, field + ' range')
    rows = q['eligible_centers_by_size']
    require(type(rows) is list and len(rows) == 3, 'eligible-center rows')
    for n, row in zip(range(6, 9), rows):
        keys(row, {'output_size', 'eligible_centers'}, 'eligible-center row')
        integer(row['output_size'], 'output size', n)
        integer(row['eligible_centers'], 'eligible centers')
        require(row['eligible_centers'] >= 0, 'eligible count range')
    c = p['collision']
    keys(c, {'sources', 'image', 'zero_based_marks'}, 'collision')
    require(type(c['sources']) is list and len(c['sources']) == 2, 'collision sources')
    for source in c['sources']: permutation(source, 9, 'collision source')
    permutation(c['image'], 11, 'collision image')
    ints(c['zero_based_marks'], 2, 'collision marks')
    require(all(mark < 11 for mark in c['zero_based_marks']), 'collision mark range')
    c = p['board']; keys(c, {'thresholds', 'one123', 'one321'}, 'board')
    ints(c['thresholds'], 6, 'board thresholds', 1)
    require(all(v <= 6 for v in c['thresholds']), 'board threshold range')
    for field in ('one123', 'one321'): integer(c[field], 'board ' + field)
    c = p['sole_support']
    keys(c, {'avoider', 'zero_based_mark', 'source', 'occurrences'}, 'sole support')
    permutation(c['avoider'], 7, 'sole-support avoider')
    permutation(c['source'], 5, 'sole-support source')
    integer(c['zero_based_mark'], 'sole-support mark')
    require(0 <= c['zero_based_mark'] < 7, 'sole-support mark range')
    integer(c['occurrences'], 'sole-support occurrence count')
    c = p['constants']
    keys(c, {'lower_ratio', 'upper_ratio', 'constant_quotient', 'unrounded_width'}, 'constants')
    for field in c: rational(c[field], field)
    records = f['obstruction_certificate']
    require(type(records) is list and len(records) == 2074, 'complete obstruction record count/type')
    seen = set()
    for row in records:
        keys(row, {'n', 'source', 'core', 'split', 'witness'}, 'obstruction record')
        n = row['n']; integer(n, 'obstruction n'); require(4 <= n <= 8, 'obstruction size range')
        permutation(row['source'], n, 'obstruction source')
        permutation(row['split'], n + 2, 'obstruction split')
        for field, bound in (('core', n), ('witness', n + 2)):
            seq = row[field]; ints(seq, 4, field)
            require(seq == sorted(set(seq)) and seq[-1] < bound, field + ' increasing index range')
        identifier = (tuple(row['source']), tuple(row['core']))
        require(identifier not in seen, 'duplicate obstruction record')
        seen.add(identifier)
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
    require(data['Report139.pdf'].startswith(b'%PDF-'), 'Report139 is not a PDF')
    require(b'\\begin{document}' in data['Report139.tex'] and b'\\end{document}' in data['Report139.tex'], 'incomplete article')


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
                info=zipfile.ZipInfo('Report139/'+name,date_time=(1980,1,1,0,0,0))
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
        ('missing_pdf', lambda p: (p / 'Report139.pdf').unlink()),
        ('changed_code', lambda p: (p / 'code/primary.py').write_bytes(data['code/primary.py'] + b'\n')),
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
        ('boolean_integer', lambda f: f['primary'].update(inflation_cases=True)),
        ('float_integer', lambda f: f['independent'].update(restriction_commutations=75419.0)),
        ('string_integer', lambda f: f['primary'].update(pattern_counter_checks='864')),
        ('extra_top_key', lambda f: f.update(extra=1)),
        ('extra_nested_key', lambda f: f['obstruction_certificate'][0].update(extra=1)),
        ('missing_nested_key', lambda f: f['primary']['board'].pop('one321')),
        ('noncanonical_fraction', lambda f: f['primary']['constants'].update(unrounded_width='22/4')),
        ('numeric_fraction', lambda f: f['primary']['constants'].update(unrounded_width=5.5)),
        ('null_scope', lambda f: f.update(scope=None)),
        ('wrong_row_length', lambda f: f['primary']['by_size'][0]['minima_distribution'].append(0)),
        ('missing_obstruction', lambda f: f['obstruction_certificate'].pop()),
        ('duplicate_obstruction', lambda f: f['obstruction_certificate'].__setitem__(0, f['obstruction_certificate'][1])),
        ('bool_permutation_entry', lambda f: f['obstruction_certificate'][0]['source'].__setitem__(0, True)),
        ('float_witness_entry', lambda f: f['obstruction_certificate'][0]['witness'].__setitem__(0, 0.0)),
        ('extra_independent_key', lambda f: f['independent']['eligible_centers_by_size'][0].update(extra=1))]
    for label, change in structural:
        p = copy(label); f = parse_json(data['checks/fixtures.json']); change(f)
        rehash(p, 'checks/fixtures.json', json_bytes(f))
        invoke(p, ['check'], optimized=True, success=False); passed.append(label)
    mathematical = [
        ('false_unique_count', lambda f: f['primary']['by_size'][0].update(unique1432=2)),
        ('false_skeleton_digest', lambda f: f['independent']['by_size'][0].update(skeleton_sha256='0'*64)),
        ('false_inverse_count', lambda f: f['primary']['inverse_certificate'][2].update(multiple_cores_passing_regions=7)),
        ('false_width', lambda f: f['primary']['constants'].update(unrounded_width='6')),
        ('false_eligible_count', lambda f: f['independent']['eligible_centers_by_size'][0].update(eligible_centers=2)),
        ('false_obstruction_witness', lambda f: f['obstruction_certificate'][0].update(witness=[0, 1, 2, 3]))]
    for label, change in mathematical:
        p = copy(label); f = parse_json(data['checks/fixtures.json']); change(f)
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
    for token in (b'NaN', b'Infinity', b'-Infinity'):
        label = 'nonfinite_' + token.decode(); p = copy(label)
        raw = data['checks/fixtures.json'].replace(b'75419', token, 1)
        require(raw != data['checks/fixtures.json'], 'nonfinite mutation did not apply')
        rehash(p, 'checks/fixtures.json', raw); invoke(p, ['check'], success=False); passed.append(label)
    p = copy('shadow_import'); marker = destination / 'SHADOW_EXECUTED'
    (p / 'argparse.py').write_text('open(' + repr(str(marker)) + ',"w").write("unsafe")\nraise RuntimeError("shadow imported")\n')
    for optimized in (False, True):
        rejected = invoke(p, ['check'], optimized=optimized, isolated=False, success=False)
        require(b'isolated Python (-I) is required' in rejected.stderr, 'missing early isolation rejection')
        require(not marker.exists(), 'shadow import executed before isolation check')
    invoke(p, ['check'], success=False); require(not marker.exists(), 'isolated shadow imported')
    passed.append('unsealed_shadow_import_blocked_before_imports')
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
        require(all(n.startswith('Report139/') and '..' not in Path(n).parts for n in archive.namelist()), 'unsafe generated ZIP')
        archive.extractall(extracted)
    second = destination / 'second.zip'; invoke(extracted / 'Report139', ['pack', '--output', str(second)])
    require(read_regular(first) == read_regular(second), 'fresh-extraction repack differs')
    passed.append('fresh_extraction_byte_identical_repack')
    result = {'status': 'PASS', 'tests': passed}
    with create_output_file(destination / 'selftest-result.json') as stream: stream.write(json_bytes(result))
    return result


def build(data,destination):
    create_output_directory(destination)
    with create_output_file(destination/'Report139.tex') as stream: stream.write(data['Report139.tex'])
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
    source=r'\pdfmapfile{+cm.map}\pdfmapfile{+cmextra.map}\pdfmapfile{+symbols.map}\pdfmapfile{+lm.map}\input{Report139.tex}'
    command=['pdflatex','-no-shell-escape','-interaction=nonstopmode','-halt-on-error','-file-line-error',source]
    with create_output_file(destination/'build-console.txt') as log:
        subprocess.run(format_command,cwd=destination,env=environment,stdout=log,stderr=subprocess.STDOUT,check=True,timeout=600)
        for _ in range(2):
            subprocess.run(command,cwd=destination,env=environment,stdout=log,stderr=subprocess.STDOUT,check=True,timeout=600)
    texlog=read_regular(destination/'Report139.log').decode('utf-8',errors='replace')
    for warning in (r'Overfull \hbox',r'Overfull \vbox','undefined references','multiply defined',
                    'undefined citations','Missing character:','Label(s) may have changed'):
        require(warning not in texlog,'TeX QA warning: '+warning)
    pdf=read_regular(destination/'Report139.pdf')
    result={'pdf_sha256':hashlib.sha256(pdf).hexdigest(),'matches_frozen_pdf_bytes':pdf==data['Report139.pdf'],
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
    parser=argparse.ArgumentParser(description='Report139 offline reproducibility companion; isolated Python is mandatory.')
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
    except (Rejected, ValueError, KeyError, TypeError, OSError, RuntimeError,
            subprocess.CalledProcessError, subprocess.TimeoutExpired) as error:
        print('REJECTED: ' + str(error), file=sys.stderr)
        sys.exit(1)
