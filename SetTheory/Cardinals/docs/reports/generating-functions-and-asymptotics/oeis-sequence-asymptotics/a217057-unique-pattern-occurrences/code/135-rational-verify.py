#!/usr/bin/env python3
"""Read-only verification, external builds, and deterministic packaging for Report135."""
import sys
sys.dont_write_bytecode = True
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
BASE = frozenset({'README.md','SOURCES.md','Report135.tex','Report135.pdf',
                  'refinements.py','second_refinements.py','kernel_sympy.py','unitary_checks.py',
                  'exact_data.json','second_exact_data.json','verify.py'})
COMPANION = frozenset({'README.md','Report134.tex','Report134.pdf','certificate.py',
                      'independent.py','fixtures.json','verify.py','manifest.json'})
PAYLOAD = BASE | frozenset('companion134/'+n for n in COMPANION)
MANIFEST = 'manifest.json'
SCHEMA = 'report135-sha256-v1'
COMPANION_MANIFEST_HASH = '87bd951e61b6a51fd8f8ec534b0bf64545535ddd7498f75013ef6656e08ed94b'
VALUES = [0,0,0,0,1,12,102,770,5545,39220,276144,1948212,13817680,98679990,
          710108396,5150076076,37641647410,277202062666,2056218941678,
          15358296210724,115469557503753]

class Rejected(Exception):
    pass


def require(condition, message):
    if not condition:
        raise Rejected(message)


def no_duplicate_keys(pairs):
    result = {}
    for key, value in pairs:
        require(key not in result, "duplicate JSON key: " + key)
        result[key] = value
    return result


def parse_json(data):
    return json.loads(data.decode("utf-8"), object_pairs_hook=no_duplicate_keys)


def json_bytes(value):
    return (json.dumps(value, sort_keys=True, indent=2, ensure_ascii=True)+"\n").encode("ascii")


def lexical_absolute(value):
    path = Path(value)
    require(".." not in path.parts, "parent traversal is not permitted")
    return path if path.is_absolute() else Path.cwd()/path


def check_ancestors(path, leaf_may_be_absent=False):
    """Check lexical components, without resolve() hiding a symlink."""
    current = Path(path.anchor)
    for index, part in enumerate(path.parts[1:]):
        current /= part
        leaf = index == len(path.parts)-2
        try:
            mode = current.lstat().st_mode
        except FileNotFoundError:
            require(leaf and leaf_may_be_absent, "missing ancestor: " + str(current))
            return
        require(not stat.S_ISLNK(mode), "symlink component refused: " + str(current))
        if not leaf:
            require(stat.S_ISDIR(mode), "non-directory ancestor: " + str(current))


def read_regular(path):
    flags = os.O_RDONLY | getattr(os, "O_NOFOLLOW", 0) | getattr(os, "O_NONBLOCK", 0)
    descriptor = os.open(path, flags)
    with os.fdopen(descriptor, "rb") as stream:
        require(stat.S_ISREG(os.fstat(stream.fileno()).st_mode), "nonregular file refused")
        return stream.read()



def preflight_output(value):
    path = lexical_absolute(value)
    check_ancestors(path, leaf_may_be_absent=True)
    require(not path.exists() and not path.is_symlink(), "output already exists: " + str(path))
    require(ROOT != path and ROOT not in path.parents, "output must be outside the bundle")
    require(path.parent.is_dir(), "output parent must already exist")
    return path


def create_output_directory(path):
    # The final mkdir is exclusive. Recheck ancestors immediately before creating.
    check_ancestors(path, leaf_may_be_absent=True)
    os.mkdir(path, mode=0o700)


def create_output_file(path):
    check_ancestors(path, leaf_may_be_absent=True)
    flags = os.O_WRONLY | os.O_CREAT | os.O_EXCL | getattr(os, "O_NOFOLLOW", 0)
    return os.fdopen(os.open(path, flags, 0o600), "wb")


def load_verified(data, name):
    module = types.ModuleType(name[:-3])
    exec(compile(data[name], name, "exec"), module.__dict__)
    return module



def inventory(root=ROOT, sealing=False):
    check_ancestors(root)
    require(root.is_dir(), 'bundle root is not a directory')
    found={}
    for directory,subdirs,files in os.walk(root,followlinks=False):
        relative=Path(directory).relative_to(root)
        for name in subdirs:
            p=Path(directory)/name
            require(p.relative_to(root).as_posix()=='companion134' and
                    stat.S_ISDIR(p.lstat().st_mode), 'unexpected directory or symlink: '+str(p))
        for name in files:
            p=Path(directory)/name
            require(stat.S_ISREG(p.lstat().st_mode),'nonregular file: '+str(p))
            found[p.relative_to(root).as_posix()]=read_regular(p)
    expected=PAYLOAD|{MANIFEST}
    if sealing and MANIFEST not in found: expected=PAYLOAD
    require(set(found)==expected,'closed inventory mismatch; missing='+str(sorted(expected-set(found)))+
            '; extra='+str(sorted(set(found)-expected)))
    return found


def validate_exact_data(data):
    f=parse_json(data['exact_data.json'])
    require(type(f) is dict and set(f)=={'schema','u_source','u_0_through_20','partial_indices','finite_partials','partial_scope'},'exact data keys')
    require(f['schema']=='report135-exact-data-v1','exact data schema')
    require(f['u_source']=='Report134 exact tableau/gluing formula; n=0..15 also frozen OEIS A217057 fixture','exact data provenance')
    require(f['partial_scope']=='Exact finite R/S partial sums. No certified infinite S/beta value or error bound.','partial scope')
    require(type(f['u_0_through_20']) is list and len(f['u_0_through_20'])==21,'count list')
    require(all(type(v) is int and v==w for v,w in zip(f['u_0_through_20'],VALUES)),'count values/types')
    require(type(f['partial_indices']) is list and f['partial_indices']==[0,1,2,5,10,20] and
            all(type(v) is int for v in f['partial_indices']),'partial indices')
    require(type(f['finite_partials']) is dict and set(f['finite_partials'])==set(map(str,f['partial_indices'])),'partial rows')
    for t in f['partial_indices']:
        row=f['finite_partials'][str(t)]
        require(type(row) is dict and set(row)=={'t','R_term','S_term','R_partial','S_partial','beta_partial_not_certified'},'partial row keys')
        require(type(row['t']) is int and row['t']==t,'partial t')
        for name in set(row)-{'t'}:
            v=row[name]
            require(type(v) is str and str(Fraction(v))==v,'canonical rational string: '+name)
    return f


def validate_second_data(data):
    f=parse_json(data['second_exact_data.json'])
    require(type(f) is dict and set(f)=={'schema','partial_indices','finite_partials','scope'},'second data keys')
    require(f['schema']=='report135-second-exact-data-v1','second data schema')
    require(f['scope']=='Exact finite signed S2 partial sums; no certified infinite S2 or delta value, sign, tail, or error bound.','second data scope')
    require(type(f['partial_indices']) is list and f['partial_indices']==[0,1,2,5,10,20] and
            all(type(v) is int for v in f['partial_indices']),'second partial indices')
    require(type(f['finite_partials']) is dict and set(f['finite_partials'])==set(map(str,f['partial_indices'])),'second partial rows')
    for t in f['partial_indices']:
        row=f['finite_partials'][str(t)]
        require(type(row) is dict and set(row)=={'t','S2_term','S2_partial'},'second partial row keys')
        require(type(row['t']) is int and row['t']==t,'second partial t')
        for name in ('S2_term','S2_partial'):
            v=row[name]
            require(type(v) is str and str(Fraction(v))==v,'canonical second rational string')
    return f


def validate_companion(data):
    raw=data['companion134/manifest.json']
    require(hashlib.sha256(raw).hexdigest()==COMPANION_MANIFEST_HASH,'changed Report134 original manifest')
    m=parse_json(raw)
    require(m['schema']=='report134-sha256-v1' and set(m['files'])==COMPANION-{'manifest.json'},'original manifest schema')
    for name,record in m['files'].items():
        payload=data['companion134/'+name]
        require(record=={'bytes':len(payload),'sha256':hashlib.sha256(payload).hexdigest()},'changed Report134 companion: '+name)


def validate_payload(data):
    validate_companion(data)
    validate_exact_data(data)
    validate_second_data(data)
    require(data['Report135.pdf'].startswith(b'%PDF-'),'Report135 is not a PDF')
    require(b'\\begin{document}' in data['Report135.tex'] and b'\\end{document}' in data['Report135.tex'],'incomplete article TeX')


def verify(root=ROOT):
    data=inventory(root)
    manifest=parse_json(data[MANIFEST])
    require(type(manifest) is dict and set(manifest)=={'schema','files'},'manifest keys')
    require(manifest['schema']==SCHEMA,'manifest schema')
    require(type(manifest['files']) is dict and set(manifest['files'])==PAYLOAD,'manifest records')
    for name in sorted(PAYLOAD):
        rec=manifest['files'][name]
        require(type(rec) is dict and set(rec)=={'bytes','sha256'},'manifest file record')
        require(type(rec['bytes']) is int and rec['bytes']==len(data[name]),'size mismatch: '+name)
        require(type(rec['sha256']) is str and rec['sha256']==hashlib.sha256(data[name]).hexdigest(),'SHA256 mismatch: '+name)
    validate_payload(data)
    return data


def make_manifest(data):
    return {'schema':SCHEMA,'files':{n:{'bytes':len(data[n]),'sha256':hashlib.sha256(data[n]).hexdigest()} for n in sorted(PAYLOAD)}}


def pack(data,destination):
    with create_output_file(destination) as stream:
        with zipfile.ZipFile(stream,'w',compression=zipfile.ZIP_STORED) as archive:
            for name in sorted(data):
                info=zipfile.ZipInfo('Report135/'+name,date_time=(1980,1,1,0,0,0))
                info.create_system=3
                info.external_attr=(stat.S_IFREG|0o644)<<16
                info.compress_type=zipfile.ZIP_STORED
                info.flag_bits=0
                archive.writestr(info,data[name])
    print('Packed SHA256 '+hashlib.sha256(read_regular(destination)).hexdigest())


def replay(data):
    primary=load_verified(data,'companion134/certificate.py')
    independent=load_verified(data,'companion134/independent.py')
    refinement=load_verified(data,'refinements.py')
    result=refinement.replay(primary,independent,validate_exact_data(data))
    second=load_verified(data,'second_refinements.py').run(refinement,primary)
    second_fixture=validate_second_data(data)
    for t in second_fixture['partial_indices']:
        require(second['finite_partials'][t]==second_fixture['finite_partials'][str(t)],'exact S2 partial fixture')
    result['second_correction_and_logarithm']=second
    result['unitary_and_boundary_algebra']=load_verified(data,'unitary_checks.py').run()
    result['unchanged_Report134_manifest_sha256']=COMPANION_MANIFEST_HASH
    return result


def selftest(data,destination):
    create_output_directory(destination)
    passed=[]
    def copy(label):
        p=destination/label;p.mkdir()
        (p/'companion134').mkdir()
        for name,raw in data.items(): (p/name).write_bytes(raw)
        return p
    def invoke(root,args,success=True):
        run=subprocess.run([sys.executable,'-I','-B','-O',str(root/'verify.py')]+args,
                           stdout=subprocess.PIPE,stderr=subprocess.PIPE)
        require((run.returncode==0)==success,'selftest unexpected result: '+str(args)+' '+run.stderr.decode(errors='replace'))
    clean=copy('clean');invoke(clean,['check']);passed.append('clean_optimized_python')
    changes=[('extra_file',lambda p:(p/'extra').write_text('x')),
             ('extra_directory',lambda p:(p/'extra').mkdir()),
             ('missing_pdf',lambda p:(p/'Report135.pdf').unlink()),
             ('changed_data',lambda p:(p/'exact_data.json').write_bytes(data['exact_data.json']+b' ')),
             ('changed_companion',lambda p:(p/'companion134/README.md').write_bytes(b'changed')),
             ('symlink_file',lambda p:(p/'extra').symlink_to(p/'README.md')),
             ('broken_symlink',lambda p:(p/'extra').symlink_to(p/'absent'))]
    if hasattr(os,'mkfifo'): changes.append(('nonregular_fifo',lambda p:os.mkfifo(p/'extra')))
    for label,change in changes:
        p=copy(label);change(p);invoke(p,['check'],False);passed.append(label)
    link=destination/'linked_bundle';link.symlink_to(clean,target_is_directory=True)
    invoke(link,['check'],False);passed.append('symlink_bundle_ancestor')
    for label,change in [('boolean_count',lambda f:f['u_0_through_20'].__setitem__(0,False)),
                         ('float_count',lambda f:f['u_0_through_20'].__setitem__(4,1.0)),
                         ('extra_data_key',lambda f:f.update(extra=1)),
                         ('float_partial_t',lambda f:f['finite_partials']['0'].update(t=0.0)),
                         ('noncanonical_fraction',lambda f:f['finite_partials']['0'].update(R_term='70/648'))]:
        p=copy(label);f=parse_json(data['exact_data.json']);change(f)
        (p/'exact_data.json').write_bytes(json_bytes(f))
        revised=dict(data);revised['exact_data.json']=read_regular(p/'exact_data.json')
        (p/MANIFEST).write_bytes(json_bytes(make_manifest(revised)))
        invoke(p,['check'],False);passed.append(label)
    for label,change in [('second_float_t',lambda f:f['finite_partials']['0'].update(t=0.0)),
                         ('second_extra_key',lambda f:f.update(extra=1)),
                         ('second_noncanonical_fraction',lambda f:f['finite_partials']['0'].update(S2_term='-2390/5184'))]:
        p=copy(label);f=parse_json(data['second_exact_data.json']);change(f)
        (p/'second_exact_data.json').write_bytes(json_bytes(f))
        revised=dict(data);revised['second_exact_data.json']=read_regular(p/'second_exact_data.json')
        (p/MANIFEST).write_bytes(json_bytes(make_manifest(revised)))
        invoke(p,['check'],False);passed.append(label)
    # Rehashed, well-typed but mathematically false fixtures must fail replay.
    for label,filename,column in [('wrong_S_rational','exact_data.json','S_partial'),
                                  ('wrong_S2_rational','second_exact_data.json','S2_partial')]:
        p=copy(label);f=parse_json(data[filename]);f['finite_partials']['0'][column]='999'
        (p/filename).write_bytes(json_bytes(f))
        revised=dict(data);revised[filename]=read_regular(p/filename)
        (p/MANIFEST).write_bytes(json_bytes(make_manifest(revised)))
        invoke(p,['replay','--output',str(destination/(label+'-result'))],False)
        passed.append(label+'_rejected_under_O')
    for label,change in [('missing_manifest_record',lambda m:m['files'].pop('README.md')),
                         ('extra_manifest_record',lambda m:m['files'].update(extra={'bytes':0,'sha256':'0'*64})),
                         ('boolean_manifest_size',lambda m:m['files']['README.md'].update(bytes=True))]:
        p=copy(label);m=parse_json(data[MANIFEST]);change(m);(p/MANIFEST).write_bytes(json_bytes(m))
        invoke(p,['check'],False);passed.append(label)
    p=copy('duplicate_json_key');(p/MANIFEST).write_bytes(data[MANIFEST].replace(b'{',b'{"schema":"duplicate",',1))
    invoke(p,['check'],False);passed.append('duplicate_json_key')
    # Resealing cannot bless a changed original companion.
    p=copy('reseal_changed_companion');(p/'companion134/README.md').write_text('changed')
    invoke(p,['seal','--output',str(destination/'must_not_exist.json')],False)
    require(not (destination/'must_not_exist.json').exists(),'failed seal created output')
    passed.append('reseal_changed_companion')
    existing=destination/'existing';existing.mkdir()
    existing_file=destination/'existing_file';existing_file.write_text('preserve')
    link=destination/'linked_parent';link.symlink_to(existing,target_is_directory=True)
    paths=[('existing_directory',existing),('existing_file',existing_file),('inside_bundle',clean/'generated'),
           ('symlink_leaf',link),('symlink_ancestor',link/'generated'),('parent_traversal',existing/'..'/'generated')]
    for label,p in paths:
        invoke(clean,['replay','--output',str(p)],False);passed.append(label)
    require(existing_file.read_text()=='preserve','existing output changed')
    require(not (clean/'generated').exists() and not (existing/'generated').exists(),'preflight created files')
    first=destination/'first.zip';invoke(clean,['pack','--output',str(first)])
    extracted=destination/'extracted';extracted.mkdir()
    with zipfile.ZipFile(first) as archive: archive.extractall(extracted)
    second=destination/'second.zip';invoke(extracted/'Report135',['pack','--output',str(second)])
    require(read_regular(first)==read_regular(second),'repack byte mismatch')
    passed.append('fresh_extraction_byte_identical_repack')
    with create_output_file(destination/'selftest-result.json') as stream:
        stream.write(json_bytes({'status':'PASS','tests':passed}))
    print('Selftest PASS: '+str(len(passed))+' tests')

def build(data, destination):
    # Frozen sources are copied externally; TeX never writes into the bundle.
    create_output_directory(destination)
    tex = destination/"Report135.tex"
    with create_output_file(tex) as stream:
        stream.write(data["Report135.tex"])
    environment = os.environ.copy()
    environment.update({"SOURCE_DATE_EPOCH":"1790899200", "FORCE_SOURCE_DATE":"1", "TZ":"UTC", "LC_ALL":"C"})
    for variable, folder in (("TEXMFVAR", "texmf-var"), ("TEXMFCONFIG", "texmf-config"),
                             ("TEXMFCACHE", "texmf-cache"), ("XDG_CACHE_HOME", "xdg-cache")):
        directory = destination/folder
        directory.mkdir()
        environment[variable] = str(directory)
    if Path("/usr/share/texlive/texmf-dist").is_dir():
        # Search real system trees even when TeX's filename database is absent.
        environment["TEXMF"] = "{/usr/share/texlive/texmf-dist,/usr/share/texmf}"
    environment["TEXFORMATS"] = str(destination)+"//:"
    format_command = ["pdftex", "-ini", "-etex", "-no-shell-escape", "-interaction=nonstopmode",
                      "-halt-on-error", "-jobname=pdflatex", "pdflatex.ini"]
    source = r"\pdfmapfile{+cm.map}\pdfmapfile{+cmextra.map}\pdfmapfile{+symbols.map}\pdfmapfile{+lm.map}\input{Report135.tex}"
    command = ["pdflatex", "-no-shell-escape", "-interaction=nonstopmode", "-halt-on-error", "-file-line-error", source]
    with create_output_file(destination/"build-console.txt") as log:
        subprocess.run(format_command, cwd=destination, env=environment, stdout=log, stderr=subprocess.STDOUT, check=True, timeout=180)
        for _ in range(2):
            subprocess.run(command, cwd=destination, env=environment, stdout=log, stderr=subprocess.STDOUT, check=True, timeout=180)
    tex_log = read_regular(destination/"Report135.log").decode("utf-8", errors="replace")
    for warning in (r"Overfull \hbox", r"Overfull \vbox", "undefined references", "multiply defined",
                    "undefined citations", "Missing character:", "Label(s) may have changed"):
        require(warning not in tex_log, "TeX QA warning: " + warning)
    result = read_regular(destination/"Report135.pdf")
    with create_output_file(destination/"build-result.json") as stream:
        stream.write(json_bytes({"pdf_sha256":hashlib.sha256(result).hexdigest(),
                                 "matches_frozen_pdf_bytes":result == data["Report135.pdf"],
                                 "source_date_epoch":1790899200}))
    print("Built PDF externally; see build-result.json for byte comparison")



def main():
    parser=argparse.ArgumentParser(description=__doc__)
    sub=parser.add_subparsers(dest='command',required=True)
    sub.add_parser('check')
    for name in ('replay','selftest','pack','build','seal'):
        command=sub.add_parser(name)
        command.add_argument('--output',required=True,help='new external output path, existing parent')
    args=parser.parse_args()
    output=preflight_output(args.output) if hasattr(args,'output') else None
    if args.command=='seal':
        data=inventory(sealing=True);validate_payload(data)
        with create_output_file(output) as stream:stream.write(json_bytes(make_manifest(data)))
        print('Wrote external manifest; review and install manually: '+str(output))
        return
    data=verify()
    if args.command=='check':print('PASS: closed inventory, hashes, unchanged companion, typed exact data')
    elif args.command=='replay':
        create_output_directory(output)
        result=replay(data)
        with create_output_file(output/'replay-result.json') as stream:stream.write(json_bytes(result))
        print('PASS: '+str(output/'replay-result.json'))
    elif args.command=='pack':pack(data,output)
    elif args.command=='build':build(data,output)
    elif args.command=='selftest':selftest(data,output)


if __name__=='__main__':
    try:main()
    except (Rejected,ValueError,KeyError,TypeError,OSError,subprocess.CalledProcessError,subprocess.TimeoutExpired) as error:
        print('REJECTED: '+str(error),file=sys.stderr);sys.exit(1)
