#!/usr/bin/env python3
import sys
if not sys.flags.isolated:
    sys.stderr.write('REJECTED: isolated Python (-I) is required before any imports\n')
    raise SystemExit(2)
sys.dont_write_bytecode = True

"""Read-only Report143 verifier and reproducible external-output workflows."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import stat
import subprocess
import zipfile

ROOT = Path(__file__).absolute().parent
CODE = ('edge.py', 'profile.py', 'check.py', 'selftest.py')
FOUNDATION_SHA256 = {'Report141.tex':'284c974be9274ee926c5e101a12ebc1abe42efc18b99b67d2db2700d2a440824','Report141.pdf':'2cbfc7ceebca3691c23606f37e7c1e6c6fc92e8080788f9d0d54197dc664d807'}
COMPARISON_SHA256 = {'Report142.tex':'787c73394945a7f95dad453397d46b8f8ef60fc12501ed458ab5dad6df8bbf4d','Report142.pdf':'1afdfd78510792f62d24f5abafdefa29418a67531c071cbf678e0a25698dc8ef'}
PAYLOAD = frozenset({'README.md','SOURCES.md','Report143.tex','Report143.pdf','bundle.py','checks/fixtures.json'}) | frozenset('code/'+n for n in CODE) | frozenset('foundation141/'+n for n in FOUNDATION_SHA256) | frozenset('comparison142/'+n for n in COMPARISON_SHA256)
DIRECTORIES = frozenset({'code','checks','foundation141','comparison142'})
MANIFEST = 'manifest.json'
SCHEMA = 'report143-sha256-v1'

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
    require(isinstance(value,str) and value.startswith('/') and not value.startswith('//'),'output must be an absolute path with one leading slash')
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


def pack(data,destination):
    with create_output_file(destination) as stream:
        with zipfile.ZipFile(stream,'w',compression=zipfile.ZIP_STORED) as archive:
            for name in sorted(data):
                info=zipfile.ZipInfo('report143/'+name,date_time=(1980,1,1,0,0,0))
                info.create_system=3
                info.external_attr=(stat.S_IFREG|0o644)<<16
                info.compress_type=zipfile.ZIP_STORED
                info.flag_bits=0
                archive.writestr(info,data[name])
    return hashlib.sha256(read_regular(destination)).hexdigest()


def build(data,destination):
    create_output_directory(destination)
    with create_output_file(destination/'Report143.tex') as stream: stream.write(data['Report143.tex'])
    environment={k:v for k,v in os.environ.items() if k in ('PATH','SYSTEMROOT','WINDIR')}
    environment.update({'SOURCE_DATE_EPOCH':'1790985600','FORCE_SOURCE_DATE':'1','TZ':'UTC','LC_ALL':'C'})
    for variable,folder in [('HOME','home'),('TEXMFHOME','texmf-home'),('TEXMFVAR','texmf-var'),
                            ('TEXMFCONFIG','texmf-config'),('TEXMFCACHE','texmf-cache'),
                            ('XDG_CACHE_HOME','xdg-cache')]:
        p=destination/folder;p.mkdir();environment[variable]=str(p)
    if Path('/usr/share/texlive/texmf-dist').is_dir():
        environment['TEXMF']='{/usr/share/texlive/texmf-dist,/usr/share/texmf}'
    environment['TEXFORMATS']=str(destination)+'//:'
    format_command=['pdftex','-ini','-etex','-no-shell-escape','-interaction=nonstopmode',
                    '-halt-on-error','-jobname=pdflatex','pdflatex.ini']
    source=r'\pdfmapfile{+cm.map}\pdfmapfile{+cmextra.map}\pdfmapfile{+symbols.map}\pdfmapfile{+lm.map}\input{Report143.tex}'
    command=['pdflatex','-no-shell-escape','-interaction=nonstopmode','-halt-on-error','-file-line-error',source]
    with create_output_file(destination/'build-console.txt') as log:
        subprocess.run(format_command,cwd=destination,env=environment,stdout=log,stderr=subprocess.STDOUT,check=True,timeout=600)
        for _ in range(2):
            subprocess.run(command,cwd=destination,env=environment,stdout=log,stderr=subprocess.STDOUT,check=True,timeout=600)
    texlog=read_regular(destination/'Report143.log').decode('utf-8',errors='replace')
    for warning in (r'Overfull \hbox',r'Overfull \vbox','undefined references','multiply defined',
                    'undefined citations','Missing character:','Label(s) may have changed'):
        require(warning not in texlog,'TeX QA warning: '+warning)
    pdf=read_regular(destination/'Report143.pdf')
    result={'pdf_sha256':hashlib.sha256(pdf).hexdigest(),'matches_frozen_pdf_bytes':pdf==data['Report143.pdf'],
            'source_date_epoch':1790985600}
    with create_output_file(destination/'build-result.json') as stream: stream.write(json_bytes(result))
    return result


def fixture_command(command, root=ROOT, optimized=False):
    process=subprocess.run([sys.executable,'-I','-B']+(['-O'] if optimized else [])+
        [str(root/'code/check.py'),command],stdout=subprocess.PIPE,stderr=subprocess.PIPE,timeout=900)
    require(process.returncode==0,'fixture '+command+' failed: '+process.stderr.decode(errors='replace'))
    return process.stdout


def validate_payload(data):
    require(data['Report143.pdf'].startswith(b'%PDF-'),'Report143 is not a PDF')
    require(b'\\begin{document}' in data['Report143.tex'] and b'\\end{document}' in data['Report143.tex'],'incomplete article')
    for directory,pins in [('foundation141',FOUNDATION_SHA256),('comparison142',COMPARISON_SHA256)]:
        for name,digest in pins.items():
            require(hashlib.sha256(data[directory+'/'+name]).hexdigest()==digest,'included source differs from its release: '+directory+'/'+name)
    fixture_command('check')


def verify(root=ROOT):
    data=inventory(root)
    validate_manifest(data[MANIFEST],SCHEMA,PAYLOAD,data)
    validate_payload(data)
    return data


def make_manifest(data):
    return {'schema':SCHEMA,'files':{name:{'bytes':len(data[name]),'sha256':hashlib.sha256(data[name]).hexdigest()} for name in sorted(PAYLOAD)}}


def write_file(path,content):
    with create_output_file(path) as stream:
        stream.write(content)


def selftest(data,destination):
    create_output_directory(destination)
    normal=fixture_command('replay')
    optimized=fixture_command('replay',optimized=True)
    require(normal==optimized,'normal and optimized exact replay output differ')
    write_file(destination/'replay.json',normal)
    write_file(destination/'fixture-selftest.json',fixture_command('selftest'))
    tests=['normal_optimized_replay_equal','fixture_selftest_normal_optimized_children']
    first_hash=pack(data,destination/'first.zip')
    require(first_hash==pack(data,destination/'second.zip'),'deterministic ZIP bytes differ')
    tests.append('deterministic_zip')
    extracted=destination/'extracted'
    extracted.mkdir()
    with zipfile.ZipFile(destination/'first.zip') as archive:
        require(set(archive.namelist())=={'report143/'+name for name in data},'ZIP inventory')
        archive.extractall(extracted)
    extracted_data=inventory(extracted/'report143')
    require(extracted_data==data,'ZIP extracted bytes differ')
    require(first_hash==pack(extracted_data,destination/'repacked.zip'),'ZIP repacking differs')
    tests.append('fresh_extract_repack')
    # Every entrypoint must reject non-isolated startup even under optimization.
    for entry in ['bundle.py']+['code/'+name for name in CODE]:
        for optimization in ([],['-O']):
            result=subprocess.run([sys.executable,'-B']+optimization+[str(ROOT/entry)],stdout=subprocess.PIPE,stderr=subprocess.PIPE,timeout=60)
            require(result.returncode==2 and b'isolated Python' in result.stderr,'missing early isolated startup guard: '+entry)
    tests.append('all_startup_guards_normal_optimized')
    # Preflight must refuse output mutations before doing the expensive work.
    existing=destination/'existing.txt';write_file(existing,b'preserve me')
    symlink=destination/'alias';symlink.symlink_to(destination,target_is_directory=True)
    invalid=[str(ROOT/'forbidden'),str(existing),str(symlink/'forbidden'),
             str(destination/'..'/'forbidden'),'//'+str(destination).lstrip('/')+'/forbidden']
    for output in invalid:
        result=subprocess.run([sys.executable,'-I','-B',str(ROOT/'bundle.py'),'pack','--output',output],stdout=subprocess.PIPE,stderr=subprocess.PIPE,timeout=60)
        require(result.returncode!=0,'unsafe output path accepted: '+output)
    require(read_regular(existing)==b'preserve me' and not (destination/'forbidden').exists(),'preflight modified a refused output')
    tests.append('output_containment_and_existing_preservation')
    require(inventory()==data,'selftest changed original bundle')
    result={'status':'PASS','tests':tests,'archive_sha256':first_hash}
    write_file(destination/'selftest-result.json',json_bytes(result))
    return result


def reproduce(data,destination):
    create_output_directory(destination)
    tests=selftest(data,destination/'selftest')
    first=build(data,destination/'build-one')
    second=build(data,destination/'build-two')
    require(first['pdf_sha256']==second['pdf_sha256'],'two fresh PDF builds differ')
    require(first['matches_frozen_pdf_bytes'] and second['matches_frozen_pdf_bytes'],'fresh builds differ from frozen PDF; inspect build-result.json for toolchain/source mismatch')
    result={'status':'PASS','selftest_count':len(tests['tests']),'fresh_builds_identical':True,
            'fresh_build_matches_frozen_pdf':True,'fresh_pdf_sha256':first['pdf_sha256'],
            'archive_sha256':tests['archive_sha256']}
    write_file(destination/'reproduction-result.json',json_bytes(result))
    return result


def main():
    parser=argparse.ArgumentParser(description='Report143 offline bundle workflows; isolated Python is mandatory.')
    sub=parser.add_subparsers(dest='command',required=True)
    sub.add_parser('check')
    for name in ('replay','selftest','pack','build','seal','reproduce'):
        p=sub.add_parser(name);p.add_argument('--output',required=True,help='absent external absolute path with an existing real parent')
    args=parser.parse_args()
    output=preflight_output(args.output) if hasattr(args,'output') else None
    if args.command=='seal':
        data=inventory(sealing=True);validate_payload(data)
        write_file(output,json_bytes(make_manifest(data)))
        print(json.dumps({'status':'PASS','external_manifest':str(output)},sort_keys=True));return
    data=verify()
    if args.command=='check':
        result={'status':'PASS','files':len(data),'closed_inventory_and_hashes':True,'unchanged_prior_reports':True}
    elif args.command=='replay':
        content=fixture_command('replay');create_output_directory(output)
        write_file(output/'replay-result.json',content)
        result={'status':'PASS','result':str(output/'replay-result.json')}
    elif args.command=='pack':
        result={'status':'PASS','archive_sha256':pack(data,output)}
    elif args.command=='build':result=build(data,output)
    elif args.command=='selftest':result=selftest(data,output)
    elif args.command=='reproduce':result=reproduce(data,output)
    print(json.dumps(result,sort_keys=True))


if __name__=='__main__':
    try:
        main()
    except (Rejected,ValueError,KeyError,TypeError,OSError,RuntimeError,ArithmeticError,
            subprocess.CalledProcessError,subprocess.TimeoutExpired,ImportError) as error:
        print('REJECTED: '+str(error),file=sys.stderr)
        sys.exit(1)
