#!/usr/bin/env python3
"""Independent release-only tests; no supplied selftest or mathematical code is executed."""
import copy, hashlib, json, os, pathlib, runpy, shutil, stat, struct, subprocess, sys, zipfile, zlib
P=pathlib.Path
SOURCE=P('/workspace/shared/report66-bounded-certificates-counting-release-20261004')
BASE=P('/workspace/shared/report66-release-tools-independent-review-20261004')
WORK=BASE/'test-work-v2'
WORK.mkdir()
EXPECTED={'release66.py':'6a86de64d934a9bf13a3780edf7ef92942d72a860146b442ad89949606360344','build_report66.py':'e12e30e6fd2503466fccac8212f28b4ee4814fa78a96a42ab08e53948c826b0e','selftest66.py':'9c92ed278635ebdb780f7d193aff5be8faf9aa71425e56d7784a600b04ee6f3b'}
def hashb(b): return hashlib.sha256(b).hexdigest()
def enc(o): return (json.dumps(o,indent=2,sort_keys=True)+'\n').encode()
def save(p,o): p.write_bytes(enc(o))
def scan(root):
    result={}
    for d,dirs,files in os.walk(root,followlinks=False):
        for p in [P(d),*[P(d)/f for f in files],*[P(d)/n for n in dirs if (P(d)/n).is_symlink()]]:
            s=p.lstat(); row={'mode':stat.S_IMODE(s.st_mode),'kind':stat.S_IFMT(s.st_mode),'mtime_ns':s.st_mtime_ns,'nlink':s.st_nlink}
            if stat.S_ISREG(s.st_mode): row.update(bytes=s.st_size,sha256=hashb(p.read_bytes()))
            if stat.S_ISLNK(s.st_mode): row['target']=os.readlink(p)
            result[p.relative_to(root).as_posix()]=row
    return result
initial_tools={name:hashb((SOURCE/'tools'/name).read_bytes()) for name in EXPECTED}
assert initial_tools==EXPECTED
frozen_roots=[SOURCE/'science',SOURCE/'audits',P('/workspace/shared/three-witness-independent-audit-20261004'),P('/workspace/shared/three-witness-bounded-halting-20261004'),P('/workspace/shared/native-gap-counting-continuation-20261004'),P('/workspace/shared/native-gap-counting-independent-review-20261004'),P('/workspace/shared/native-gap-halting-continuation-20261004'),P('/workspace/shared/report64-five-signal-branching-release-20261004')]
originals={str(p):scan(p) for p in frozen_roots}
save(BASE/'ORIGINALS_BEFORE.json',originals)
fixture=WORK/'fixture';fixture.mkdir()
for n in ('science','audits'): shutil.copytree(SOURCE/n,fixture/n,copy_function=shutil.copy2)
shutil.copy2(SOURCE/'INPUT_PINS.json',fixture/'INPUT_PINS.json')
(fixture/'tools').mkdir();(fixture/'manuscript').mkdir()
for n in EXPECTED: shutil.copy2(SOURCE/'tools'/n,fixture/'tools'/n)
(fixture/'README.md').write_text('Independent synthetic release fixture; contains no mathematical claims.\n')
modules=('bounded.tex','gaps.tex','counting.tex','scope.tex')
for i,n in enumerate(modules): (fixture/'manuscript'/n).write_text('Independent section '+str(i+1)+'.\\par\n')
tex=r'''\documentclass{article}
\pdfinfoomitdate=1
\pdftrailerid{}
\IfFileExists{Report66.aux}{}{\usepackage{calc}}
\begin{document}
Independent release review, deterministic typesetting fixture.\par
'''+''.join('\\input{manuscript/'+n+'}\n' for n in modules)+r'\end{document}'+'\n'
(fixture/'manuscript/Report66.tex').write_text(tex)
results=[]; observations=[]; count=0

def mark(name,detail=None):
    results.append({'name':name,'status':'PASS',**({'detail':detail} if detail is not None else {})})
    print('PASS',name,flush=True)

def run(name,tool,args,root=fixture,ok=True,env=None,absent=None,flags=True):
    global count
    count+=1;before=scan(root)
    c=[sys.executable]+(['-I','-S','-B'] if flags else ['-B'])+[str(root/'tools'/tool),*map(str,args)]
    r=subprocess.run(c,cwd=WORK,env=env,stdin=subprocess.DEVNULL,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,timeout=420)
    (BASE/('v2-'+str(count).zfill(3)+'-'+name+'.log')).write_bytes(r.stdout)
    if (r.returncode==0)!=ok: raise AssertionError(name+': '+r.stdout.decode(errors='replace')[-5000:])
    if absent is not None: assert not os.path.lexists(absent),(name,'created rejected output')
    assert scan(root)==before,(name,'source changed')
    mark(name,{'exit':r.returncode,'source_preserved':True})
    return r

def clone(name):
    dst=WORK/('clone-'+name);shutil.copytree(fixture,dst,copy_function=shutil.copy2);return dst

def mutate_reject(name,fn,cmd='check-inputs',args=()):
    dst=clone(name);fn(dst);run(name,'release66.py',[cmd,*args],root=dst,ok=False)

run('authenticate-inert-inputs','release66.py',['check-inputs'])
prepared=WORK/'prepared';run('prepare-synthetic-flatten','release66.py',['prepare','--output-dir',prepared])
for n,t in [('Report66.tex','Report66.tex'),('MANUSCRIPT_PINS.json','manuscript/MANUSCRIPT_PINS.json')]:shutil.copy2(prepared/n,fixture/t)
pin=hashb((prepared/'MANUSCRIPT_PINS.json').read_bytes())
assert (fixture/'Report66.tex').read_bytes()==tex.encode().replace(b'\\input{manuscript/bounded.tex}\n',(fixture/'manuscript/bounded.tex').read_bytes()).replace(b'\\input{manuscript/gaps.tex}\n',(fixture/'manuscript/gaps.tex').read_bytes()).replace(b'\\input{manuscript/counting.tex}\n',(fixture/'manuscript/counting.tex').read_bytes()).replace(b'\\input{manuscript/scope.tex}\n',(fixture/'manuscript/scope.tex').read_bytes())
mark('independent-flat-byte-oracle')
bootstrap=WORK/'bootstrap';run('synthetic-bootstrap','build_report66.py',['--pins-sha',pin,'--bootstrap','--output-dir',bootstrap])
b=json.loads((bootstrap/'BUILD_RECEIPT.json').read_bytes());assert b['status']=='BOOTSTRAP' and b['dependency_lock_verified'] is False
mark('bootstrap-not-preflight-verified')
lockdata=(bootstrap/'BUILD_DEPENDENCIES.json').read_bytes();lock=json.loads(lockdata);lockpin=hashb(lockdata)
shutil.copy2(bootstrap/'BUILD_DEPENDENCIES.json',fixture/'tools/BUILD_DEPENDENCIES_LOCK.json');shutil.copy2(bootstrap/'Report66.pdf',fixture/'Report66.pdf')
common=['--pins-sha',pin,'--dependency-lock-sha',lockpin,'--require-packaged-match']
run('synthetic-locked-equal','build_report66.py',[*common,'--output-dir',WORK/'locked'])
assert (WORK/'locked/Report66.pdf').read_bytes()==(bootstrap/'Report66.pdf').read_bytes()
union=json.loads((bootstrap/'RECORDER_INPUT_UNION.json').read_bytes());assert [p['pass'] for p in union['passes']]==['format','compile-1','compile-2','compile-3']
sets=[set(p['system_inputs']) for p in union['passes']];first_only=sets[1]-sets[2]-sets[3]
early=[p for p in first_only if p.endswith('/calc.sty')];assert len(early)==1 and early[0] in union['union'] and early[0] in lock['system_inputs']
assert set.union(*sets)<=set(union['union']);mark('all-pass-union-first-only-calc',early[0])
for key in ('TMPDIR','TEMP','TMP'):
    env=dict(os.environ)
    for v in ('TMPDIR','TEMP','TMP'):env.pop(v,None)
    env[key]=str(fixture/'science/bounded-certificates')
    run('hostile-'+key,'build_report66.py',[*common,'--output-dir',WORK/('hostile-'+key)],env=env)
# Environment poisoning is independently checked beyond temporary-directory variables.
env=dict(os.environ,TEXINPUTS=str(fixture/'science')+'//',TEXMFOUTPUT=str(fixture/'audits'),PYTHONPATH=str(fixture/'science'),TEXFORMATS=str(fixture/'science'),BASH_ENV=str(fixture/'science/static_algebra.py'))
run('hostile-tex-python-environment','build_report66.py',[*common,'--output-dir',WORK/'hostile-env'],env=env)
for name,args in [('bad-manuscript-pin',['--pins-sha','0'*64,'--bootstrap']),('bad-lock-pin',['--pins-sha',pin,'--dependency-lock-sha','0'*64]),('uppercase-pin',['--pins-sha',pin.upper(),'--bootstrap']),('invalid-dpi',[*common,'--render-dpi',201])]:
    out=WORK/(name+'-out');run(name,'build_report66.py',[*args,'--output-dir',out],ok=False,absent=out)
run('reject-unisolated-python','release66.py',['check-inputs'],ok=False,flags=False)
for name,target in [('relative-output','relative-child'),('dot-alias',str(WORK)+'/./alias'),('dotdot-alias',str(WORK)+'/../alias'),('double-slash',str(WORK)+'//alias'),('leading-double-slash','/'+str(WORK/'alias')),('trailing-slash',str(WORK/'alias')+'/'),('inside-release',str(fixture/'child')),('inside-protected',str(frozen_roots[2]/'child')),('existing-dir',str(prepared)),('existing-file',str(fixture/'README.md'))]:
    run('reject-'+name,'release66.py',['prepare','--output-dir',target],ok=False)
link=WORK/'linked-parent';link.symlink_to(WORK,target_is_directory=True)
run('reject-linked-output-parent','release66.py',['prepare','--output-dir',link/'child'],ok=False)
rootlink=WORK/'linked-root';rootlink.symlink_to(fixture,target_is_directory=True)
run('reject-linked-source-parent','release66.py',['check-inputs'],root=rootlink,ok=False)
dangling=WORK/'dangling-output';dangling.symlink_to(WORK/'absent')
run('reject-dangling-output','release66.py',['prepare','--output-dir',dangling],ok=False)
for scope in ('science','audits'):
    def mode(d,scope=scope):p=d/scope;p.chmod(stat.S_IMODE(p.stat().st_mode)^0o010)
    def mtime(d,scope=scope):p=d/scope;s=p.stat();os.utime(p,ns=(s.st_atime_ns,s.st_mtime_ns+1))
    mutate_reject('reject-'+scope+'-root-mode',mode);mutate_reject('reject-'+scope+'-root-ns-mtime',mtime)
fp='science/bounded-certificates/PROOF.md';dp='science/bounded-certificates'
def file_mode(d):p=d/fp;p.chmod(stat.S_IMODE(p.stat().st_mode)^0o100)
def file_time(d):p=d/fp;s=p.stat();os.utime(p,ns=(s.st_atime_ns,s.st_mtime_ns+1))
def dir_mode(d):p=d/dp;p.chmod(stat.S_IMODE(p.stat().st_mode)^0o010)
def dir_time(d):p=d/dp;s=p.stat();os.utime(p,ns=(s.st_atime_ns,s.st_mtime_ns+1))
for name,fn in [('frozen-bytes',lambda d:(d/fp).write_bytes((d/fp).read_bytes()+b'X')),('frozen-file-mode',file_mode),('frozen-file-mtime',file_time),('frozen-dir-mode',dir_mode),('frozen-dir-mtime',dir_time),('missing-frozen-file',lambda d:(d/fp).unlink()),('extra-frozen-file',lambda d:(d/dp/'unexpected').write_text('x')),('empty-frozen-dir',lambda d:(d/dp/'empty').mkdir()),('hardlink',lambda d:os.link(d/'README.md',d/'readme-link')),('symlink',lambda d:(d/'symlink').symlink_to(d/'README.md')),('fifo',lambda d:os.mkfifo(d/'fifo')),('tampered-input-map',lambda d:(d/'INPUT_PINS.json').write_bytes((d/'INPUT_PINS.json').read_bytes()+b' '))]: mutate_reject('reject-'+name,fn)
for name,change,preflight in [('omitted-early-input',lambda x:x['system_inputs'].pop(early[0]),False),('wrong-system-digest',lambda x:x['system_inputs'][early[0]].update(sha256='0'*64),True),('wrong-executable-digest',lambda x:x['executables']['pdftex'].update(sha256='0'*64),True),('unsafe-system-path',lambda x:x['system_inputs'].update({'/tmp/not-a-system-input':{'bytes':0,'sha256':'0'*64}}),True)]:
    d=clone(name);changed=copy.deepcopy(lock);change(changed);data=enc(changed);(d/'tools/BUILD_DEPENDENCIES_LOCK.json').write_bytes(data);out=WORK/(name+'-out')
    run('reject-'+name,'build_report66.py',['--pins-sha',pin,'--dependency-lock-sha',hashb(data),'--output-dir',out],root=d,ok=False,absent=out if preflight else None)
    if not preflight:assert json.loads((out/'BUILD_FAILURE.json').read_bytes())['release_preserved'] is True
# Inspect-loaded release/build modules only. Their main entry points are not invoked by runpy.
h=runpy.run_path(str(fixture/'tools/release66.py'),run_name='independent_review_release')
g=runpy.run_path(str(fixture/'tools/build_report66.py'),run_name='independent_review_builder')
def refuses(name,fn):
    try:fn()
    except (ValueError,OSError,KeyError,TypeError,zlib.error):mark(name)
    else:raise AssertionError(name+' unexpectedly accepted')
row={'mode':0o644,'mtime_ns':123,'bytes':0,'sha256':hashb(b'')};dr={'mode':0o755,'mtime_ns':123}
minimal={'format':h['FORMAT'],'files':{'a/b.txt':row},'directories':{'a':dr}}
assert h['validate_manifest'](minimal)==minimal;mark('valid-minimal-manifest')
for bad in ('../x','/x','./x','a//x','a/../x','a\\x','a/\nx','a/.','a/'):
    m={'format':h['FORMAT'],'files':{bad:row},'directories':{}}
    refuses('reject-manifest-path-'+repr(bad),lambda m=m:h['validate_manifest'](m))
for name,mut in [('missing-directory',lambda m:m['directories'].clear()),('extra-empty-directory',lambda m:m['directories'].update({'z':dr})),('file-directory-collision',lambda m:m['files'].update({'a':row})),('self-reference',lambda m:m['files'].update({'RELEASE_MANIFEST.json':row})),('manifest-directory',lambda m:(m['files'].update({'RELEASE_MANIFEST.json/x':row}),m['directories'].update({'RELEASE_MANIFEST.json':dr}))),('mode-bool',lambda m:m['files']['a/b.txt'].update(mode=True)),('mode-special',lambda m:m['files']['a/b.txt'].update(mode=0o4755)),('mtime-bool',lambda m:m['files']['a/b.txt'].update(mtime_ns=True)),('negative-mtime',lambda m:m['files']['a/b.txt'].update(mtime_ns=-1)),('negative-size',lambda m:m['files']['a/b.txt'].update(bytes=-1)),('size-bool',lambda m:m['files']['a/b.txt'].update(bytes=False)),('short-digest',lambda m:m['files']['a/b.txt'].update(sha256='0')),('uppercase-digest',lambda m:m['files']['a/b.txt'].update(sha256='A'*64)),('unknown-field',lambda m:m.update(extra=0)),('unknown-row-field',lambda m:m['files']['a/b.txt'].update(extra=0))]:
    m=copy.deepcopy(minimal);mut(m);refuses('reject-manifest-'+name,lambda m=m:h['validate_manifest'](m))
refuses('reject-duplicate-json-key',lambda:h['parse'](b'{"x":1,"x":2}'))
# Independently create PNG chunk/raster specimens.
def chunk(k,p):return struct.pack('>I',len(p))+k+p+struct.pack('>I',zlib.crc32(k+p)&0xffffffff)
def png(raw=b'\x00\x10\x20\x30',tail=b'',header=None,compressed=None):
    return b'\x89PNG\r\n\x1a\n'+chunk(b'IHDR',header or struct.pack('>IIBBBBB',1,1,8,2,0,0,0))+chunk(b'IDAT',compressed if compressed is not None else zlib.compress(raw))+chunk(b'IEND',b'')+tail
assert g['validate_png'](png(),h['require'])=={'width':1,'height':1};mark('valid-png-raster')
for name,data in [('truncated',png()[:-5]),('trailing',png(tail=b'x')),('invalid-filter',png(raw=b'\x05abc')),('short-raster',png(raw=b'\x00ab')),('oversized-raster',png(raw=b'\x00abcd')),('extra-zlib-stream',png(compressed=zlib.compress(b'\0abc')+zlib.compress(b'other'))),('wrong-color',png(header=struct.pack('>IIBBBBB',1,1,8,6,0,0,0))),('crc-bit-flip',png()[:-5]+bytes([png()[-5]^1])+png()[-4:])]:refuses('reject-png-'+name,lambda data=data:g['validate_png'](data,h['require']))
manifestfile=WORK/'manifest.json';run('generate-manifest','release66.py',['manifest','--output',manifestfile]);shutil.copy2(manifestfile,fixture/'RELEASE_MANIFEST.json');mpin=hashb(manifestfile.read_bytes())
run('verify-sealed-fixture','release66.py',['verify','--manifest-sha256',mpin]);run('reject-manifest-external-pin','release66.py',['verify','--manifest-sha256','0'*64],ok=False)
for name,fn in [('unfrozen-bytes',lambda d:(d/'README.md').write_text('tampered')),('unexpected-file',lambda d:(d/'unexpected').write_text('x')),('unexpected-empty-dir',lambda d:(d/'extra-empty').mkdir()),('unfrozen-mode',lambda d:(d/'README.md').chmod(0o600)),('unfrozen-ns-mtime',lambda d:os.utime(d/'README.md',ns=(1,1))),('unfrozen-directory-mode',lambda d:(d/'tools').chmod(0o700)),('unfrozen-directory-time',lambda d:os.utime(d/'tools',ns=(1,1)))]:mutate_reject('verify-reject-'+name,fn,'verify',['--manifest-sha256',mpin])
# Deliberately characterize out-of-scope metadata instead of claiming it is sealed.
d=clone('root-metadata-boundary');d.chmod(0o700);os.utime(d,ns=(1,1));run('boundary-root-metadata-not-manifest-sealed','release66.py',['verify','--manifest-sha256',mpin],root=d)
d=clone('manifest-metadata-boundary');(d/'RELEASE_MANIFEST.json').chmod(0o600);os.utime(d/'RELEASE_MANIFEST.json',ns=(1,1));run('boundary-manifest-metadata-not-self-sealed','release66.py',['verify','--manifest-sha256',mpin],root=d)
observations.extend(['The release root mode/mtime are preserved per operation but absent from RELEASE_MANIFEST.json, so not authenticated or transported.','The manifest authenticates its own bytes only via the external SHA-256; its filesystem mode/mtime are not self-sealed. Extraction assigns mode 0644 and fixed epoch.'])
archives=[]
for n in (1,2):
    a=WORK/('archive-'+str(n)+'.zip');run('archive-'+str(n),'release66.py',['archive','--manifest-sha256',mpin,'--output',a]);archives.append(a)
assert archives[0].read_bytes()==archives[1].read_bytes();mark('independent-archive-byte-equality',hashb(archives[0].read_bytes()))
with zipfile.ZipFile(archives[0]) as z:
    infos=z.infolist();assert z.namelist()==sorted(z.namelist());assert all(i.filename.startswith('Report66/') and i.date_time==(2026,10,4,0,0,0) and i.create_system==3 and i.compress_type==zipfile.ZIP_DEFLATED and stat.S_ISREG(i.external_attr>>16) and not i.extra and not i.comment for i in infos)
mark('independent-archive-metadata-inspection')
extracted=WORK/'extracted';run('extract-exact-fixture','release66.py',['extract','--archive',archives[0],'--output-dir',extracted,'--manifest-sha256',mpin]);run('relocated-exact-verification','release66.py',['verify','--manifest-sha256',mpin],root=extracted)
a=scan(fixture);b=scan(extracted)
for n in a:
    if n not in ('.','RELEASE_MANIFEST.json'):assert a[n]==b[n],n
mark('independent-extracted-bytes-modes-ns-mtime-oracle')
run('relocated-locked-pdf-equality','build_report66.py',[*common,'--output-dir',WORK/'relocated-build'],root=extracted)
assert (WORK/'relocated-build/Report66.pdf').read_bytes()==(fixture/'Report66.pdf').read_bytes();mark('independent-relocated-pdf-byte-oracle')
# Repack hostile archives without asking the reviewed tool to create them.
def repack(name,edit):
    out=WORK/(name+'.zip')
    with zipfile.ZipFile(archives[0]) as src,zipfile.ZipFile(out,'w') as dst:
        entries=[(copy.copy(i),src.read(i)) for i in src.infolist()]
        entries=edit(entries)
        for i,data in entries:dst.writestr(i,data)
    return out
edits={
 'zip-traversal':lambda es:es+[(zipfile.ZipInfo('../escape'),b'x')],
 'zip-absolute':lambda es:es+[(zipfile.ZipInfo('/escape'),b'x')],
 'zip-duplicate':lambda es:es+[es[0]],
 'zip-missing':lambda es:es[1:],
 'zip-wrong-order':lambda es:list(reversed(es)),
 'zip-extra-directory':lambda es:es+[(zipfile.ZipInfo('Report66/empty/'),b'')],
}
def alter(es,which,attr,value):
    for i,data in es:
        if i.filename==which:setattr(i,attr,value)
    return es
edits['zip-symlink']=lambda es:alter(es,'Report66/README.md','external_attr',(stat.S_IFLNK|0o777)<<16)
edits['zip-wrong-file-mode']=lambda es:alter(es,'Report66/README.md','external_attr',(stat.S_IFREG|0o600)<<16)
edits['zip-nonunix']=lambda es:alter(es,'Report66/README.md','create_system',0)
edits['zip-tampered-data']=lambda es:[(i,data+b'x' if i.filename=='Report66/README.md' else data) for i,data in es]
for name,edit in edits.items():
    a=repack(name,edit);dest=WORK/(name+'-extract');run('reject-'+name,'release66.py',['extract','--archive',a,'--output-dir',dest,'--manifest-sha256',mpin],ok=False,absent=dest)
a=repack('alternate-zip-time',lambda es:alter(es,'Report66/README.md','date_time',(2001,1,1,0,0,0)))
run('boundary-extraction-does-not-require-fixed-zip-time','release66.py',['extract','--archive',a,'--output-dir',WORK/'alternate-time-extract','--manifest-sha256',mpin])
observations.append('Archive creation emits sorted fixed-time Unix regular entries with deterministic deflate; extraction authenticates logical payload/modes, not all container metadata such as member timestamps or compression settings.')
final={str(p):scan(p) for p in frozen_roots};save(BASE/'ORIGINALS_AFTER.json',final);assert final==originals;mark('all-original-frozen-scopes-and-protected-roots-preserved')
assert {name:hashb((SOURCE/'tools'/name).read_bytes()) for name in EXPECTED}==EXPECTED
receipt={'status':'PASS','independently_authored':True,'test_count':len(results),'tests':results,'observations':observations,'tool_pins':EXPECTED,'input_pins_sha256':hashb((SOURCE/'INPUT_PINS.json').read_bytes()),'synthetic_pins_sha256':pin,'synthetic_lock_sha256':lockpin,'synthetic_manifest_sha256':mpin,'originals_preserved':True,'executed_scope':'Inspected Report66-owned release/build modules; independent synthetic test harness; TeX/Poppler executables. No mathematical or scientific program, original selftest, native interpreter, simulator, saved schedule, or Lean execution.'}
save(BASE/'INDEPENDENT_SYNTHETIC_RESULTS.json',receipt)
print(json.dumps({'status':'PASS','test_count':len(results)}),flush=True)
