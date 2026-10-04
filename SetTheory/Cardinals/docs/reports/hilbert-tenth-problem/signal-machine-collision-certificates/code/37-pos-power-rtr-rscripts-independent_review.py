"""Independent presentation/release adversarial review. Runs only reviewed current
release tools and authored synthetic fixtures; frozen scientific evidence stays inert.
"""
from pathlib import Path
import copy,hashlib,json,os,runpy,shutil,stat,struct,subprocess,sys,warnings,zipfile,zlib
BASE=Path('/workspace/shared/report67-release-independent-review-20261004')
CANDIDATE=BASE/'candidate'
PINS='fae9d4bcd2e199f70a136f73ac42f22aa21e4c368ac6ff2c1878aa5640a00822'
LOCK='924a24fab30a2e05eccd168d7951273e31b99a8adbb3290ab5d8b6f332b884e1'
PDF='37005d94aa9a6037c35f64638a2443fdb471aff9cee8eb56c1529c32566fa58d'
I=runpy.run_path(str(BASE/'auth_snapshot.py'))
inv,sha,enc=I['inventory'],I['sha'],I['encoded']
H=runpy.run_path(str(CANDIDATE/'tools/release67.py'),run_name='independent_review_release')
B=runpy.run_path(str(CANDIDATE/'tools/build_report67.py'),run_name='independent_review_builder')
TESTS=[]
LOGS=BASE/'independent-logs'; LOGS.mkdir()

def record(name,**fields):
    TESTS.append({'name':name,'status':'PASS',**fields})
    (BASE/'INDEPENDENT_PROGRESS.json').write_bytes(enc(TESTS))
    print(name,flush=True)

def command(name,root,tool,args,success=True,expected=None,no_output=None,env=None):
    before=inv(root)
    cp=subprocess.run([sys.executable,'-I','-S','-B',str(root/'tools'/tool),*args],cwd=BASE,env=env,
        stdin=subprocess.DEVNULL,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,timeout=300)
    (LOGS/(name+'.stdout')).write_bytes(cp.stdout)
    assert (cp.returncode==0)==success,(name,cp.stdout[-2000:])
    if expected: assert expected.encode() in cp.stdout,(name,cp.stdout[-2000:])
    if no_output is not None: assert not no_output.exists(),name
    assert inv(root)==before,name+' changed source'
    record(name,exit_status=cp.returncode,source_preserved=True)
    return cp

def rejects(name,fn):
    try: fn()
    except (ValueError,KeyError,TypeError,zlib.error,UnicodeError) as e:
        record(name,error_type=type(e).__name__,error=str(e)); return
    raise AssertionError(name+' unexpectedly accepted')

def clone(name):
    p=BASE/('challenge-'+name); shutil.copytree(SEALED,p,copy_function=shutil.copy2); return p

def verify_fail(name,change,expected=None):
    p=clone(name); change(p)
    command(name,p,'release67.py',['verify','--manifest-sha256',MANIFEST_PIN],False,expected)

def pngchunk(kind,payload):
    return struct.pack('>I',len(payload))+kind+payload+struct.pack('>I',zlib.crc32(kind+payload)&0xffffffff)

def png(pixels=b'\x00\x00\x00\x00',width=1,height=1,depth=8,color=2,interlace=0,extra=b''):
    return b'\x89PNG\r\n\x1a\n'+pngchunk(b'IHDR',struct.pack('>IIBBBBB',width,height,depth,color,0,0,interlace))+pngchunk(b'IDAT',zlib.compress(pixels)+extra)+pngchunk(b'IEND',b'')

original_candidate=inv(CANDIDATE)
command('fixed-input-authentication',CANDIDATE,'release67.py',['check-inputs'])
prepared=BASE/'independent-flatten'
command('standalone-flatten',CANDIDATE,'release67.py',['prepare','--output-dir',str(prepared)])
assert (prepared/'Report67.tex').read_bytes()==(CANDIDATE/'Report67.tex').read_bytes()
assert sha((prepared/'MANUSCRIPT_PINS.json').read_bytes())==PINS
record('standalone-exact-bytes')

# Independently construct a manifest over a preserved copy. This is a candidate
# testing seal only, not the parent's later final release seal.
SEALED=BASE/'sealed-candidate'; shutil.copytree(CANDIDATE,SEALED,copy_function=shutil.copy2)
s=inv(SEALED); manifest={'format':'Report67 release manifest v1','files':s['files'],'directories':s['directories']}
manifest_bytes=enc(manifest); MANIFEST_PIN=sha(manifest_bytes)
(SEALED/'RELEASE_MANIFEST.json').write_bytes(manifest_bytes)
(BASE/'CANDIDATE_MANIFEST.json').write_bytes(manifest_bytes)
command('independently-authenticated-manifest',SEALED,'release67.py',['verify','--manifest-sha256',MANIFEST_PIN])
record('candidate-seal-pin',sha256=MANIFEST_PIN,files=len(manifest['files']),directories=len(manifest['directories']))

for name,value in [('relative','relative/path'),('dotdot',str(BASE)+'/../outside'),('double-slash','//workspace/shared/new-output'),('root-overlap',str(SEALED/'new-output')),('protected-overlap',str(H['PROTECTED'][0]/'independent-should-not-exist'))]:
    command('path-reject-'+name,SEALED,'release67.py',['prepare','--output-dir',value],False)
link=BASE/'output-ancestor-link'; link.symlink_to(BASE,target_is_directory=True)
command('path-reject-symlink-ancestor',SEALED,'release67.py',['prepare','--output-dir',str(link/'unused')],False)
command('path-reject-existing',SEALED,'release67.py',['prepare','--output-dir',str(prepared)],False)

verify_fail('manifest-file-content',lambda p:(p/'README.md').write_bytes(b'changed'))
verify_fail('manifest-file-extra',lambda p:(p/'extra.txt').write_bytes(b'extra'))
verify_fail('manifest-file-missing',lambda p:(p/'README.md').unlink())
verify_fail('manifest-empty-directory',lambda p:(p/'empty').mkdir())
verify_fail('manifest-file-mode',lambda p:(p/'README.md').chmod(0o600))
verify_fail('manifest-directory-mode',lambda p:(p/'manuscript').chmod(0o700))
def tick(p):
    s=p.stat();os.utime(p,ns=(s.st_atime_ns,s.st_mtime_ns+1))
verify_fail('manifest-file-nanosecond',lambda p:tick(p/'README.md'))
verify_fail('manifest-directory-nanosecond',lambda p:tick(p/'manuscript'))
# The reviewed inventory itself must reject links/special files; do not pass them
# to the independent inventory, whose deliberate strictness rejects them first.
for name,make in [('symlink',lambda p:(p/'link').symlink_to(p/'README.md')),('hardlink',lambda p:os.link(p/'README.md',p/'link')),('fifo',lambda p:os.mkfifo(p/'pipe'))]:
    p=clone(name);make(p)
    cp=subprocess.run([sys.executable,'-I','-S','-B',str(p/'tools/release67.py'),'verify','--manifest-sha256',MANIFEST_PIN],stdout=subprocess.PIPE,stderr=subprocess.STDOUT,timeout=30)
    (LOGS/('manifest-'+name+'.stdout')).write_bytes(cp.stdout)
    assert cp.returncode!=0
    record('manifest-'+name+'-rejected',exit_status=cp.returncode)

# Pin authentication survives recomputing surrounding manifests.
p=clone('frozen-pin-replacement');pmap=json.loads((p/'INPUT_PINS.json').read_bytes());pmap['files']['science/bounded-certificates/PROOF.md']['sha256']='0'*64
(p/'INPUT_PINS.json').write_bytes(enc(pmap))
command('frozen-pin-replacement-rejected',p,'release67.py',['check-inputs'],False,'Frozen input-pin map differs')
rejects('json-duplicate-key',lambda:H['parse'](b'{"a":1,"a":2}'))
for name in ('../escape','/absolute','a/../b','a//b','a\\b','a\x00b','a/','./a'):
    rejects('relative-name-'+repr(name),lambda n=name:H['relative_name'](n))
for name,change in [
    ('bool-bytes',lambda m:m['files']['README.md'].__setitem__('bytes',True)),
    ('negative-mtime',lambda m:m['files']['README.md'].__setitem__('mtime_ns',-1)),
    ('special-mode',lambda m:m['files']['README.md'].__setitem__('mode',0o4755)),
    ('uppercase-digest',lambda m:m['files']['README.md'].__setitem__('sha256','A'*64)),
    ('extra-field',lambda m:m['files']['README.md'].__setitem__('extra',0)),
    ('missing-directory',lambda m:m['directories'].pop('manuscript')),
    ('empty-directory',lambda m:m['directories'].__setitem__('unoccupied',{'mode':0o755,'mtime_ns':0})),
    ('file-directory-collision',lambda m:m['directories'].__setitem__('README.md',{'mode':0o755,'mtime_ns':0})),
    ('self-reference',lambda m:m['files'].__setitem__('RELEASE_MANIFEST.json',copy.deepcopy(m['files']['README.md']))),
]:
    m=copy.deepcopy(manifest);change(m);rejects('schema-'+name,lambda m=m:H['validate_manifest'](m))

valid=png();assert B['validate_png'](valid,H['require'])=={'width':1,'height':1};record('png-valid-synthetic')
for name,data in [('truncated',valid[:-1]),('bad-crc',valid[:45]+bytes([valid[45]^1])+valid[46:]),('trailing-bytes',valid+b'bad'),('bad-filter',png(pixels=b'\x05\x00\x00\x00')),('bad-raster-length',png(pixels=b'\x00\x00')),('second-zlib-stream',png(extra=zlib.compress(b'bad'))),('grayscale',png(color=0)),('zero-dimension',png(width=0)),('interlaced',png(interlace=1)),('missing-iend',valid[:-12])]:
    rejects('png-reject-'+name,lambda data=data:B['validate_png'](data,H['require']))

# Full-article replay evidence is parsed independently of the reported booleans.
full=BASE/'full-build';r=json.loads((full/'BUILD_RECEIPT.json').read_bytes());assert r['status']=='PASS' and r['page_count']==24
assert sha((full/'Report67.pdf').read_bytes())==PDF
assert (full/'BUILD_DEPENDENCIES.json').read_bytes()==(CANDIDATE/'tools/BUILD_DEPENDENCIES_LOCK.json').read_bytes()
union=json.loads((full/'RECORDER_INPUT_UNION.json').read_bytes());lock=json.loads((full/'BUILD_DEPENDENCIES.json').read_bytes())
assert [p['pass'] for p in union['passes']]==['format','compile-1','compile-2','compile-3']
observed=set()
for pas in union['passes']:
    fls=(full/(pas['pass']+'.fls')).read_bytes(); assert sha(fls)==pas['fls_sha256'];inputs=set()
    for line in fls.decode().splitlines():
        if line.startswith('INPUT '):
            p=Path(line[6:])
            if p.is_absolute() and any(str(p).startswith(prefix) for prefix in B['SYSTEM_ROOTS']):inputs.add(str(p.resolve(strict=True)))
    assert inputs==set(pas['system_inputs']);observed|=inputs
assert union['union']==lock['system_inputs']
assert observed<=set(lock['system_inputs'])
assert set(lock['system_inputs'])-observed <= {str(Path('/usr/share/texmf/fonts/map/dvips/lm/lm.map')),
'/usr/share/texlive/texmf-dist/fonts/map/dvips/amsfonts/cm.map','/usr/share/texlive/texmf-dist/fonts/map/dvips/amsfonts/cmextra.map','/usr/share/texlive/texmf-dist/fonts/map/dvips/amsfonts/symbols.map','/usr/share/texlive/texmf-dist/fonts/map/dvips/amsfonts/latxfont.map'}
record('full-article-exact-pdf-and-all-pass-union',pdf_sha256=PDF,pages=24,system_inputs=len(lock['system_inputs']),per_pass={x['pass']:len(x['system_inputs']) for x in union['passes']})
rasters=json.loads((full/'PAGE_INVENTORY.json').read_bytes());assert len(rasters)==24
for name,row in rasters.items():
    data=(full/'pages'/name).read_bytes();assert len(data)==row['bytes'] and sha(data)==row['sha256'];assert B['validate_png'](data,H['require'])=={'width':row['width'],'height':row['height']}
record('all-24-raster-records-independently-validated')

# Hostile inherited values must not alter the article, tool selection, or source.
hostile=os.environ.copy();hostile.update({v:str(SEALED/'science/bounded-certificates') for v in ('TMPDIR','TEMP','TMP','HOME','TEXMFHOME','TEXMFVAR','TEXMFCONFIG','TEXFORMATS','TEXINPUTS','TEXFONTMAPS')})
hostile.update({'PATH':'/nonexistent','PYTHONPATH':'/nonexistent','PYTHONHOME':'/nonexistent','PYTHONOPTIMIZE':'2','SOURCE_DATE_EPOCH':'1','FORCE_SOURCE_DATE':'0','shell_escape':'t','openin_any':'a','openout_any':'a'})
command('hostile-environment-full-article',SEALED,'build_report67.py',['--output-dir',str(BASE/'hostile-full-build'),'--pins-sha',PINS,'--dependency-lock-sha',LOCK,'--require-packaged-match'],env=hostile)

for suffix in ('a','b'):
    command('archive-'+suffix,SEALED,'release67.py',['archive','--manifest-sha256',MANIFEST_PIN,'--output',str(BASE/('candidate-'+suffix+'.zip'))])
assert (BASE/'candidate-a.zip').read_bytes()==(BASE/'candidate-b.zip').read_bytes()
with zipfile.ZipFile(BASE/'candidate-a.zip') as z:
    assert z.namelist()==['Report67/'+n for n in sorted([*manifest['files'],'RELEASE_MANIFEST.json'])]
    assert all(i.date_time==(2026,10,4,0,0,0) and i.create_system==3 and i.compress_type==zipfile.ZIP_DEFLATED for i in z.infolist())
record('deterministic-archive-bytes-and-container-metadata',sha256=sha((BASE/'candidate-a.zip').read_bytes()))
relocated=BASE/'relocated'
command('extract-preserve-exact-descendants',SEALED,'release67.py',['extract','--manifest-sha256',MANIFEST_PIN,'--archive',str(BASE/'candidate-a.zip'),'--output-dir',str(relocated)])
ri=inv(relocated); assert ri['directories']==manifest['directories']
assert {n:r for n,r in ri['files'].items() if n!='RELEASE_MANIFEST.json'}==manifest['files'];assert ri['root']['mode']==0o700
record('relocated-independent-inventory-equality')
command('relocated-authenticate',relocated,'release67.py',['verify','--manifest-sha256',MANIFEST_PIN])
command('relocated-full-article-exact-rebuild',relocated,'build_report67.py',['--output-dir',str(BASE/'relocated-full-build'),'--pins-sha',PINS,'--dependency-lock-sha',LOCK,'--require-packaged-match'])
assert sha((BASE/'relocated-full-build/Report67.pdf').read_bytes())==PDF

# Archive attacks are fully prepared before extraction; refusal must precede output.
for attack in ('traversal','duplicate','extra','tampered','mode','symlink','bad-manifest','wrong-order'):
    dest=BASE/('attack-'+attack+'.zip')
    with zipfile.ZipFile(BASE/'candidate-a.zip') as zin,zipfile.ZipFile(dest,'w',compression=zipfile.ZIP_DEFLATED) as zout:
        entries=zin.infolist()
        if attack=='wrong-order':entries=list(reversed(entries))
        for original in entries:
            i=copy.copy(original); data=zin.read(original)
            if i.filename=='Report67/README.md':
                if attack=='tampered':data+=b'changed'
                if attack=='mode':i.external_attr=(stat.S_IFREG|0o600)<<16
                if attack=='symlink':i.external_attr=(stat.S_IFLNK|0o777)<<16
            if i.filename=='Report67/RELEASE_MANIFEST.json' and attack=='bad-manifest':data=b'{}'
            zout.writestr(i,data)
        if attack in ('traversal','extra','duplicate'):
            with warnings.catch_warnings():
                warnings.simplefilter('ignore',UserWarning)
                zout.writestr({'traversal':'../escape','extra':'Report67/extra','duplicate':'Report67/README.md'}[attack],b'bad')
    output=BASE/('attack-output-'+attack)
    command('archive-reject-'+attack,SEALED,'release67.py',['extract','--manifest-sha256',MANIFEST_PIN,'--archive',str(dest),'--output-dir',str(output)],False,no_output=output)

# Preflight failures and an unused-but-valid locked dependency challenge postflight
# union equality without changing the system toolchain.
for name,edit in [('stale-executable',lambda l:l['executables']['pdftex'].__setitem__('sha256','0'*64)),('stale-system',lambda l:next(iter(l['system_inputs'].values())).__setitem__('sha256','0'*64))]:
    p=clone(name);l=copy.deepcopy(lock);edit(l);data=enc(l);(p/'tools/BUILD_DEPENDENCIES_LOCK.json').write_bytes(data);output=BASE/(name+'-output')
    command(name+'-preflight',p,'build_report67.py',['--output-dir',str(output),'--pins-sha',PINS,'--dependency-lock-sha',sha(data)],False,no_output=output)
unused=next(p for p in Path('/usr/share/texlive/texmf-dist/tex/latex/base').glob('*.sty') if str(p.resolve()) not in lock['system_inputs'])
p=clone('unused-lock-entry');l=copy.deepcopy(lock);data=unused.read_bytes();l['system_inputs'][str(unused.resolve())]={'bytes':len(data),'sha256':sha(data)};data=enc(l);(p/'tools/BUILD_DEPENDENCIES_LOCK.json').write_bytes(data)
command('postflight-reject-unused-lock-entry',p,'build_report67.py',['--output-dir',str(BASE/'unused-lock-entry-output'),'--pins-sha',PINS,'--dependency-lock-sha',sha(data)],False,'All-pass executed TeX-input union differs from lock')

assert inv(CANDIDATE)==original_candidate
originals=json.loads((BASE/'ORIGINALS_BEFORE.json').read_bytes());after={p:inv(Path(p)) for p in originals};assert after==originals
(BASE/'ORIGINALS_AFTER.json').write_bytes(enc(after))
record('candidate-snapshot-and-seven-original-roots-preserved')
receipt={'status':'PASS','scope':'Independent presentation/release candidate review; no scientific code execution; not the final release seal','candidate_manifest_sha256':MANIFEST_PIN,'pdf_sha256':PDF,'tests':TESTS,'test_count':len(TESTS),'original_roots_preserved':True,'candidate_snapshot_preserved':True,'review_script_sha256':sha(Path(__file__).read_bytes())}
(BASE/'INDEPENDENT_RECEIPT.json').write_bytes(enc(receipt))
print(json.dumps({'status':'PASS','tests':len(TESTS),'candidate_manifest_sha256':MANIFEST_PIN}),flush=True)
