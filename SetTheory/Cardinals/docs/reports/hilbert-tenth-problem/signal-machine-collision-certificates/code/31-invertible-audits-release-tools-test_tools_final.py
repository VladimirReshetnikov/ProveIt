#!/usr/bin/env python3
"""Independent release engineering tests; executes only inspected owned release/build tools and installed TeX/Poppler."""
import hashlib,json,os,re,runpy,shutil,stat,struct,subprocess,sys,tempfile,zipfile,zlib
from pathlib import Path
A=Path('/workspace/shared/report61-release-tools-independent-review-20261004')
SEED=A/'final-source'
OUT=A/'final-adversarial-tests'
OUT.mkdir()
CASES=[]
def sha(x):return hashlib.sha256(x).hexdigest()
def enc(x):return (json.dumps(x,sort_keys=True,indent=2)+'\n').encode()
def snap(root):
 out={}
 for p in sorted(root.rglob('*')):
  st=p.lstat();name=p.relative_to(root).as_posix()
  out[name]={'mode':st.st_mode,'size':st.st_size if not p.is_dir() else None,'mtime_ns':st.st_mtime_ns if not p.is_dir() else None,'nlink':st.st_nlink if not p.is_dir() else None,'data':os.readlink(p) if p.is_symlink() else sha(p.read_bytes()) if stat.S_ISREG(st.st_mode) else None}
 return out
def fresh(name):
 d=OUT/name;d.mkdir();r=d/'release';shutil.copytree(SEED,r)
 return d,r
def call(name,root,args,expect=False,env=None,flags=None,tool='release61.py'):
 before=snap(root)
 argv=['/usr/bin/python3',*(flags if flags is not None else ['-I','-S','-B']),str(root/'tools'/tool),*map(str,args)]
 p=subprocess.run(argv,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,env=env or {'PATH':'/usr/bin:/bin','LANG':'C.UTF-8'},timeout=300,cwd=OUT)
 (root.parent/(name+'.log')).write_bytes(p.stdout)
 actual=p.returncode==0
 row={'case':name,'argv':argv,'exit':p.returncode,'expected_success':expect,'passed':actual==expect,'source_unchanged':before==snap(root),'last_output':p.stdout.decode(errors='replace')[-1200:]}
 CASES.append(row)
 if not row['passed']:raise RuntimeError(json.dumps(row))
 return p

def buildargs(root,out,*,lock=True):
 args=['--pins-sha',sha((root/'manuscript/MANUSCRIPT_PINS.json').read_bytes()),'--output-dir',str(out)]
 if lock:args+=['--dependency-lock-sha',sha((root/'tools/BUILD_DEPENDENCIES_LOCK.json').read_bytes())]
 return args

def mutate_case(name,mutate,tool='release61.py',args=None):
 d,r=fresh(name);mutate(d,r)
 call(name,r,args(r,d) if args else ['check-inputs'],tool=tool)

# Reject before output creation; malformed input paths are never followed.
for name,func in [
 ('frozen-content',lambda d,r:(r/'science/frozen-proof/PROOF.md').write_bytes(b'changed')),
 ('frozen-checker-content',lambda d,r:(r/'science/frozen-proof/static_algebra.py').write_bytes(b'raise RuntimeError("must never run")')),
 ('frozen-extra-file',lambda d,r:(r/'science/frozen-proof/extra').write_bytes(b'x')),
 ('frozen-extra-directory',lambda d,r:(r/'science/empty').mkdir()),
 ('frozen-delete',lambda d,r:(r/'audits/scientific/REVIEW.md').unlink()),
 ('input-pins-corrupt',lambda d,r:(r/'INPUT_PINS.json').write_bytes(b'{}')),
 ('source-symlink',lambda d,r:(r/'evil').symlink_to('/etc/passwd')),
 ('source-directory-symlink',lambda d,r:(r/'evil').symlink_to('/tmp',target_is_directory=True)),
 ('source-hardlink',lambda d,r:os.link(r/'science/frozen-proof/PROOF.md',r/'linked')),
 ('source-fifo',lambda d,r:os.mkfifo(r/'pipe')),
 ('source-backslash',lambda d,r:(r/'bad\\name').write_bytes(b'x')),
 ('source-newline',lambda d,r:(r/'bad\nname').write_bytes(b'x'))]:mutate_case(name,func)

for name in ('build','release'):
 tool='build_report61.py' if name=='build' else 'release61.py'
 for flagname,flags in [('optimized',['-I','-S','-B','-O']),('missing-isolation',['-S','-B']),('missing-no-site',['-I','-B']),('missing-no-bytecode',['-I','-S'])]:
  d,r=fresh(name+'-'+flagname);args=buildargs(r,d/'output') if name=='build' else ['check-inputs'];call(name+'-'+flagname,r,args,flags=flags,tool=tool)

for name,mutate in [
 ('module-corrupt',lambda d,r:(r/'manuscript/results.tex').write_bytes(b'x')),
 ('module-extra',lambda d,r:(r/'manuscript/extra.tex').write_bytes(b'x')),
 ('flat-corrupt',lambda d,r:(r/'Report61.tex').write_bytes(b'x')),
 ('pins-malformed',lambda d,r:(r/'manuscript/MANUSCRIPT_PINS.json').write_bytes(b'[]')),
 ('pins-duplicate',lambda d,r:(r/'manuscript/MANUSCRIPT_PINS.json').write_bytes(b'{"a":1,"a":2}')),
 ('pins-nonfinite',lambda d,r:(r/'manuscript/MANUSCRIPT_PINS.json').write_bytes(b'{"a":NaN}')),
 ('pins-bool-size',lambda d,r:(r/'manuscript/MANUSCRIPT_PINS.json').write_bytes(enc({'Report61.tex':{'bytes':True,'sha256':'0'*64}}))),
 ('lock-malformed',lambda d,r:(r/'tools/BUILD_DEPENDENCIES_LOCK.json').write_bytes(b'[]')),
 ('lock-duplicate',lambda d,r:(r/'tools/BUILD_DEPENDENCIES_LOCK.json').write_bytes(b'{"a":1,"a":2}'))]:
 mutate_case(name,mutate,tool='build_report61.py',args=lambda r,d:buildargs(r,d/'output'))

def lockchange(root,fn):
 p=root/'tools/BUILD_DEPENDENCIES_LOCK.json';v=json.loads(p.read_bytes());fn(v);p.write_bytes(enc(v))
for name,fn in [
 ('lock-binary-hash',lambda v:v['executables']['pdftex'].update(sha256='0'*64)),
 ('lock-system-hash',lambda v:next(iter(v['system_inputs'].values())).update(sha256='0'*64)),
 ('lock-extra-executable',lambda v:v['executables'].update(extra=v['executables']['pdftex'])),
 ('lock-relative-input',lambda v:v['system_inputs'].update({'relative':{'sha256':'0'*64,'bytes':0}})),
 ('lock-parent-alias',lambda v:v['system_inputs'].update({'/etc/texmf/../passwd':{'sha256':'0'*64,'bytes':0}})),
 ('lock-outside-input',lambda v:v['system_inputs'].update({'/etc/passwd':{'sha256':'0'*64,'bytes':0}})),
 ('lock-bool-size',lambda v:next(iter(v['system_inputs'].values())).update(bytes=True))]:
 mutate_case(name,lambda d,r,fn=fn:lockchange(r,fn),tool='build_report61.py',args=lambda r,d:buildargs(r,d/'output'))

# Output path cases exercised independently on both output-producing command paths.
for tool in ('build_report61.py','release61.py'):
 for kind in ('relative','dot','dotdot','double-slash','trailing-slash','existing-file','existing-dir','inside','equal','ancestor','parent-symlink','leaf-symlink','leaf-hardlink','missing-parent'):
  d,r=fresh(tool.split('.')[0]+'-'+kind)
  (r/'Report61.pdf').write_bytes((SEED/'Report61.pdf').read_bytes());(r/'qa/VISUAL_REVIEW.md').write_text('Fixture only; not a release visual approval.\n')
  output=str(d/'output')
  if kind=='relative':output='relative'
  if kind=='dot':output=str(d)+'/./output'
  if kind=='dotdot':output=str(d)+'/../output'
  if kind=='double-slash':output='//'+str(d).lstrip('/')+'/output'
  if kind=='trailing-slash':output+='/'
  if kind=='existing-file':Path(output).write_text('sentinel')
  if kind=='existing-dir':Path(output).mkdir()
  if kind=='inside':output=str(r/'output')
  if kind=='equal':output=str(r)
  if kind=='ancestor':output=str(d)
  if kind=='parent-symlink':(d/'link').symlink_to(d);output=str(d/'link/output')
  if kind=='leaf-symlink':(d/'sentinel').write_text('sentinel');Path(output).symlink_to(d/'sentinel')
  if kind=='leaf-hardlink':(d/'sentinel').write_text('sentinel');os.link(d/'sentinel',output)
  if kind=='missing-parent':output=str(d/'missing/output')
  args=buildargs(r,output) if tool.startswith('build') else ['seal','--zip',output]
  call(tool+'-'+kind,r,args,tool=tool)
  if (d/'sentinel').exists() and (d/'sentinel').read_text()!='sentinel':raise RuntimeError('Sentinel changed')

# Preparation semantics, unresolved input syntax, and source aliases.
d,r=fresh('prepare');call('prepare',r,['prepare'],expect=True)
for kind in ('duplicate-input','missing-input','space-input','space-include'):
 d,r=fresh(kind);p=r/'manuscript/Report61.tex';data=p.read_bytes()
 if kind=='duplicate-input':data+=b'\\input{results.tex}\n'
 if kind=='missing-input':data=data.replace(b'\\input{results.tex}\n',b'')
 if kind=='space-input':data+=b'\\input forbidden\n'
 if kind=='space-include':data+=b'\\include forbidden\n'
 p.write_bytes(data);call(kind,r,['prepare'])
for tool in ('build_report61.py','release61.py'):
 d,r=fresh('root-alias-'+tool);link=d/'alias';link.symlink_to(r,target_is_directory=True)
 call('root-alias',link,buildargs(link,d/'output') if tool.startswith('build') else ['check-inputs'],tool=tool)

# Real locked clean build and polluted-environment build against copied exact source.
d,r=fresh('clean-build');call('clean-build',r,buildargs(r,d/'output'),expect=True,tool='build_report61.py')
clean=d/'output';pdf=(clean/'Report61.pdf').read_bytes();(r/'Report61.pdf').write_bytes(pdf)
(r/'qa/VISUAL_REVIEW.md').write_text('Fixture only; used to test deterministic archive mechanics.\n')
call('seal-one',r,['seal','--zip',d/'one.zip'],expect=True)
call('seal-two',r,['seal','--zip',d/'two.zip'],expect=True)
if (d/'one.zip').read_bytes()!=(d/'two.zip').read_bytes():raise RuntimeError('Nondeterministic ZIP')
manraw=(r/'RELEASE_MANIFEST.json').read_bytes();pin=sha(manraw)
call('verify-manifest',r,['verify','--manifest-sha256',pin],expect=True)
with zipfile.ZipFile(d/'one.zip') as z:z.extractall(d/'extracted')
call('verify-extracted',d/'extracted/Report61',['verify','--manifest-sha256',pin],expect=True)
call('rebuild-extracted',d/'extracted/Report61',buildargs(d/'extracted/Report61',d/'rebuilt')+['--require-packaged-match'],expect=True,tool='build_report61.py')
for name,fn in [
 ('manifest-duplicate',lambda raw:b'{"files":{},"files":{}}'),
 ('manifest-list',lambda raw:b'[]'),
 ('manifest-schema',lambda raw:enc({'report':61,'format':1,'files':{}})),
 ('manifest-bool-size',lambda raw:enc({'report':61,'format':1,'scope':'Every regular release file except this manifest; ZIP separately hashed','files':{'x':{'bytes':True,'sha256':'0'*64}}})),
 ('manifest-alias',lambda raw:enc({'report':61,'format':1,'scope':'Every regular release file except this manifest; ZIP separately hashed','files':{'../x':{'bytes':0,'sha256':'0'*64}}})),
 ('manifest-stale',lambda raw:raw.replace(b'"Report61.pdf": {',b'"absent.pdf": {'))]:
 base=d;case=OUT/name;shutil.copytree(r,case/'release');rr=case/'release';bad=fn(manraw);(rr/'RELEASE_MANIFEST.json').write_bytes(bad)
 call(name,rr,['verify','--manifest-sha256',sha(bad)])
call('sealed-prepare-refused',r,['prepare'])
call('wrong-manifest-pin',r,['verify','--manifest-sha256','0'*64])

h,hr=fresh('hostile-build');evil=h/'evil';evil.mkdir();(evil/'sitecustomize.py').write_text('raise RuntimeError("executed hostile sitecustomize")\n');(evil/'usercustomize.py').write_text('raise RuntimeError("executed hostile usercustomize")\n')
for name in ('pdftex','pdflatex','kpsewhich','pdftoppm','pdftotext','pdfinfo'):
 p=evil/name;p.write_text('#!/bin/sh\necho compromised > '+str(h/'SENTINEL')+'\nexit 77\n');p.chmod(0o755)
(evil/'pdflatex.fmt').write_bytes(b'poison format');(evil/'article.cls').write_text('\\errmessage{hostile class}')
hostile={'PATH':str(evil),'HOME':str(evil),'TMPDIR':str(evil),'LANG':'bad_LOCALE','LC_ALL':'bad_LOCALE','TZ':'Pacific/Honolulu','SOURCE_DATE_EPOCH':'1','PYTHONPATH':str(evil),'PYTHONHOME':str(evil),'PYTHONSTARTUP':str(evil/'sitecustomize.py'),'TEXINPUTS':str(evil),'TEXFORMATS':str(evil),'TEXMF':str(evil),'TEXMFHOME':str(evil),'TEXMFVAR':str(evil),'TEXMFCONFIG':str(evil),'TEXFONTMAPS':str(evil),'shell_escape':'t','openin_any':'a','openout_any':'a','MKTEXPK':'1','MKTEXTFM':'1','MKTEXMF':'1'}
call('hostile-build',hr,buildargs(hr,h/'output'),expect=True,tool='build_report61.py',env=hostile)
if (h/'output/Report61.pdf').read_bytes()!=pdf or (h/'SENTINEL').exists():raise RuntimeError('Hostile environment changed PDF/executed poison')
if {p.name:sha(p.read_bytes()) for p in (clean/'pages').iterdir()}!={p.name:sha(p.read_bytes()) for p in (h/'output/pages').iterdir()}:raise RuntimeError('Rendered pages differ')

# A valid preflight lock lacking one actual input must fail the post-build equality gate.
d,r=fresh('postflight-extra-dependency');lockchange(r,lambda v:v['system_inputs'].pop(next(iter(v['system_inputs']))));call('postflight-extra-dependency',r,buildargs(r,d/'output'),tool='build_report61.py')
if 'Post-build dependency set' not in (d/'postflight-extra-dependency.log').read_text():raise RuntimeError('Wrong postflight refusal')

# Parse and decompress every actual page; test CRC-correct hostile raster mutations.
mod=runpy.run_path(str(SEED/'tools/build_report61.py'),run_name='audit_load')
validate=mod['validate_png'];pngcases=[]
for p in sorted((clean/'pages').iterdir()):pngcases.append({'case':p.name,'dimensions':validate(p.read_bytes()),'sha256':sha(p.read_bytes())})
def chunk(k,x):return struct.pack('>I',len(x))+k+x+struct.pack('>I',zlib.crc32(k+x)&0xffffffff)
head=b'\x89PNG\r\n\x1a\n';ihdr=chunk(b'IHDR',struct.pack('>IIBBBBB',1,1,8,2,0,0,0));idat=chunk(b'IDAT',zlib.compress(b'\0\0\0\0'));iend=chunk(b'IEND',b'')
valid=head+ihdr+idat+iend
validate(valid)
for name,data in [('signature',b'bad'),('truncated-chunk',valid[:-1]),('crc',valid[:42]+bytes([valid[42]^1])+valid[43:]),('trailing',valid+b'x'),('duplicate-header',head+ihdr+ihdr+idat+iend),('missing-data',head+ihdr+iend),('bad-deflate',head+ihdr+chunk(b'IDAT',b'bad')+iend),('too-long-raster',head+ihdr+chunk(b'IDAT',zlib.compress(b'\0'*5))+iend),('bad-filter',head+ihdr+chunk(b'IDAT',zlib.compress(b'\5\0\0\0'))+iend),('trailing-deflate',head+ihdr+chunk(b'IDAT',zlib.compress(b'\0'*4)+b'x')+iend),('bad-phys-length',head+ihdr+chunk(b'pHYs',b'bad')+idat+iend),('bad-phys-unit',head+ihdr+chunk(b'pHYs',struct.pack('>IIB',1,1,2))+idat+iend),('duplicate-phys',head+ihdr+chunk(b'pHYs',struct.pack('>IIB',1,1,1))*2+idat+iend),('late-phys',head+ihdr+idat+chunk(b'pHYs',struct.pack('>IIB',1,1,1))+iend),('bad-dimensions',head+chunk(b'IHDR',struct.pack('>IIBBBBB',0,1,8,2,0,0,0))+idat+iend)]:
 try:validate(data)
 except (ValueError,zlib.error):pngcases.append({'case':name,'rejected':True})
 else:raise RuntimeError('PNG mutation accepted: '+name)
summary={'status':'PASS','command_cases':len(CASES),'all_rejection_cases_preserved_sources':all(row['source_unchanged'] for row in CASES if not row['expected_success']),'pdf_sha256':sha(pdf),'png_pages':len(list((clean/'pages').iterdir())),'clean_hostile_pdf_and_all_pngs_equal':True,'zip_deterministic':True,'zip_sha256':sha((OUT/'clean-build/one.zip').read_bytes()),'extracted_source_build_matches':True,'tool_hashes':{p.name:sha(p.read_bytes()) for p in (SEED/'tools').glob('*.py')},'execution_boundary':'Only owned inspected release/build tools and installed TeX/Poppler; no scientific programs executed'}
(OUT/'RESULTS.json').write_bytes(enc(CASES));(OUT/'PNG_RESULTS.json').write_bytes(enc(pngcases));(OUT/'SUMMARY.json').write_bytes(enc(summary));print(enc(summary).decode())
