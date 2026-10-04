#!/usr/bin/env python3
"""Independent presentation-only hostile tests. Only reviewed owned top-level helpers run."""
import hashlib,json,os,runpy,shutil,stat,struct,subprocess,sys,zlib,zipfile
from pathlib import Path
D=Path('/workspace/shared/oeis-uniform-sectors-tools-review-20261004')
O=D/'independent-hostile-tests'
F=D/'owned-selftests/fixture'
R=Path('/workspace/shared/oeis-uniform-sectors-release-20261004')
O.mkdir()
def sha(b):return hashlib.sha256(b).hexdigest()
def enc(v):return (json.dumps(v,sort_keys=True,indent=2)+'\n').encode()
def need(ok,msg):
 if not ok:raise ValueError(msg)
H=runpy.run_path(str(R/'tools/release.py'),run_name='reviewed_release_helpers')
B=runpy.run_path(str(R/'tools/build_article.py'),run_name='reviewed_png_helpers')
results=[]
pin=sha((F/'manuscript/MANUSCRIPT_PINS.json').read_bytes());ld=(F/'tools/BUILD_DEPENDENCIES_LOCK.json').read_bytes();lp=sha(ld)
manifest=(F/'RELEASE_MANIFEST.json').read_bytes();mp=sha(manifest)
def clone(name):
 p=O/('fixture-'+name);shutil.copytree(F,p,copy_function=shutil.copy2);return p
def command(name,root,tool,args,error=None,no_output=None,flags=None):
 before=H['snapshot'](root)
 c=[sys.executable,*(flags or ['-I','-S','-B']),str(root/'tools'/tool),*args]
 r=subprocess.run(c,cwd=O,stdin=subprocess.DEVNULL,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,timeout=300)
 (O/(name+'.stdout')).write_bytes(r.stdout)
 need((r.returncode==0)==(error is None),'unexpected status '+name)
 if error is not None:need(error.encode() in r.stdout,'wrong rejection reason '+name)
 if no_output is not None:need(not no_output.exists(),'created rejected output '+name)
 need(H['snapshot'](root)==before,'changed fixture '+name)
 results.append({'name':name,'status':'PASS','exit_status':r.returncode,'expected_reason':error,'fixture_preserved':True})
 return r
p=clone('byte-tamper');q=p/'inputs/uniform-sectors/PROOF.md';s=q.stat();q.chmod(0o644);q.write_bytes(q.read_bytes()+b'\n');q.chmod(stat.S_IMODE(s.st_mode));os.utime(q,ns=(s.st_atime_ns,s.st_mtime_ns))
command('reject-frozen-byte-change-same-mtime',p,'release.py',['check-inputs'],'Frozen input inventory')
p=clone('missing');q=p/'inputs/uniform-sectors';q.chmod(0o755);(q/'PROOF.md').unlink()
command('reject-missing-frozen-file',p,'release.py',['check-inputs'],'Frozen input inventory')
p=clone('pin-map');q=p/'INPUT_PINS.json';q.write_bytes(q.read_bytes()+b' ')
command('reject-input-pin-map-change',p,'release.py',['check-inputs'],'Frozen input-pin map differs')
p=clone('duplicate-manuscript');q=p/'manuscript/MANUSCRIPT_PINS.json';v=json.loads(q.read_bytes())['article.tex'];raw=('{"article.tex":"'+v+'","article.tex":"'+v+'"}').encode();q.write_bytes(raw);dest=O/'duplicate-manuscript-output'
command('reject-duplicate-manuscript-key',p,'build_article.py',['--pins-sha',sha(raw),'--bootstrap','--output-dir',str(dest)],'Duplicate JSON key',dest)
p=clone('helper');q=p/'tools/release.py';q.write_bytes(q.read_bytes()+b'\n# Deliberate presentation-helper digest corruption.\n');dest=O/'helper-output'
command('reject-helper-digest-change',p,'build_article.py',['--pins-sha',pin,'--bootstrap','--output-dir',str(dest)],'Release helper differs from inspected source',dest)
dest=O/'optimized-output'
command('reject-python-optimization',F,'build_article.py',['--pins-sha',pin,'--bootstrap','--output-dir',str(dest)],'Use python3 -I -S -B',dest,flags=['-I','-S','-B','-O'])
p=clone('binary-pin');lock=json.loads(ld);lock['executables']['python']['sha256']='0'*64;raw=enc(lock);(p/'tools/BUILD_DEPENDENCIES_LOCK.json').write_bytes(raw);dest=O/'binary-output'
command('reject-stale-executable-lock',p,'build_article.py',['--pins-sha',pin,'--dependency-lock-sha',sha(raw),'--output-dir',str(dest)],'Executable preflight mismatch',dest)
p=clone('extra-system');lock=json.loads(ld);q=Path('/usr/share/texlive/texmf-dist/tex/latex/amsmath/amsmath.sty');need(str(q) not in lock['system_inputs'],'extra system candidate actually used');b=q.read_bytes();lock['system_inputs'][str(q)]={'bytes':len(b),'sha256':sha(b)};raw=enc(lock);(p/'tools/BUILD_DEPENDENCIES_LOCK.json').write_bytes(raw);dest=O/'extra-system-output'
command('reject-extra-unexecuted-lock-dependency',p,'build_article.py',['--pins-sha',pin,'--dependency-lock-sha',sha(raw),'--output-dir',str(dest)],'All-pass executed TeX-input union differs from lock')
need(json.loads((dest/'BUILD_FAILURE.json').read_bytes())['release_preserved'],'missing failure preservation')
original=D/'owned-selftests/archive-a.zip'
def archive_variant(name,kind):
 path=O/(name+'.zip')
 with zipfile.ZipFile(original) as src,zipfile.ZipFile(path,'w') as dst:
  target='UniformSectors/README.md'
  for info in src.infolist():
   data=src.read(info)
   if info.filename==target:
    if kind=='payload':data+=b'X'
    if kind=='mode':info.external_attr=(stat.S_IFREG|0o600)<<16
    if kind=='symlink':info.external_attr=(stat.S_IFLNK|0o777)<<16
   dst.writestr(info,data)
  if kind=='duplicate':dst.writestr('UniformSectors/README.md',b'duplicate')
 return path
for kind,reason in [('payload','Archived bytes differ'),('mode','Archived mode differs'),('symlink','Nonregular ZIP entry'),('duplicate','Archive inventory mismatch or duplicates')]:
 path=archive_variant('archive-'+kind,kind);dest=O/('extract-'+kind)
 command('reject-archive-'+kind,F,'release.py',['extract','--manifest-sha256',mp,'--archive',str(path),'--output-dir',str(dest)],reason,dest)
dest=O/'extract-wrong-pin'
command('reject-archive-external-pin',F,'release.py',['extract','--manifest-sha256','0'*64,'--archive',str(original),'--output-dir',str(dest)],'Archived manifest pin mismatch',dest)
command('reject-extraction-existing-output',F,'release.py',['extract','--manifest-sha256',mp,'--archive',str(original),'--output-dir',str(O)],'Output must be fresh')
p=clone('duplicate-manifest');raw=manifest.rstrip()[:-1]+b',"format":"UniformSectors release manifest v1"}\n';(p/'RELEASE_MANIFEST.json').write_bytes(raw)
command('reject-duplicate-manifest-key',p,'release.py',['verify','--manifest-sha256',sha(raw)],'Duplicate JSON key')
def chunk(kind,payload):return struct.pack('>I',len(payload))+kind+payload+struct.pack('>I',zlib.crc32(kind+payload)&0xffffffff)
def png(width,height,raster):return b'\x89PNG\r\n\x1a\n'+chunk(b'IHDR',struct.pack('>IIBBBBB',width,height,8,2,0,0,0))+chunk(b'IDAT',zlib.compress(raster))+chunk(b'IEND',b'')
for name,data,reason in [('bad-row-filter',png(1,1,b'\x05\0\0\0'),'Invalid PNG row filter'),('oversized-raster',png(1,1,b'\0'*5),'PNG raster size or compression failure'),('short-raster',png(1,1,b'\0'*3),'PNG raster size or compression failure'),('oversized-dimensions',png(10001,1,b'\0'*4),'Invalid PNG raster format')]:
 try:B['validate_png'](data,need)
 except ValueError as e:need(reason in str(e),'wrong PNG rejection '+name)
 else:raise ValueError('accepted hostile PNG '+name)
 results.append({'name':'reject-png-'+name,'status':'PASS','expected_reason':reason})
receipt={'status':'PASS','test_count':len(results),'tests':results,'scope':'Independent presentation-only additional rejection tests using synthetic manuscripts; supplied scientific programs stay inert','owned_helper_sha256':sha((R/'tools/release.py').read_bytes()),'owned_build_sha256':sha((R/'tools/build_article.py').read_bytes())}
(O/'INDEPENDENT_HOSTILE_RECEIPT.json').write_bytes(enc(receipt));print(enc(receipt).decode())
