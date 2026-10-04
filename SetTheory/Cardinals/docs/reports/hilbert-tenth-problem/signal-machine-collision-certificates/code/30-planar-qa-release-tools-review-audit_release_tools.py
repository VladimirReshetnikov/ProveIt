#!/usr/bin/env python3
"""Independent source-reviewed tool tests; executes only the two release tools."""
import argparse,hashlib,json,os,shutil,stat,subprocess,sys,time,zipfile
from pathlib import Path

def require(ok,message):
 if not ok: raise RuntimeError(message)
def enc(v):return (json.dumps(v,sort_keys=True,indent=2)+'\n').encode()
def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def snap(r):
 out={}
 for p in sorted(r.rglob('*')):
  s=p.lstat(); name=p.relative_to(r).as_posix(); typ='dir' if stat.S_ISDIR(s.st_mode) else 'file' if stat.S_ISREG(s.st_mode) else 'other'
  if typ=='file':out[name]={'sha256':digest(p),'bytes':s.st_size,'mode':stat.S_IMODE(s.st_mode),'mtime_ns':s.st_mtime_ns}
 return out

def run(argv,cwd,env=None):
 p=subprocess.run(argv,cwd=cwd,env=env,stdin=subprocess.DEVNULL,stdout=subprocess.PIPE,stderr=subprocess.PIPE,timeout=300)
 return {'argv':list(map(str,argv)),'returncode':p.returncode,'stdout':p.stdout.decode(errors='replace'),'stderr':p.stderr.decode(errors='replace')}

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--source',required=True);ap.add_argument('--output',required=True);ap.add_argument('--builds',action='store_true');a=ap.parse_args()
 r=Path(a.source);o=Path(a.output);o.mkdir();fx=o/'fixtures';fx.mkdir();records=[];original=snap(r);n=0
 (o/'source-before.json').write_bytes(enc(original))
 def fixture(label):
  nonlocal n
  n+=1;dest=fx/(f'{n:03d}-'+label);shutil.copytree(r,dest,copy_function=shutil.copy2);return dest
 def invoke(root,tool,args,flags=('-I','-S','-B'),env=None):return run(['/usr/bin/python3',*flags,str(root/'tools'/tool),*args],o,env)
 def record(label,res,expected,before=None,root=None):
  res.update(label=label,expected=expected,as_expected=(res['returncode']==0)==(expected=='pass'),explicit_refusal=(res['returncode']==2 and 'REFUSED:' in res['stderr']))
  if before is not None:
   res['fixture_preserved']=before==snap(root);require(res['fixture_preserved'],'Tool changed fixture: '+label)
  records.append(res);(o/'TEST_RESULTS.json').write_bytes(enc(records));return res
 def neg(label,mutate=None,args=None,tool='release60.py',flags=('-I','-S','-B')):
  root=fixture(label)
  if mutate:mutate(root)
  cmd=args(root) if callable(args) else args or ['check-inputs'];before=snap(root)
  return record(label,invoke(root,tool,cmd,flags), 'refuse',before,root)
 def buildargs(root):return ['--output-dir',str(o/('output-'+root.name))]
 base=fixture('clean');record('clean-frozen-authentication',invoke(base,'release60.py',['check-inputs']),'pass',snap(base),base)
 for flag in ('-O','-OO'):
  neg('release-optimization-'+flag[1:],flags=('-I','-S','-B',flag))
  neg('build-optimization-'+flag[1:],tool='build_report60.py',args=buildargs,flags=('-I','-S','-B',flag))
 for absent in ('-I','-S','-B'):
  flags=tuple(x for x in ('-I','-S','-B') if x!=absent)
  neg('release-missing-flag-'+absent[1:],flags=flags)
  neg('build-missing-flag-'+absent[1:],tool='build_report60.py',args=buildargs,flags=flags)
 target='science/physical/PROOF.md'
 mods={
 'missing-frozen-file':lambda d:(d/target).unlink(),
 'changed-frozen-file':lambda d:(d/target).write_bytes((d/target).read_bytes()+b'\n'),
 'extra-frozen-sibling':lambda d:((d/'science/unknown').mkdir(),(d/'science/unknown/item').write_text('extra')),
 'extra-root-empty-directory':lambda d:(d/'EMPTY_ROOT').mkdir(),
 'extra-frozen-file':lambda d:(d/'science/physical/EXTRA').write_text('extra'),
 'extra-frozen-directory':lambda d:(d/'science/physical/EMPTY_EXTRA').mkdir(),
 'missing-pin-map':lambda d:(d/'INPUT_PINS.json').unlink(),
 'malformed-pin-map':lambda d:(d/'INPUT_PINS.json').write_text('{'),
 'changed-pin-map':lambda d:(d/'INPUT_PINS.json').write_bytes((d/'INPUT_PINS.json').read_bytes()+b' '),
 'fifo-in-release':lambda d:os.mkfifo(d/'FIFO'),
 'symlink-in-release':lambda d:(d/'alias').symlink_to(d/'science/physical'),
 'symlink-frozen-file':lambda d:((d/target).rename(d/'target-save'),(d/target).symlink_to(d/'target-save')),
 'hardlink-frozen-file':lambda d:os.link(d/target,d/'hardlink'),
 }
 for label,mutate in mods.items():
  neg('release-'+label,mutate)
  neg('build-'+label,mutate,args=buildargs,tool='build_report60.py')
 for label,mutate in {
 'missing-toolchain-lock':lambda d:(d/'tools/BUILD_DEPENDENCIES_LOCK.json').unlink(),
 'changed-toolchain-lock':lambda d:(d/'tools/BUILD_DEPENDENCIES_LOCK.json').write_bytes((d/'tools/BUILD_DEPENDENCIES_LOCK.json').read_bytes()+b' '),
 'malformed-toolchain-lock':lambda d:(d/'tools/BUILD_DEPENDENCIES_LOCK.json').write_text('null'),
 'missing-standalone':lambda d:(d/'Report60.tex').unlink(),
 'changed-standalone':lambda d:(d/'Report60.tex').write_bytes((d/'Report60.tex').read_bytes()+b'\n'),
 'missing-manuscript':lambda d:(d/'manuscript/physical.tex').unlink(),
 'changed-manuscript':lambda d:(d/'manuscript/physical.tex').write_bytes((d/'manuscript/physical.tex').read_bytes()+b'\n'),
 'extra-manuscript':lambda d:(d/'manuscript/extra.tex').write_text('extra'),
 'extra-manuscript-directory':lambda d:(d/'manuscript/extra').mkdir(),
 'malformed-manuscript-pins':lambda d:(d/'manuscript/MANUSCRIPT_PINS.json').write_text('{'),
 }.items():neg('build-'+label,mutate,args=buildargs,tool='build_report60.py')
 # Each output test uses pre-existing, harmless fixtures and checks no source mutation.
 def outpath(root,kind):
  fresh=o/('output-'+root.name)
  if kind=='relative':return 'relative-output'
  if kind=='double-leading-slash':return '/'+str(fresh)
  if kind=='dot-component':return str(o)+'/./'+fresh.name
  if kind=='dotdot-component':return str(o)+'/missing/../'+fresh.name
  if kind=='double-slash':return str(o)+'//'+fresh.name
  if kind=='trailing-slash':return str(fresh)+'/'
  if kind=='inside-release':return str(root/'new-output')
  if kind=='ancestor':return str(root.parent)
  if kind=='missing-parent':return str(fresh/'new')
  if kind=='existing-file':fresh.write_text('preserve');return str(fresh)
  if kind=='existing-dir':fresh.mkdir();return str(fresh)
  if kind=='symlink-leaf':fresh.symlink_to(o/'missing-symlink-target');return str(fresh)
  if kind=='symlink-parent':fresh.symlink_to(o);return str(fresh/'new')
  if kind=='file-parent':fresh.write_text('preserve');return str(fresh/'new')
  raise RuntimeError(kind)
 for kind in ('relative','double-leading-slash','dot-component','dotdot-component','double-slash','trailing-slash','inside-release','ancestor','missing-parent','existing-file','existing-dir','symlink-leaf','symlink-parent','file-parent'):
  neg('release-output-'+kind,args=lambda d,k=kind:['manifest','--output',outpath(d,k)])
  neg('build-output-'+kind,args=lambda d,k=kind:['--output-dir',outpath(d,k)],tool='build_report60.py')
 # Root and tool alias rejection; aliases are outside copied release roots.
 for tool in ('release60.py','build_report60.py'):
  for mode in ('root-symlink','tool-symlink'):
   root=fixture(tool[:-3]+'-'+mode);alias=o/(root.name+'-alias')
   if mode=='root-symlink':alias.symlink_to(root);script=alias/'tools'/tool
   else:alias.symlink_to(root/'tools'/tool);script=alias
   args=['check-inputs'] if tool=='release60.py' else buildargs(root)
   record(tool+'-'+mode,run(['/usr/bin/python3','-I','-S','-B',str(script),*args],o),'refuse',snap(root),root)
 for dpi in ('0','71','201','-10'):
  neg('build-dpi-'+dpi,args=lambda d,x=dpi:buildargs(d)+['--render-dpi',x],tool='build_report60.py')
 # Create the trusted manifest over copied baseline and validate exact archive roundtrip.
 m=o/'baseline-manifest.json';res=invoke(base,'release60.py',['manifest','--output',str(m)]);record('manifest-clean',res,'pass');require(res['returncode']==0,'Manifest generation failed')
 shutil.copy2(m,base/'RELEASE_MANIFEST.json');pin=digest(m);before=snap(base)
 record('verify-clean',invoke(base,'release60.py',['verify','--manifest-sha256',pin]),'pass',before,base)
 for wrong in ('0'*64,pin.upper(),'xyz',pin+'0'):
  record('verify-invalid-pin-'+wrong[:8],invoke(base,'release60.py',['verify','--manifest-sha256',wrong]),'refuse',before,base)
 zips=[]
 for i in range(2):
  z=o/f'release-{i+1}.zip';res=invoke(base,'release60.py',['archive','--manifest-sha256',pin,'--output',str(z)]);record('archive-clean-'+str(i+1),res,'pass',before,base);require(res['returncode']==0,'Archive failed');zips.append(z)
 require(zips[0].read_bytes()==zips[1].read_bytes(),'Archives not identical')
 with zipfile.ZipFile(zips[0]) as z:
  entries=z.infolist();expected=['Report60/'+p.relative_to(base).as_posix() for p in sorted(base.rglob('*')) if p.is_file()]
  require(z.namelist()==expected,'Archive inventory differs');require(len(z.namelist())==len(set(z.namelist())),'Duplicate archive names')
  for e in entries:
   require(e.date_time==(2026,10,4,0,0,0),'Wrong archive timestamp');require(e.create_system==3 and e.external_attr>>16==stat.S_IFREG|0o644,'Wrong archive mode');require(not e.flag_bits&1,'Encrypted archive entry');require(not e.extra and not e.comment,'Extra ZIP metadata');require(z.read(e)==(base/e.filename.removeprefix('Report60/')).read_bytes(),'Archive bytes differ')
  extracted=o/'extracted';extracted.mkdir();z.extractall(extracted)
 restored=extracted/'Report60';record('verify-extracted',invoke(restored,'release60.py',['verify','--manifest-sha256',pin]),'pass',snap(restored),restored)
 z=o/'roundtrip.zip';record('archive-extracted',invoke(restored,'release60.py',['archive','--manifest-sha256',pin,'--output',str(z)]),'pass',snap(restored),restored);require(z.read_bytes()==zips[0].read_bytes(),'Roundtrip archive changed')
 # Malformed authenticated manifest copies are independently pinned to exercise schema checks.
 for label,change in {
 'missing-file':lambda v:v['files'].pop(next(iter(v['files']))),
 'extra-file':lambda v:v['files'].update({'ghost':{'bytes':0,'sha256':'0'*64}}),
 'negative-size':lambda v:v['files'][next(iter(v['files']))].update(bytes=-1),
 'boolean-size':lambda v:v['files'][next(iter(v['files']))].update(bytes=True),
 'bad-hash':lambda v:v['files'][next(iter(v['files']))].update(sha256='Z'*64),
 'extra-key':lambda v:v.update(unexpected=True),
 'bad-format':lambda v:v.update(format='wrong'),
 }.items():
  root=fixture('manifest-'+label);v=json.loads(m.read_bytes());change(v);(root/'RELEASE_MANIFEST.json').write_bytes(enc(v));record('manifest-'+label,invoke(root,'release60.py',['verify','--manifest-sha256',digest(root/'RELEASE_MANIFEST.json')]),'refuse',snap(root),root)
 for label,data in [('invalid-json',b'{'),('duplicate-key',b'{"format":"bad","format":"Report60 release manifest v1","files":{}}'),('array',b'[]'),('null',b'null')]:
  root=fixture('manifest-'+label);(root/'RELEASE_MANIFEST.json').write_bytes(data);record('manifest-'+label,invoke(root,'release60.py',['verify','--manifest-sha256',digest(root/'RELEASE_MANIFEST.json')]),'refuse',snap(root),root)
 (o/'source-after.json').write_bytes(enc(snap(r)));require(snap(r)==original,'Original source changed during audit')
 summary={'source':str(r),'tool_sha256':{t:digest(r/'tools'/t) for t in ('release60.py','build_report60.py')},'tests':len(records),'expected_refusals':sum(x['expected']=='refuse' for x in records),'observed_refusals':sum(x['returncode']!=0 for x in records),'mismatches':[x['label'] for x in records if not x['as_expected']],'nonexplicit_refusals':[x['label'] for x in records if x['expected']=='refuse' and x['returncode']!=0 and not x['explicit_refusal']],'source_preserved':True,'archive_sha256':digest(zips[0]),'archive_bytes':zips[0].stat().st_size,'roundtrip_byte_equal':True,'archive_entries':len(entries)}
 (o/'SUMMARY.json').write_bytes(enc(summary));print(enc(summary).decode())
if __name__=='__main__':main()
