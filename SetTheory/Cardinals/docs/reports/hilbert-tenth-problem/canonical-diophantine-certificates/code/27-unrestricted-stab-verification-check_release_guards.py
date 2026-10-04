"""Fresh nonmutating negative tests of the Report54 release entry point."""
import hashlib,json,pathlib,subprocess,sys,tempfile
root=pathlib.Path(__file__).resolve().parent.parent
script=root/'release.py'
def snapshot():
 return {str(p.relative_to(root)):(p.stat().st_mtime_ns, p.stat().st_mode, hashlib.sha256(p.read_bytes()).hexdigest() if p.is_file() else None) for p in [root]+sorted(root.rglob('*'))}
before=snapshot();cases=[]
with tempfile.TemporaryDirectory(prefix='report54-release-guards-') as raw:
 t=pathlib.Path(raw);link=t/'link';link.symlink_to(t,target_is_directory=True)
 tests=[('Python isolation required',[sys.executable,str(script),'build-pdf','--draft','--output',str(t/'unused1')]),('Optimized release execution rejected',[sys.executable,'-I','-O',str(script),'build-pdf','--draft','--output',str(t/'unused2')]),('Existing output rejected',[sys.executable,'-I',str(script),'build-pdf','--draft','--output',str(t)]),('Output within bundle rejected',[sys.executable,'-I',str(script),'build-pdf','--draft','--output',str(root/'unused-output')]),('Symlink output parent rejected',[sys.executable,'-I',str(script),'build-pdf','--draft','--output',str(link/'unused3')]),('Missing output parent rejected',[sys.executable,'-I',str(script),'build-pdf','--draft','--output',str(t/'missing'/'unused4')])]
 for name,command in tests:
  result=subprocess.run(command,capture_output=True,text=True,timeout=30)
  if result.returncode==0:raise RuntimeError('Accepted negative case '+name)
  cases.append({'case':name,'rejected':True,'error':result.stderr.strip().splitlines()[-1]})
 if any((t/x).exists() for x in ['unused1','unused2','unused3','missing']):raise RuntimeError('Negative test wrote output')
if snapshot()!=before:raise RuntimeError('Negative guard tests changed bundle')
receipt={'status':'PASS','negative_cases':cases,'no_output_created':True,'release_bytes_modes_mtimes_unchanged':True,'program_sha256':hashlib.sha256(script.read_bytes()).hexdigest()}
print(json.dumps(receipt,sort_keys=True,indent=2))
