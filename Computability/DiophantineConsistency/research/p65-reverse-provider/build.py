from pathlib import Path
import json,os,subprocess,sys,time,hashlib
base=Path('/tmp/p65-reverse-provider'); manifest=json.loads((base/'manifest.json').read_text())
if manifest['missing']:raise SystemExit('Missing source modules: '+repr(manifest['missing']))
env=os.environ.copy();env['LEAN_PATH']=':'.join([str(base/'lib'),'/tmp','/tmp/trace74-direct-four-block-1zltaw2f/lib','/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib'])
logs=base/'logs';logs.mkdir(exist_ok=True)
subprocess.run([sys.executable, '/tmp/p65_check_reverse_manifest.py'],check=True)
results_path=base/'results.json'
results=json.loads(results_path.read_text()) if results_path.exists() else {}
for index,entry in enumerate(manifest['order'],1):
 name=entry['module'];obj=base/'lib'/(name.replace('.','/')+'.olean');obj.parent.mkdir(parents=True,exist_ok=True)
 if obj.exists() and name in results and results[name]['object_sha256']==hashlib.sha256(obj.read_bytes()).hexdigest() and results[name]['shim_sha256']==entry['shim_sha256']:
  print(f'{index}/{len(manifest["order"])} cached {name}',flush=True);continue
 cmd=['timeout','300','lean','-M6000','-j1','-DElab.async=false','--root='+str(base/'src'),entry['shim'],'-o',str(obj)]
 print(f'{index}/{len(manifest["order"])} compile {name}',flush=True);start=time.monotonic()
 result=subprocess.run(cmd,env=env,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
 log=logs/(name+'.txt');log.write_text('command: '+' '.join(cmd)+'\n'+f'exit: {result.returncode}, elapsed: {time.monotonic()-start:.2f}s\n'+result.stdout)
 if result.returncode:
  print(f'FAIL {name}: exit {result.returncode}, log {log}',flush=True)
  print(result.stdout[-5000:],flush=True);sys.exit(result.returncode)
 results[name]={'object':str(obj),'object_sha256':hashlib.sha256(obj.read_bytes()).hexdigest(),'shim_sha256':entry['shim_sha256'],'log':str(log),'log_sha256':hashlib.sha256(log.read_bytes()).hexdigest()}
 results_path.write_text(json.dumps(results,indent=2)+'\n')
print('All reverse provider modules built.',flush=True)
