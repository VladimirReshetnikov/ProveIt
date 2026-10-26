from pathlib import Path
import hashlib,json,os,shutil,subprocess,time
root=Path('/home/codex/.codex/worktrees/46be/Proofs')
out=Path(__file__).resolve().parent
lean=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean')
hashfile=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
paths=subprocess.check_output(['lake','env','printenv','LEAN_PATH'],cwd=root,text=True).strip().split(':')
shared=root/'.lake/build/lib/lean'
paths=[str(out/'lib')]+[p for p in paths if Path(p).resolve()!=shared.resolve()]
env=dict(os.environ,LEAN_PATH=':'.join(paths))
names=['ThirteenSharedSquares96','ThirteenSharedSquares96Checks']
inputs={'compiler':{'path':str(lean),'sha256':hashfile(lean)},'LEAN_PATH':paths,
        'prerequisites_sha256':hashfile(out/'prerequisites.json'),
        'sources':{n:hashfile(root/'Computability/DiophantineConsistency/Lean/DiophantineConsistency'/f'{n}.lean') for n in names}}
(out/'inputs.json').write_text(json.dumps(inputs,indent=2,sort_keys=True)+'\n')
records=[]
for name in names:
 if shutil.disk_usage(out).free<512*1024**2: raise SystemExit('512MiB reserve')
 source=root/'Computability/DiophantineConsistency/Lean/DiophantineConsistency'/f'{name}.lean'
 if hashfile(source)!=inputs['sources'][name]: raise SystemExit('source changed')
 obj=out/'lib/DiophantineConsistency'/f'{name}.olean'
 if obj.exists() or obj.is_symlink(): raise SystemExit('target already exists')
 command=[str(lean),'-M6000','-j1','-DElab.async=false','-o',str(obj),str(source)]
 log=out/f'{name}.log'; stats=out/f'{name}.time'
 start=time.monotonic()
 with log.open('wb') as f:
  completed=subprocess.run(['/usr/bin/time','-v','-o',str(stats)]+command,cwd=root,env=env,stdout=f,stderr=subprocess.STDOUT)
 item={'module':name,'command':command,'exit_code':completed.returncode,
       'seconds':time.monotonic()-start,'source':str(source),'source_sha256':hashfile(source),
       'log':str(log),'log_sha256':hashfile(log),'resource_log':str(stats),'resource_sha256':hashfile(stats)}
 if obj.exists(): item.update(object=str(obj),object_sha256=hashfile(obj),object_bytes=obj.stat().st_size)
 records.append(item);(out/'fresh.json').write_text(json.dumps(records,indent=2,sort_keys=True)+'\n')
 print(json.dumps(item),flush=True)
 if completed.returncode: raise SystemExit(completed.returncode)
