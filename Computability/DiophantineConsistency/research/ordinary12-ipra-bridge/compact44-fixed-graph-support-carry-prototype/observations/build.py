import os,subprocess,json,pathlib,hashlib,sys
root=pathlib.Path('/tmp/compact44-graph-support-join-01')
names=['CompactSymbolicGraphSaturation','CompactSameWitnessSaturation2','CompactPositionIncrement','CompactPositionGraph','CleanGeometry','CleanMaskClasses','CleanModelSupport']
env={'PATH':'/usr/bin:/bin','HOME':'/home/codex','LEAN_PATH':str(root/'lib')+':/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib'}
lean='/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean';runs=[]
for name in names:
 src=root/(name+'.lean');output=root/'lib/DiophantineConsistency'/(name+'.olean');log=root/(name+'.log')
 cmd=['timeout','120',lean,'-M3000','-j1','-DElab.async=false','--root='+str(root),str(src),'-o',str(output)]
 with log.open('wb') as f:p=subprocess.run(cmd,env=env,stdout=f,stderr=subprocess.STDOUT)
 content=log.read_text();runs.append({'module':name,'exit':p.returncode,'source_sha256':hashlib.sha256(src.read_bytes()).hexdigest(),'log_sha256':hashlib.sha256(log.read_bytes()).hexdigest(),'warning':'warning:' in content,'sorryAx':'sorryAx' in content});print(name,p.returncode,flush=True)
 if p.returncode or 'warning:' in content or 'sorryAx' in content:break
(root/'build-observation.json').write_text(json.dumps(runs,indent=2)+'\n')
sys.exit(0 if len(runs)==len(names) and not runs[-1]['exit'] and not runs[-1]['warning'] and not runs[-1]['sorryAx'] else 1)
