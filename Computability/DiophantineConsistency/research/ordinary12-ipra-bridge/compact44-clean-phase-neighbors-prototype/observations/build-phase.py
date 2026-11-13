import os,subprocess,json,pathlib,hashlib,sys
root=pathlib.Path('/tmp/compact44-graph-support-join-01');names=['CleanPhaseChoice','CleanTargetPhase'];runs=[]
env={'PATH':'/usr/bin:/bin','HOME':'/home/codex','LEAN_PATH':str(root/'lib')+':/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib'}
lean='/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean'
for name in names:
 src=root/(name+'.lean');out=root/'lib/DiophantineConsistency'/(name+'.olean');log=root/(name+'.log')
 with log.open('wb') as f:p=subprocess.run(['timeout','120',lean,'-M3000','-j1','-DElab.async=false','--root='+str(root),str(src),'-o',str(out)],env=env,stdout=f,stderr=subprocess.STDOUT)
 s=log.read_text();runs.append({'module':name,'exit':p.returncode,'source_sha256':hashlib.sha256(src.read_bytes()).hexdigest(),'log_sha256':hashlib.sha256(log.read_bytes()).hexdigest(),'warning':'warning:' in s,'sorryAx':'sorryAx' in s});print(name,p.returncode,flush=True)
 if p.returncode or 'warning:' in s or 'sorryAx' in s:break
(root/'build-phase-observation.json').write_text(json.dumps(runs,indent=2)+'\n')
sys.exit(0 if len(runs)==len(names) and not runs[-1]['exit'] and not runs[-1]['warning'] and not runs[-1]['sorryAx'] else 1)
