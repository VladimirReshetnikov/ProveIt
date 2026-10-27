from pathlib import Path
import json,hashlib,os,shutil,subprocess,time,re
R=Path('/home/codex/.codex/worktrees/46be/Proofs');p=Path(Path('/tmp/command-circuitperm222-root-author-location.txt').read_text());sha=lambda f:hashlib.sha256(Path(f).read_bytes()).hexdigest()
def rec(f):return dict(path=str(f),sha256=sha(f))
def check(e):assert sha(e['path'])==e['sha256'],e['path']
def save(f,d):f.write_text(json.dumps(d,indent=2)+'\n')
i=json.loads((p/'inputs.json').read_text());previous=p/'attempt-1793073199808937621/RESULT.json';s0=json.loads(previous.read_text());main=s0['records'][0];assert main['exit_code']==0
for k in['source','snapshot','log','object']:check(main[k])
for e in i['pins']:check(e)
assert shutil.disk_usage(p).free>=512*1024**2;d=p/('attempt-'+str(time.time_ns()));d.mkdir();n='ArithmeticCommandCircuitPerm222Checks';src=R/'Computability/DiophantineConsistency/Lean/DiophantineConsistency'/(n+'.lean');snap=d/(n+'.lean');shutil.copyfile(src,snap);out=p/'lib/DiophantineConsistency'/(n+'.olean');assert not out.is_symlink()and not out.exists();log=d/(n+'.log');timing=d/(n+'.time');env=dict(os.environ,LEAN_PATH=i['lean_path'],LEAN_NUM_THREADS='1');env.pop('LEAN_SRC_PATH',None);cmd=[i['compiler']['path'],'-M6000','-j1','-DElab.async=false','-o',str(out),str(src)];t=time.monotonic()
with log.open('w')as f:code=subprocess.run(['/usr/bin/time','-v','-o',str(timing),*cmd],cwd=R,env=env,stdout=f,stderr=subprocess.STDOUT).returncode
r=dict(module='DiophantineConsistency.'+n,source=rec(src),snapshot=rec(snap),command=cmd,exit_code=code,seconds=time.monotonic()-t,log=rec(log),timing=rec(timing),object=rec(out)if code==0 else None);s=dict(status='PASS'if code==0 else'FAILED',inputs=rec(p/'inputs.json'),driver=rec(__file__),inherited_main_result=rec(previous),records=[main,r],private=str(p));save(d/'RESULT.json',s);print(json.dumps(r),flush=True)
assert code==0,log.read_text();assert sha(src)==sha(snap);r['axiom_reports']=re.findall(r"'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)",log.read_text());assert len(r['axiom_reports'])==9
for title,ax in r['axiom_reports']:assert set(re.findall(r'[A-Za-z][A-Za-z.]*',ax))<={'propext','Classical.choice','Quot.sound'}
assert not re.search(r'\b(?:warning|error):',log.read_text())
for e in i['pins']:check(e)
save(d/'RESULT.json',s);save(p/'LATEST.json',rec(d/'RESULT.json'));print('PASS '+str(d),flush=True)
