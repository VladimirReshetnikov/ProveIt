from pathlib import Path
import json,hashlib,os,re,shutil,subprocess,tempfile,time
R=Path('/home/codex/.codex/worktrees/46be/Proofs');V=R/'Computability/DiophantineConsistency/reviews';mp=V/'native-adaptive-power-recovery-replay.json';sha=lambda f:hashlib.sha256(Path(f).read_bytes()).hexdigest()
def check(e):assert sha(e['path'])==e['sha256'],e['path']
def rec(f):return dict(path=str(f),sha256=sha(f))
def save(f,d):f.write_text(json.dumps(d,indent=2)+'\n')
assert sha(mp)=='480e34f77e08ca6d26a9c1ead6839a58baec7b36e9ac8c11f0019aba0384d056';d=json.loads(mp.read_text());assert d['status']=='PASS'
assert len(d['artifact_texts'])==34
for e in d['artifact_texts']:check(e)
for k in ['driver','inputs_record','state_record']:check(d[k])
i=d['inputs'];assert len(i['selected_custom'])==30 and len(i['external_boundary'])==22
pins=[rec(mp),d['driver'],d['inputs_record'],d['state_record'],*i['pins']]
for e in pins:check(e)
p=Path(tempfile.mkdtemp(prefix='native-adaptive-power-root-'));lib=p/'lib';lib.mkdir()
for e in i['selected_custom']:
 check(e['source']);check(e['object']);q=lib/Path(*e['module'].split('.')).with_suffix('.olean');q.parent.mkdir(parents=True,exist_ok=True);q.symlink_to(e['object']['path'])
env=dict(os.environ,LEAN_PATH=':'.join([str(lib),*i['LEAN_PATH'][1:]]),LEAN_NUM_THREADS='1');env.pop('LEAN_SRC_PATH',None);s=dict(status='RUNNING',private=str(p),author_packet=rec(mp),driver=rec(__file__),pins=pins,records=[],counts=dict(custom=30,external=22,external_companions=66));save(p/'ROOT.json',s);Path('/tmp/native-adaptive-power-root-location.txt').write_text(str(p))
for e in d['completed']:
 assert shutil.disk_usage('/tmp').free>=512*1024**2
 for k in ['source','snapshot','log','timing','object']:check(e[k])
 n=e['module'];out=lib/Path(*n.split('.')).with_suffix('.olean');out.parent.mkdir(parents=True,exist_ok=True);assert not out.exists()and not out.is_symlink();log=p/(n+'.txt');timing=p/(n+'.time');cmd=[i['compiler']['path'],'-M6000','-j1','-DElab.async=false','-o',str(out),e['source']['path']];start=time.monotonic()
 with log.open('w')as f:code=subprocess.run(['/usr/bin/time','-v','-o',str(timing),*cmd],cwd=R,env=env,stdout=f,stderr=subprocess.STDOUT).returncode
 x=dict(module=n,source=e['source'],command=cmd,exit_code=code,seconds=time.monotonic()-start,log=rec(log),timing=rec(timing),object=rec(out)if code==0 else None);s['records'].append(x);save(p/'ROOT.json',s);print(json.dumps(x),flush=True)
 assert code==0,log.read_text();x['matches_author']=x['object']['sha256']==e['object']['sha256'];assert x['matches_author'];reports=re.findall(r"'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)",log.read_text());x['axiom_reports']=reports
 for title,ax in reports:assert set(re.findall(r'[A-Za-z][A-Za-z.]*',ax))<={'propext','Classical.choice','Quot.sound'}
 assert not re.search(r'\b(?:error|warning):|sorryAx',log.read_text())
for e in pins:check(e)
assert sum(len(e['axiom_reports'])for e in s['records'])==14 and Path(s['records'][0]['log']['path']).read_text()=='';s['status']='PASS';save(p/'ROOT.json',s);print('PASS '+str(p),flush=True)
