from pathlib import Path
import hashlib,json,shutil,subprocess,tempfile,time
R=Path('/home/codex/.codex/worktrees/46be/Proofs');B=R/'Computability/DiophantineConsistency';P=B/'research/thirteen-scaled-norm-syzygy86'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def rec(p):return dict(path=str(p),sha256=sha(p))
def save(p,d):p.write_text(json.dumps(d,indent=2)+'\n')
expected={'audit.py':'4ea291f7a2680be91cd48a896ade395139fbaae5ecd8a0857636aa3be0d1535b','PROOF.md':'609fcdece2ba042a1fa0c5cf73783a8b76cda4d2238e6e1fcf1a28464bd6adf7'}
for f,h in expected.items():assert sha(P/f)==h,f
inputs=[P/f for f in ['audit.py','PROOF.md','polynomial.json','CERTIFICATE.json']]
inputs += [B/'Lean/DiophantineConsistency'/n for n in ['ThirteenScaledNormSyzygy86.lean','ThirteenScaledNormSyzygy86Checks.lean','ThirteenSecondFirstNormCorrections.lean']]
inputs += [B/'research/thirteen-second-first-norm-corrections'/n for n in ['polynomial88.json','CERTIFICATE.json']]
inputs += [B/'research/padding-staircase-independent'/n for n in ['PROOF.md','certificate.json','coefficients.json']]
g=json.loads((P/'polynomial.json').read_text())
inputs += [P/g['coefficient_binding']['path']/e['file']for e in g['coefficient_binding']['ports'].values()]
pins=[rec(p)for p in inputs];assert len(pins)==16
out=Path(tempfile.mkdtemp(prefix='thirteen-syzygy86-finite-root-'));Path('/tmp/thirteen-syzygy86-finite-root-location.txt').write_text(str(out))
s=dict(status='RUNNING',scope='Independent normal and optimized executions of the fully read frozen finite auditor only; no Lean build or mathematical consistency conclusion.',private=str(out),driver=rec(__file__),auditor=rec(P/'audit.py'),source_snapshot=subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip(),pins=pins,records=[]);save(out/'ROOT.json',s)
try:
 for mode in ['normal','optimized']:
  assert shutil.disk_usage(out).free>=512*1024**2
  cmd=['python']+(['-O']if mode=='optimized'else[])+[str(P/'audit.py')];log=out/(mode+'.txt');timing=out/(mode+'.time');start=time.time()
  with log.open('w')as f:code=subprocess.run(['/usr/bin/time','-v','-o',str(timing),*cmd],cwd=R,stdout=f,stderr=subprocess.STDOUT).returncode
  e=dict(mode=mode,command=cmd,exit_code=code,seconds=time.time()-start,log=rec(log),timing=rec(timing));s['records'].append(e);save(out/'ROOT.json',s);print(json.dumps(e),flush=True);assert code==0
  d=json.loads(log.read_text());assert d['status']=='PASS'and(d['variables'],d['operations'],d['degree'],d['raw_port_bytes'])==(13,178,86,47313);assert d['certificate_sha256']==sha(P/'CERTIFICATE.json');e['summary']=d
  for pin in pins:assert sha(pin['path'])==pin['sha256'],pin['path']
  save(out/'ROOT.json',s)
 assert (out/'normal.txt').read_bytes()==(out/'optimized.txt').read_bytes()
 s['status']='PASS';s['normal_optimized_bytes_identical']=True;s['free_bytes_after']=shutil.disk_usage(out).free;save(out/'ROOT.json',s);print('PASS '+str(out),flush=True)
except BaseException as exc:
 s['status']='FAILED';s['failure']=repr(exc);save(out/'ROOT.json',s);raise
