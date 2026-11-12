from pathlib import Path
import hashlib,json,random,subprocess,sys
p=Path(__file__).resolve().parent;D=p.parents[1];s=(p/'RingParentTo88.lean').read_text()
for t in ('project_extend','Ring88ToParentDraft.main_eval','Ring88ToParentDraft.aux_eval','Ring88ToParentDraft.strong_eval','theorem first_eval','v 7,sigma','v 12,t'):assert t in s
r=D/'research/ordinary14-88-parent-ring-client-draft';x=subprocess.run([sys.executable,'-I','-S','-B',str(r/'check_source.py')],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=60);assert not x.stderr and x.stdout==(r/'observation.json').read_bytes()
rng=random.Random(131488)
for _ in range(500):
 v=[rng.randrange(-5,6) for _ in range(13)];sigma=rng.randrange(-5,6);t=rng.randrange(-5,6)
 w=v[:];w[8]=sigma;w.append(t);back=w[:13];back[8]=v[8]
 assert back==v
print(json.dumps({'slot_controls':500,'lean_run':False,'source_sha256':hashlib.sha256((p/'RingParentTo88.lean').read_bytes()).hexdigest()},sort_keys=True,indent=2))
