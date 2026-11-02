#!/usr/bin/env python3
"""Independent wording-only and reproducible-PDF review; not PDF semantics."""
import hashlib,json,shutil,subprocess,sys,tempfile
from pathlib import Path
if not __debug__:raise RuntimeError('optimized Python is unsupported')
here=Path(__file__).resolve().parent;root=here.parents[1];rel='Computability/DiophantineConsistency/research/aq17-positive-signed-binding/'
task=root/'research/aq17-positive-signed-binding';prior=root/'reviews/equation32-16-wording-independent-audit/receipt.json';pair=root/'reviews/ipra-aq16-historical-retry-pair-terminal'
H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest();J=lambda p:json.loads(Path(p).read_text())
files=[task/x for x in ('build_display16.py','equation32-16.tex','equation32-16.pdf','candidate16.json')]+[root/'equation.tex',prior,pair/'outer-terminal-observation.json',pair/'pair-state.json',Path(__file__).resolve()]
before={str(p.resolve()):H(p) for p in files};p=J(prior);outer=J(pair/'outer-terminal-observation.json');state=J(pair/'pair-state.json')
assert p['status']=='PASS_AQ16_WORDING_AUDIT' and H(task/'candidate16.json')=='a7d6f8a618a810b37eb7a9de6bd92ceb73bd6351971fdd39045bf95f8bf9edac'
assert outer['observed_exit_code']==0 and outer['session_id']==2984 and outer['pair_state_sha256']==H(pair/'pair-state.json')=='e37d8bb577d7a2188929a9d8044eb48898c2f76191ce77d33237c149ae3e1e7b'
assert state['status']=='MATCHED_SELECTIVE_PASS' and state['comparison']['affected_modules']==52
old=b'substitution identities, using the actual fixed value of beta. An exploratory\nLean run compiled witness transport and an intuitionistic PRA equivalence to\na translated consistency sentence; a paired replay remains pending. No'
new=b'substitution identities, using the actual fixed value of beta. Historical paired\nLean runs compiled witness transport and an intuitionistic PRA equivalence to\na translated consistency sentence. No'
for name in ('build_display16.py','equation32-16.tex'):
 oldbytes=subprocess.check_output(['git','show','7d72057118:'+rel+name],cwd=root);newbytes=subprocess.check_output(['git','show','a76a74fb49:'+rel+name],cwd=root)
 assert oldbytes.count(old)==1 and newbytes==oldbytes.replace(old,new,1) and (task/name).read_bytes()==newbytes
pdfgit=subprocess.check_output(['git','show','a76a74fb49:'+rel+'equation32-16.pdf'],cwd=root);assert pdfgit==(task/'equation32-16.pdf').read_bytes()
assert H(task/'equation32-16.pdf')=='6be4ca4615ff04be45dd76d8a251186de114047c62db691fee49fd0880b943db'
pdfs=[]
with tempfile.TemporaryDirectory(prefix='aq16-paired-wording-review-') as tmp:
 for label in ('first','second'):
  d=Path(tmp)/label/'research/aq17-positive-signed-binding';d.mkdir(parents=True)
  for name in ('build_display16.py','candidate16.json'):shutil.copy2(task/name,d/name)
  shutil.copy2(root/'equation.tex',d.parents[1]/'equation.tex')
  r=subprocess.run([sys.executable,str(d/'build_display16.py')],cwd=d,capture_output=True,text=True,timeout=180)
  assert r.returncode==0 and 'two warning-free identical PDF builds' in r.stdout,(r.returncode,r.stdout,r.stderr)
  assert (d/'equation32-16.tex').read_bytes()==(task/'equation32-16.tex').read_bytes();pdfs.append(H(d/'equation32-16.pdf'))
assert pdfs==[H(task/'equation32-16.pdf')]*2 and before=={str(p.resolve()):H(p) for p in files}
out={'status':'PASS_AQ16_PAIRED_WORDING_AUDIT','inputs_sha256':before,'baseline_commit':'7d72057118','reviewed_commit':'a76a74fb49','pdf_sha256':pdfs[0],'generator_runs':2,'builds_per_run':2,'scope':'Finite wording and presentation audit of a historical paired result; no Lean proof of PDF decoder or arbitrary Con(ZFC) identification.'};path=here/'receipt.json'
if path.exists():raise ValueError('refusing overwrite')
path.write_text(json.dumps(out,sort_keys=True,indent=2)+'\n');print(out['status'],H(path))
