#!/usr/bin/env python3
"""Independently audit the final AQ17 wording refresh and PDF builds."""
import hashlib,json,shutil,subprocess,sys,tempfile
from pathlib import Path
if not __debug__:raise RuntimeError('optimized Python is unsupported')
here=Path(__file__).resolve().parent;root=here.parents[1];rel='Computability/DiophantineConsistency/research/aq22-positive-binding-survey/'
task=root/'research/aq22-positive-binding-survey';old=root/'reviews/equation32-17-independent-audit/receipt.json'
art=root/'reviews/ipra-aq17-guarded-author-independent-audit';trial=root/'reviews/ipra-aq17-guarded-author'
H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest();J=lambda p:json.loads(Path(p).read_text())
files=[task/x for x in ('build_display17.py','equation32-17.tex','equation32-17.pdf','candidate17.json')]
files += [root/'equation.tex',old,art/'receipt.json',art/'terminal-observation.json',trial/'state.json',trial/'terminal-observation.json',Path(__file__).resolve()]
before_hashes={str(p.resolve()):H(p) for p in files};prior=J(old);audit=J(art/'receipt.json');terminal=J(art/'terminal-observation.json');run=J(trial/'terminal-observation.json')
assert prior['status']=='PASS_INDEPENDENT_AQ17_DISPLAY'
assert H(task/'candidate17.json')=='760b9e7babbb559b7175344915456fdc3d9bd8ce85382873d4915faf2cd76d81'
assert audit['status']=='PASS_INDEPENDENT_AQ17_AUTHOR_ARTIFACT_AUDIT' and audit['added_modules']==44 and audit['added_direct_import_edges']==123
assert terminal['observed_exit_code']==0 and terminal['receipt_sha256']==H(art/'receipt.json')
assert run['observed_exit_code']==0 and run['state_sha256']==H(trial/'state.json')==audit['trial_state_sha256']
oldtext=b'substitution identities. An exploratory Lean run compiled witness transport\nand an intuitionistic PRA equivalence to a translated consistency sentence;\na guarded replay remains pending. No'
newtext=b'substitution identities. A historical guarded Lean author run compiled witness\ntransport and an intuitionistic PRA equivalence to a translated consistency\nsentence; a paired replay remains pending. No'
for name in ('build_display17.py','equation32-17.tex'):
    base=subprocess.run(['git','show','39f2c60c9d:'+rel+name],cwd=root,check=True,capture_output=True).stdout
    final=subprocess.run(['git','show','702a31c646:'+rel+name],cwd=root,check=True,capture_output=True).stdout
    matches=[v for k,v in prior['inputs_sha256'].items() if k.endswith('/'+name)]
    assert len(matches)==1 and hashlib.sha256(base).hexdigest()==matches[0]
    assert base.count(oldtext)==1 and final==base.replace(oldtext,newtext,1)
    assert (task/name).read_bytes()==final
pdfgit=subprocess.run(['git','show','702a31c646:'+rel+'equation32-17.pdf'],cwd=root,check=True,capture_output=True).stdout
assert pdfgit==(task/'equation32-17.pdf').read_bytes()
assert H(task/'equation32-17.pdf')=='9e11ae20b1b59f6480e52dc1c7055493ba8990776ecc22f84ed0adcc59828e54'
pdfs=[]
with tempfile.TemporaryDirectory(prefix='aq17-wording-review-') as tmp:
    for runname in ('first','second'):
        d=Path(tmp)/runname/'research/aq22-positive-binding-survey';d.mkdir(parents=True)
        for name in ('build_display17.py','candidate17.json'):shutil.copy2(task/name,d/name)
        shutil.copy2(root/'equation.tex',d.parents[1]/'equation.tex')
        p=subprocess.run([sys.executable,str(d/'build_display17.py')],cwd=d,capture_output=True,text=True,timeout=180)
        assert p.returncode==0 and 'two warning-free identical PDF builds' in p.stdout,(p.returncode,p.stdout,p.stderr)
        assert (d/'equation32-17.tex').read_bytes()==(task/'equation32-17.tex').read_bytes()
        pdfs.append(H(d/'equation32-17.pdf'))
assert pdfs==[H(task/'equation32-17.pdf')]*2
assert {str(p.resolve()):H(p) for p in files}==before_hashes
result={'status':'PASS_AQ17_WORDING_AUDIT','inputs_sha256':before_hashes,'baseline_commit':'39f2c60c9d','reviewed_commit':'702a31c646',
        'comparison':'only the status paragraph differs in generator and TeX','candidate_sha256':H(task/'candidate17.json'),
        'generator_runs':2,'generator_builds_per_run':2,'generator_pdf_sha256':pdfs,
        'scope':'Historical guarded author-only artifact evidence; no paired AQ17 replay or formal PDF-to-Lean identification. The decoder/rank recipe remains manually transcribed.'}
out=here/'receipt.json'
if out.exists():raise ValueError('refusing to overwrite receipt')
out.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n');print(result['status'],H(out),pdfs[0])
