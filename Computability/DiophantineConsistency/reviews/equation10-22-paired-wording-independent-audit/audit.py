#!/usr/bin/env python3
"""Independently audit the final AQ22 wording refresh and PDF builds."""
import hashlib,json,shutil,subprocess,sys,tempfile
from pathlib import Path
if not __debug__:raise RuntimeError('optimized Python is unsupported')
here=Path(__file__).resolve().parent;root=here.parents[1];rel='Computability/DiophantineConsistency/research/adaptive-square-sums22-degree10/'
task=root/'research/adaptive-square-sums22-degree10';old=root/'reviews/equation10-22-wording-independent-audit/receipt.json'
art=root/'reviews/ipra-aq22-historical-pair-independent-audit';trial=root/'reviews/ipra-aq22-historical-pair-terminal'
H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest();J=lambda p:json.loads(Path(p).read_text())
files=[task/x for x in ('build_display.py','equation10-22.tex','equation10-22.pdf','candidate.json')]
files += [root/'equation.tex',old,art/'receipt.json',art/'terminal-observation.json',trial/'pair-state.json',trial/'pair-observation.json',Path(__file__).resolve()]
before_hashes={str(p.resolve()):H(p) for p in files};prior=J(old);audit=J(art/'receipt.json');terminal=J(art/'terminal-observation.json');run=J(trial/'pair-observation.json')
assert prior['status']=='PASS_AQ22_WORDING_AUDIT'
assert H(task/'candidate.json')=='1266b143c5512351739ea2c71fc8e0b8b0e5cecc599392f128c0803ff78ce106'
assert audit['status']=='PASS_INDEPENDENT_AQ22_PAIRED_ARTIFACT_AUDIT' and audit['added_modules']==37 and audit['expected_diagnostics']==94
assert terminal['observed_exit_code']==0 and terminal['receipt_sha256']==H(art/'receipt.json')
assert run['observed_exit_code']==0 and run['pair_state_sha256']==H(trial/'pair-state.json')==audit['pair_state_sha256']
oldtext=b'substitution identities. A historical author-only Lean run established the\nwitness transport and an internal intuitionistic PRA equivalence to a\ntranslated consistency sentence. A paired replay remains pending. No'
newtext=b'substitution identities. Historical paired Lean runs compiled the witness\ntransport and an internal intuitionistic PRA equivalence to a translated\nconsistency sentence. No'
for name in ('build_display.py','equation10-22.tex'):
    base=subprocess.run(['git','show','fc8c78438c:'+rel+name],cwd=root,check=True,capture_output=True).stdout
    final=subprocess.run(['git','show','4202c66a54:'+rel+name],cwd=root,check=True,capture_output=True).stdout
    matches=[v for k,v in prior['inputs_sha256'].items() if k.endswith('/'+name)]
    assert len(matches)==1 and hashlib.sha256(base).hexdigest()==matches[0]
    assert base.count(oldtext)==1 and final==base.replace(oldtext,newtext,1)
    assert (task/name).read_bytes()==final
pdfgit=subprocess.run(['git','show','4202c66a54:'+rel+'equation10-22.pdf'],cwd=root,check=True,capture_output=True).stdout
assert pdfgit==(task/'equation10-22.pdf').read_bytes()
assert H(task/'equation10-22.pdf')=='310f638eff89ab3b9776756fac3a8b4984e2feb94c838eeb6508444e8c177363'
pdfs=[]
with tempfile.TemporaryDirectory(prefix='aq22-wording-review-') as tmp:
    for runname in ('first','second'):
        d=Path(tmp)/runname/'research/adaptive-square-sums22-degree10';d.mkdir(parents=True)
        for name in ('build_display.py','candidate.json'):shutil.copy2(task/name,d/name)
        shutil.copy2(root/'equation.tex',d.parents[1]/'equation.tex')
        p=subprocess.run([sys.executable,str(d/'build_display.py')],cwd=d,capture_output=True,text=True,timeout=180)
        assert p.returncode==0 and 'two warning-free identical PDF builds' in p.stdout,(p.returncode,p.stdout,p.stderr)
        assert (d/'equation10-22.tex').read_bytes()==(task/'equation10-22.tex').read_bytes()
        pdfs.append(H(d/'equation10-22.pdf'))
assert pdfs==[H(task/'equation10-22.pdf')]*2
assert {str(p.resolve()):H(p) for p in files}==before_hashes
result={'status':'PASS_AQ22_PAIRED_WORDING_AUDIT','inputs_sha256':before_hashes,'baseline_commit':'fc8c78438c','reviewed_commit':'4202c66a54',
        'comparison':'only the status paragraph differs in generator and TeX','candidate_sha256':H(task/'candidate.json'),
        'generator_runs':2,'generator_builds_per_run':2,'generator_pdf_sha256':pdfs,
        'scope':'Historical matched AQ22 artifact evidence; no formal PDF-to-Lean identification. The decoder/rank recipe remains manually transcribed.'}
out=here/'receipt.json'
if out.exists():raise ValueError('refusing to overwrite receipt')
out.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n');print(result['status'],H(out),pdfs[0])
