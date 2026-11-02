#!/usr/bin/env python3
"""Independently audit the final AQ16 wording refresh and PDF builds."""
import hashlib,json,shutil,subprocess,sys,tempfile
from pathlib import Path
if not __debug__:raise RuntimeError('optimized Python is unsupported')
here=Path(__file__).resolve().parent;root=here.parents[1];rel='Computability/DiophantineConsistency/research/aq17-positive-signed-binding/'
task=root/'research/aq17-positive-signed-binding';old=root/'reviews/equation32-16-independent-audit/receipt.json'
obs=root/'research/aq16-witness-transport/exploratory/observations.json'
H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest();J=lambda p:json.loads(Path(p).read_text())
files=[task/x for x in ('build_display16.py','equation32-16.tex','equation32-16.pdf','candidate16.json')]
files += [root/'equation.tex',old,obs,Path(__file__).resolve()]
before_hashes={str(p.resolve()):H(p) for p in files};prior=J(old);observation=J(obs)
assert prior['status']=='PASS_INDEPENDENT_AQ16_DISPLAY'
assert H(task/'candidate16.json')=='a7d6f8a618a810b37eb7a9de6bd92ceb73bd6351971fdd39045bf95f8bf9edac'==observation['candidate_sha256']
rows={r['module']:r for r in observation['rows']}
assert {'AdaptiveAQ16Transport','AdaptiveAQ16','IPRAAQ16Native','IPRAStandardAQ16'}<=set(rows)
assert all(rows[n]['observed_exit_code']==0 for n in ('AdaptiveAQ16Transport','AdaptiveAQ16','IPRAAQ16Native','IPRAStandardAQ16'))
oldtext=b'substitution identities, using the actual fixed value of beta. A Lean\nwitness-transport theorem and an internal intuitionistic PRA equivalence for\nthis candidate remain open. No'
newtext=b'substitution identities, using the actual fixed value of beta. An exploratory\nLean run compiled witness transport and an intuitionistic PRA equivalence to\na translated consistency sentence; a paired replay remains pending. No'
for name in ('build_display16.py','equation32-16.tex'):
    base=subprocess.run(['git','show','007aeb301b:'+rel+name],cwd=root,check=True,capture_output=True).stdout
    final=subprocess.run(['git','show','7d72057118:'+rel+name],cwd=root,check=True,capture_output=True).stdout
    matches=[v for k,v in prior['inputs_sha256'].items() if k.endswith('/'+name)]
    assert len(matches)==1 and hashlib.sha256(base).hexdigest()==matches[0]
    assert base.count(oldtext)==1 and final==base.replace(oldtext,newtext,1)
    assert (task/name).read_bytes()==final
pdfgit=subprocess.run(['git','show','7d72057118:'+rel+'equation32-16.pdf'],cwd=root,check=True,capture_output=True).stdout
assert pdfgit==(task/'equation32-16.pdf').read_bytes()
assert H(task/'equation32-16.pdf')=='73a337169a75eb647a7e7f4a3f8ae9d159732df420c82a4b5ce81fca6a16f376'
pdfs=[]
with tempfile.TemporaryDirectory(prefix='aq16-wording-review-') as tmp:
    for runname in ('first','second'):
        d=Path(tmp)/runname/'research/aq17-positive-signed-binding';d.mkdir(parents=True)
        for name in ('build_display16.py','candidate16.json'):shutil.copy2(task/name,d/name)
        shutil.copy2(root/'equation.tex',d.parents[1]/'equation.tex')
        p=subprocess.run([sys.executable,str(d/'build_display16.py')],cwd=d,capture_output=True,text=True,timeout=180)
        assert p.returncode==0 and 'two warning-free identical PDF builds' in p.stdout,(p.returncode,p.stdout,p.stderr)
        assert (d/'equation32-16.tex').read_bytes()==(task/'equation32-16.tex').read_bytes()
        pdfs.append(H(d/'equation32-16.pdf'))
assert pdfs==[H(task/'equation32-16.pdf')]*2
assert {str(p.resolve()):H(p) for p in files}==before_hashes
result={'status':'PASS_AQ16_WORDING_AUDIT','inputs_sha256':before_hashes,'baseline_commit':'007aeb301b','reviewed_commit':'7d72057118',
        'comparison':'only the status paragraph differs in generator and TeX','candidate_sha256':H(task/'candidate16.json'),
        'generator_runs':2,'generator_builds_per_run':2,'generator_pdf_sha256':pdfs,
        'scope':'Exploratory AQ16 overlay only; no guarded or paired AQ16 replay or formal PDF-to-Lean identification. The decoder/rank recipe remains manually transcribed.'}
out=here/'receipt.json'
if out.exists():raise ValueError('refusing to overwrite receipt')
out.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n');print(result['status'],H(out),pdfs[0])
