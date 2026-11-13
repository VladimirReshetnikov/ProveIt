#!/usr/bin/env python3
"""Audit the 27-variable PDF's author-only status refresh, not a Lean replay."""
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys
import tempfile

if not __debug__:
    raise RuntimeError('This audit requires assertions; do not run Python with -O or -OO')

D=Path(__file__).resolve().parent
BASE=D.parents[1]
ROOT=BASE.parents[1]
R=BASE/'research/adaptive-square-sums27-degree8'
PACKET=BASE/'reviews/aq26-author-trial-v2'
AUDIT=BASE/'reviews/aq26-author-independent-audit'
H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
old='its model witness transport and native intuitionistic PRA equivalence have not yet been proved in Lean.'
new='its model transport and native intuitionistic PRA equivalence have passed one historical author run, but not a paired replay.'
baseline='50ff01847d385f74b59aa71abf8cb32104042f87'
tex=BASE/'equation8-27.tex'; pdf=BASE/'equation8-27.pdf'; generator=R/'generate_equation8_27.py'
inputs=[Path(__file__),tex,pdf,generator,R/'equation8-27-display.tex',R/'candidate.json',R/'verify_display8_27.py',R/'verify_degree.py',
        BASE/'research/adaptive-aq28-27-proof/verify_literals.py',
        PACKET/'state.json',PACKET/'author-additions.json',PACKET/'terminal-observation.json',
        AUDIT/'receipt.json',AUDIT/'terminal-observation.json',
        PACKET/'src/DiophantineConsistency/IPRAAQ27Native.lean',
        BASE/'README.md',BASE/'IPRA_PROVABILITY_PLAN.md',
        BASE/'research/adaptive-aq28-27-proof/README.md']
inputs += [BASE/f'research/adaptive-square-sums{n}-degree8/README.md' for n in (26,27,28)]
inputs += [BASE/f'research/adaptive-square-sums{n}-degree8/candidate.json' for n in (26,28)]
inputs += [BASE/f'research/adaptive-aq28-27-proof/draft-src/AdaptiveAQ{n}Literal.lean' for n in (26,27,28)]
inputs += [BASE/'research/adaptive-direct-ordinate86/verify_display_tex14.py',
           BASE/'research/adaptive-direct-ordinate86/verify_display_tex86.py',
           BASE/'research/adaptive-direct-ordinate86/candidate.json',BASE/'equation86.tex']
before={str(p.resolve()):H(p) for p in inputs}
def show(path):
    return subprocess.run(['git','show',baseline+':'+str(path.relative_to(ROOT))],cwd=ROOT,
                          check=True,capture_output=True).stdout
def cmd(args,**kw):
    p=subprocess.run(args,capture_output=True,**kw)
    assert p.returncode==0,(args,p.returncode,p.stdout,p.stderr)
    return p

# The only TeX and generator changes are the exact disclosure sentence.
for path in (tex,generator):
    was=show(path).decode(); now=path.read_text()
    assert was.count(old)==1 and now==was.replace(old,new,1),str(path)
assert H(pdf)=='2f05619dba9240de671d8734dc6d96ef5161364ceca9ebf198dacd0f36cab4c6'
old_pdf=show(pdf)
assert hashlib.sha256(old_pdf).hexdigest()=='181e6b6dea3c1bd9433e3a5f93fa4b10894616463b94d23f0fe717d290bb04e2'
state=json.loads((PACKET/'state.json').read_text())
obs=json.loads((PACKET/'terminal-observation.json').read_text())
audit=json.loads((AUDIT/'receipt.json').read_text())
assert H(PACKET/'state.json')==obs['state_sha256']==audit['trial_state_sha256']=='b7b18c51f0a8a921b916cd64119a8cccd0971c6bc2b0d759d4ae3d5433c92c73'
assert state['status']==obs['status']=='AUTHOR_ONLY_PASS' and obs['observed_exit_code']==0
assert audit['status']=='PASS_INDEPENDENT_AQ26_AUTHOR_ARTIFACT_AUDIT' and audit['added_modules']==24
assert len(audit['exact_diagnostic_names'])==75
rows={r['module']:r for r in state['rows']}
manifest=json.loads((PACKET/'author-additions.json').read_text())
for n in (28,27,26):
    name=f'DiophantineConsistency.AdaptiveAQ{n}Literal'
    path=BASE/f'research/adaptive-aq28-27-proof/draft-src/AdaptiveAQ{n}Literal.lean'
    assert H(path)==manifest['sources'][name]['sha256']==rows[name]['source_sha256']
for module in ('AdaptiveAQ27','IPRAAQ27Native','IPRAAQ27NativeChecks'):
    name='DiophantineConsistency.'+module
    assert rows[name]['exit']==0
assert 'DiophantineConsistency.AdaptiveAQ27.current_no_zero_iff' in audit['exact_diagnostic_names']
assert 'DiophantineConsistency.IPRAAQ27Native.literal_equivalence' in audit['exact_diagnostic_names']
source=(PACKET/'src/DiophantineConsistency/IPRAAQ27Native.lean').read_text()
assert re.search(r'theorem\s+literal_equivalence\s*:\s*nativeTheory\s*⊢',source)
assert '∼mappedNativeRefutation embedding' in source

# Check actual current Lean gate text and the displayed polynomial separately.
v=cmd([sys.executable,str(R/'verify_display8_27.py')],cwd=BASE,text=True)
assert '40 display definitions; eighteen-square wiring; 129 circuit rows' in v.stdout
l=cmd([sys.executable,str(BASE/'research/adaptive-aq28-27-proof/verify_literals.py')],cwd=BASE,text=True)
assert '27 variables, four ports, 129 draft Lean gates match graph' in l.stdout
assert H(R/'candidate.json')=='1982b2f164b9b72f965050e3a26cec751f7d0839c2da0cbe3cc020b7e6fc0170'

# Each README's actual update states the author-only result and its limits.
for n in (26,27,28):
    raw=' '.join((BASE/f'research/adaptive-square-sums{n}-degree8/README.md').read_text().split())
    assert 'author-only' in raw and 'independent artifact' in raw and 'not a matched peer' in raw
    assert 'Foundation wrapper' in raw and 'dynamic ancestry' in raw
chain=(BASE/'research/adaptive-aq28-27-proof/README.md').read_text()
assert 'author-only Lean extension' in chain and 'not a paired Lean replay or current-source result' in chain
assert '**Compilation is pending.**' not in chain and 'not yet Lean-verified' not in chain
summary=(BASE/'README.md').read_text();plan=(BASE/'IPRA_PROVABILITY_PLAN.md').read_text()
assert 'author-only historical run and independent artifact audit' in summary
assert 'paired Lean replay remains open' in summary
assert 'author-only extension' in plan and 'no matched peer' in plan

builds=[]
with tempfile.TemporaryDirectory(prefix='eq27-author-status-') as td:
    root=Path(td); oldfile=root/'previous.pdf';oldfile.write_bytes(old_pdf)
    for i in range(2):
        out=root/f'build{i}';out.mkdir()
        cmd(['pdflatex','-halt-on-error','-interaction=batchmode','-output-directory',str(out),tex.name],cwd=BASE)
        log=(out/'equation8-27.log').read_text(errors='replace')
        assert not re.search(r'Overfull|Underfull|Font Warning',log)
        builds.append(H(out/'equation8-27.pdf'))
    assert builds==[H(pdf),H(pdf)]
    for p in (pdf,oldfile):
        info=cmd(['pdfinfo',str(p)],text=True).stdout
        assert re.search(r'^Pages:\s+2\s*$',info,re.M)
    def textpage(path,page,layout=False):
        return cmd(['pdftotext',*(['-layout'] if layout else ['-raw']),'-f',str(page),'-l',str(page),str(path),'-'],text=True).stdout
    assert textpage(pdf,2,True)==textpage(oldfile,2,True)
    a=textpage(pdf,1);b=textpage(oldfile,1)
    assert a.split('The fixed integer A above')[0]==b.split('The fixed integer A above')[0]
    assert 'have passed one historical author run, but not a paired replay' in ' '.join(a.split())

assert before=={str(p.resolve()):H(p) for p in inputs}
receipt={'status':'PASS_27_AUTHOR_STATUS_REFRESH_AUDIT','input_sha256':before,
         'baseline_commit':baseline,'baseline_pdf_sha256':hashlib.sha256(old_pdf).hexdigest(),
         'current_pdf_sha256':H(pdf),'clean_pdf_builds':builds,'tex_and_generator_diff':'exact disclosure sentence only',
         'finite_display_validation_exit':v.returncode,'finite_lean_gate_validation_exit':l.returncode,
         'trial_state_sha256':H(PACKET/'state.json'),'author_artifact_audit_sha256':H(AUDIT/'receipt.json'),
         'scope':'Author-only historical status and finite presentation check; not a second Lean replay, current-source or package/dynamic authentication, or a Lean degree theorem.'}
out=D/'receipt.json'
if out.exists(): raise RuntimeError('refusing to overwrite audit evidence')
out.write_text(json.dumps(receipt,indent=2,sort_keys=True)+'\n')
print(receipt['status'],H(out))
