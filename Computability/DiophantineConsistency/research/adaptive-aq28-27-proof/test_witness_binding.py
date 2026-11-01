#!/usr/bin/env python3
"""Negative controls for the finite source-to-graph witness audit."""
from contextlib import redirect_stdout
import io
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import verify_witness_binding as check

SOURCE=Path(__file__).resolve().parent/'draft-src'
with tempfile.TemporaryDirectory(prefix='aq-draft-binding-control-') as tmp:
    draft=Path(tmp)/'draft-src';shutil.copytree(SOURCE,draft)
    with redirect_stdout(io.StringIO()):check.verify(draft)
    def reject(filename,old,new,reason):
        path=draft/filename;saved=path.read_text()
        if saved.count(old)!=1:raise AssertionError(('mutation not unique',filename,old,saved.count(old)))
        path.write_text(saved.replace(old,new,1))
        try:
            with redirect_stdout(io.StringIO()):check.verify(draft)
        except (ValueError,KeyError) as exc:
            if reason not in str(exc):raise AssertionError((reason,str(exc)))
        else:raise AssertionError(('mutation accepted',filename,old))
        finally:path.write_text(saved)
    reject('AdaptiveAQ27Maps.lean','v 17 * (v 17 + (v 9 + v 10))',
           'v 16 * (v 17 + (v 9 + v 10))','map/fill mismatch')
    reject('AdaptiveAQ26Transport.lean','have h9 := hall 16','have h9 := hall 15','deleted equation index')
    reject('AdaptiveAQ28Zeros.lean','![A0,A1,auxResidual','![A1,A0,auxResidual','sum not definitionally aligned')
    reject('AdaptiveAQ28Zeros.lean','v ↔ ∀ i : Fin 19, InternalZero (residuals p i) v',
           'v ↔ ∀ i : Fin 18, InternalZero (residuals p i) v','sum-zero statement')
    reject('AdaptiveAQ27Transport.lean','change InternalZero (.var 25 - (.var 17 *',
           'change InternalZero (.var 24 - (.var 17 *','deleted equation expression')
    reject('IPRAAQ26Native.lean','IPRAAQ27Native.bridge27','IPRAAQ27Native.bridge28','native endpoint wiring')
    # Regenerate in an isolated miniature tree. In particular, this catches
    # the old overlapping replacement Fin 20 → Fin 19 → Fin 18 for AQ28.
    project=Path(tmp)/'project';research=project/'research';runner=research/'adaptive-aq28-27-proof'
    runner.mkdir(parents=True);shutil.copyfile(SOURCE.parent/'generate_model.py',runner/'generate_model.py')
    for n in (28,27,26):
        name=f'adaptive-square-sums{n}-degree8';(research/name).mkdir()
        shutil.copyfile(SOURCE.parent.parent/name/'candidate.json',research/name/'candidate.json')
    parent=project/'Lean/DiophantineConsistency';parent.mkdir(parents=True)
    shutil.copyfile(check.ROOT/'Lean/DiophantineConsistency/AdaptiveAQ29Zeros.lean',parent/'AdaptiveAQ29Zeros.lean')
    result=subprocess.run([sys.executable,str(runner/'generate_model.py')],env=dict(os.environ,PYTHONDONTWRITEBYTECODE='1'),capture_output=True,text=True)
    if result.returncode:raise AssertionError(('generator failed',result.stdout,result.stderr))
    for n in (28,27,26):
        for suffix in ('Zeros','Literal'):
            name=f'AdaptiveAQ{n}{suffix}.lean'
            if (runner/'draft-src'/name).read_bytes()!=(SOURCE/name).read_bytes():
                raise AssertionError(('generator output differs',name))
    shutil.copyfile(SOURCE.parent/'generate_transport.py',runner/'generate_transport.py')
    for name in ('AdaptiveAQ29Transport','AdaptiveAQ29','AdaptiveAQ29Checks','IPRAAQ29Native','IPRAAQ29NativeChecks'):
        shutil.copyfile(check.ROOT/'Lean/DiophantineConsistency'/(name+'.lean'),parent/(name+'.lean'))
    result=subprocess.run([sys.executable,str(runner/'generate_transport.py')],env=dict(os.environ,PYTHONDONTWRITEBYTECODE='1'),capture_output=True,text=True)
    if result.returncode:raise AssertionError(('transport generator failed',result.stdout,result.stderr))
    for n in (28,27,26):
        for name in (f'AdaptiveAQ{n}Maps',f'AdaptiveAQ{n}Transport',f'AdaptiveAQ{n}',
                     f'AdaptiveAQ{n}Checks',f'IPRAAQ{n}Native',f'IPRAAQ{n}NativeChecks'):
            if (runner/'draft-src'/(name+'.lean')).read_bytes()!=(SOURCE/(name+'.lean')).read_bytes():
                raise AssertionError(('transport generator output differs',name))
    for script,template,reason in (('generate_model.py','AdaptiveAQ29Zeros.lean','AQ29 zero template drift'),
                                   ('generate_transport.py','AdaptiveAQ29Transport.lean','AQ29 template drift')):
        path=parent/template;saved=path.read_bytes();path.write_bytes(saved+b'\n-- changed\n')
        result=subprocess.run([sys.executable,str(runner/script)],env=dict(os.environ,PYTHONDONTWRITEBYTECODE='1'),capture_output=True,text=True)
        path.write_bytes(saved)
        if result.returncode==0 or reason not in result.stderr:
            raise AssertionError(('modified template accepted',script,result.stdout,result.stderr))
print('PASS: generator arities, residuals, maps, deleted equations, transport indices and native wiring; negative controls rejected')
