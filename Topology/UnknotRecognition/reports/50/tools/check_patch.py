"""Check/apply the additive patch in a clean local tree, then run its tests.

This is NOT a full maintained repository checkout or a full repository test run.
"""
from bootstrap import bootstrap
ROOT=bootstrap()
import os,shutil,subprocess,sys,tempfile


def main():
    log=[]
    with tempfile.TemporaryDirectory(prefix='sparse_incidence_patch_') as temp:
        root=__import__('pathlib').Path(temp)
        fast=root/'Topology/UnknotRecognition/fast'
        native=fast/'fastunknot';native.mkdir(parents=True)
        (native/'__init__.py').write_text('')
        for f in (ROOT/'snapshots/fastunknot').glob('*.py'):shutil.copy2(f,native/f.name)
        commands=[['git','init','-q'],['git','apply','--check',str(ROOT/'integration.patch')],
                  ['git','apply',str(ROOT/'integration.patch')],
                  [sys.executable,'-m','unittest','discover','-s',str(fast/'tests'),'-v']]
        for command in commands:
            env={**os.environ,'PYTHONPATH':str(fast)}
            x=subprocess.run(command,cwd=root,env=env,capture_output=True,text=True)
            log.extend(['$ '+' '.join(command),x.stdout,x.stderr,'exit='+str(x.returncode)])
            if x.returncode:
                (ROOT/'results/integration_patch_check.txt').write_text('\n'.join(log))
                raise SystemExit(x.returncode)
    (ROOT/'results/integration_patch_check.txt').write_text('\n'.join(log))
    print('Additive patch check/apply and 21 native-style local test methods passed.')
if __name__=='__main__':main()
