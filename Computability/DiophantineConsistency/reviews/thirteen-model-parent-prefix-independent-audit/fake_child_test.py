#!/usr/bin/env python3
"""Run the actual prefix loop with a fake compiler; never invoke real Lean."""
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile

ROOT=Path(__file__).resolve().parents[4]
DRIVER=ROOT/'Computability/DiophantineConsistency/research/thirteen-model-parent-prefix/replay.py'
FAKE = r'''#!/usr/bin/python3
import json, os, pathlib, sys, time
if any(k.startswith('PYTHON') for k in os.environ):
    raise SystemExit('unsanitized startup environment')
m=json.loads(pathlib.Path('/tmp/ipra-thirteen-current-source-02/manifest.json').read_text())
root=pathlib.Path('/tmp/ipra-thirteen-current-source-02/src')
source=pathlib.Path(next(x for x in sys.argv[1:] if x.endswith('.lean')))
module='.'.join(source.relative_to(root).with_suffix('').parts)
lib=pathlib.Path(os.environ['LEAN_PATH'].split(':')[0])
package=pathlib.Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib')
with open(os.environ['PREFIX_FAKE_EVENTS'],'a') as f:f.write(('deps ' if '--deps' in sys.argv else 'compile ')+module+'\n')
if '--deps' in sys.argv:
    print(package/'Init.olean')
    for dep in m['sources'][module]['imports']:
        if dep in m['external_direct']:print(m['external_direct'][dep]['path'])
        else:print(lib/pathlib.Path(*dep.split('.')).with_suffix('.olean'))
else:
    out=pathlib.Path(sys.argv[sys.argv.index('-o')+1])
    out.write_bytes(('FAKE_OBJECT:'+module).encode())
    if os.environ['PREFIX_FAKE_MODE']=='admission':print('synthetic sorryAx')
    elif module=='DiophantineConsistency.ArithmeticHalfBinomial2011':print('warning: synthetic linter warning')
    time.sleep(.12)
'''

def need(ok,msg):
    if not ok:raise ValueError(msg)

def main():
    with tempfile.TemporaryDirectory(prefix='ipra-prefix-fake-harness-') as t:
        root=Path(t);fake=root/'fake_lean';fake.write_text(FAKE);fake.chmod(0o700)
        marker=root/'site-hook-ran';site=root/'site';site.mkdir()
        (site/'sitecustomize.py').write_text('from pathlib import Path\nPath('+repr(str(marker))+').write_text("executed")\n')
        events=root/'events';env=os.environ.copy();env['PYTHONPATH']=str(site);env['PYTHONHOME']='/nonexistent-prefix-canary'
        env['PREFIX_FAKE_EVENTS']=str(events)
        wrapper=('import importlib.util,sys; '
            f's=importlib.util.spec_from_file_location("driver",{str(DRIVER)!r}); '
            'm=importlib.util.module_from_spec(s);s.loader.exec_module(m); '
            f'm.LEAN=__import__("pathlib").Path({str(fake)!r}); '
            'sys.argv=[str(m.HERE/"replay.py"),"--output",sys.argv[1]];m.main()')
        # Fresh randomized names live directly in /tmp, as required by the driver.
        for mode in ('warning','admission'):
            out=Path(tempfile.mkdtemp(prefix='ipra-thirteen-parent-prefix-fake-',dir='/tmp'));out.rmdir()
            env['PREFIX_FAKE_MODE']=mode
            proc=subprocess.run([sys.executable,'-I','-S','-c',wrapper,str(out)],env=env,capture_output=True,text=True,timeout=240)
            if mode=='warning':
                need(proc.returncode==0 and (out/'receipt.json').is_file(),'warning run did not complete: '+proc.stderr[-2000:])
                receipt=json.loads((out/'receipt.json').read_bytes())
                need(receipt['status']=='PASS_PAIRED_2011_PARENT_PREFIX' and len(receipt['runs'])==40 and
                     all(not x['axiom_reports'] for x in receipt['runs']),'fake paired receipt')
                need('warning: synthetic linter warning' in (out/'author/DiophantineConsistency_ArithmeticHalfBinomial2011.log').read_text(),'warning was not accepted')
            else:
                need(proc.returncode!=0 and not (out/'receipt.json').exists() and 'compiler failure' in proc.stderr,'synthetic sorryAx accepted')
            import shutil
            if out.exists():shutil.rmtree(out)
        need(not marker.exists(),'PYTHONPATH site hook ran')
        lines=events.read_text().splitlines()
        need(sum(x.startswith('compile ') for x in lines)==41 and sum(x.startswith('deps ') for x in lines)==41,'fake child call count')
        print(json.dumps({'status':'PASS_FAKE_PREFIX_CHILD_CONTROLS','fake_compiler_count':41,'fake_deps_count':41,
          'warning_run_exit':0,'synthetic_sorry_run_nonzero':True,'site_hook_executed':False,
          'scope':'Actual builder loop with an injected fake compiler; not a Lean build or a proof of runtime resource isolation.'},indent=2))

if __name__=='__main__':main()
