#!/usr/bin/env python3
"""Execute the actual 342-step sibling loops with fake deps/compiler, never Lean."""
import json,os,shutil,subprocess,sys,tempfile
from pathlib import Path
ROOT=Path(__file__).resolve().parents[4]
DRIVER=ROOT/'Computability/DiophantineConsistency/research/thirteen-model-endpoint-successor/replay.py'
FAKE_LEAN=r'''#!/usr/bin/python3
import json,os,pathlib,sys
if any(k.startswith('PYTHON') for k in os.environ):raise SystemExit('unsanitized Python startup variable')
if '--deps' not in sys.argv:raise SystemExit('actual fake compiler path unexpectedly invoked')
source=pathlib.Path(sys.argv[-1]);snap=pathlib.Path('/tmp/ipra-thirteen-endpoint-source-01');m=json.loads((snap/'manifest.json').read_text());p=json.loads(pathlib.Path(os.environ['FAKE_FRONTIER']).read_text());lib=pathlib.Path(os.environ['LEAN_PATH'].split(':')[0]);package=pathlib.Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib')
try:name='.'.join(source.relative_to(snap/'src').with_suffix('').parts);imports=m['sources'][name]['imports']
except ValueError:
 name=source.stem
 if name in ('Thirteen69Nodes','Thirteen69Cuts'):name='DiophantineConsistency.'+name
 imports={'DiophantineConsistency.Thirteen69Nodes':['DiophantineConsistency.ModelDifferenceRing','DiophantineConsistency.ThirteenCarrier'],'DiophantineConsistency.Thirteen69Cuts':['DiophantineConsistency.Thirteen69Nodes'],'Model69EndpointBindingDraft':['DiophantineConsistency.ModelThirteenCarrier','DiophantineConsistency.Thirteen69Cuts'],'Model69EndpointChecks':['Model69EndpointBindingDraft']}[name]
with open(os.environ['FAKE_EVENTS'],'a') as f:f.write('deps '+name+'\n')
print(package/'Init.olean')
for dep in imports:
 if dep in p['rebuild_external_guards']:print(p['rebuild_external_guards'][dep]['path'])
 else:print(lib/pathlib.Path(*dep.split('.')).with_suffix('.olean'))
'''
FAKE_MONITOR=r'''import os,pathlib

def monitored(cmd,env,log,timeout=180):
    if any(k.startswith('PYTHON') for k in env):raise ValueError('unsanitized compiler environment')
    source=pathlib.Path(cmd[-3]);root=pathlib.Path(next(x[7:] for x in cmd if x.startswith('--root=')))
    name='.'.join(source.relative_to(root).with_suffix('').parts)
    with open(env['FAKE_EVENTS'],'a') as f:f.write('compile '+name+'\n')
    out=pathlib.Path(cmd[-1]);out.write_bytes(('FAKE_OBJECT:'+name).encode())
    text=''
    if env.get('FAKE_MODE')=='admission':text='synthetic sorryAx\n'
    elif name=='Model69EndpointChecks':text=''.join("'Fake.theorem%d' depends on axioms: [propext]\n"%i for i in range(8))
    log.write_text(text)
    return 0,123456,None
'''
def need(b,m):
    if not b:raise ValueError(m)
def main():
    with tempfile.TemporaryDirectory(prefix='ipra-thirteen-successor-fake-') as td:
        root=Path(td);fake=root/'fake_lean';fake.write_text(FAKE_LEAN);fake.chmod(0o700);monitor=root/'fake_monitor.py';monitor.write_text(FAKE_MONITOR)
        events=root/'events';site=root/'site';site.mkdir();marker=root/'site-hook';(site/'sitecustomize.py').write_text('from pathlib import Path\nPath('+repr(str(marker))+').write_text("ran")\n')
        env=os.environ.copy();env['PYTHONPATH']=str(site);env['PYTHONHOME']='/nonexistent-python-canary';env['FAKE_EVENTS']=str(events);env['FAKE_FRONTIER']=str(ROOT/'Computability/DiophantineConsistency/research/thirteen-model-endpoint-closure/frontier-plan.json')
        for x in ('LD_PRELOAD','LD_LIBRARY_PATH','LD_AUDIT'):env.pop(x,None)
        wrapper=('import importlib.util,sys,pathlib,hashlib; '
          f's=importlib.util.spec_from_file_location("driver",{str(DRIVER)!r}); '
          'm=importlib.util.module_from_spec(s);s.loader.exec_module(m); '
          f'm.PINS.pop(m.LEAN);m.LEAN=pathlib.Path({str(fake)!r});m.PINS[m.LEAN]=hashlib.sha256(m.LEAN.read_bytes()).hexdigest();m.MONITOR=pathlib.Path({str(monitor)!r}); '
          'sys.argv=[str(m.HERE/"replay.py"),"--output",sys.argv[1]];m.main()')
        outcomes=[]
        for mode in ('complete','admission'):
            out=Path(tempfile.mkdtemp(prefix='ipra-thirteen-endpoint-successor-pair-fake-',dir='/tmp'));out.rmdir();env['FAKE_MODE']=mode
            p=subprocess.run([sys.executable,'-I','-S','-c',wrapper,str(out)],env=env,capture_output=True,text=True,timeout=900)
            if mode=='complete':
                need(p.returncode==0 and (out/'receipt.json').is_file(),'fake loop failed '+p.stderr[-4000:])
                receipt=json.loads((out/'receipt.json').read_bytes());need(receipt['status']=='PASS_PAIRED_THIRTEEN_ENDPOINT_SUCCESSOR' and len(receipt['runs'])==684,'receipt rows')
                need(all(row['exit']==0 and row['deps_exit']==0 for row in receipt['runs']),'fake child exits')
                need(receipt['runs'][341]['module']==receipt['runs'][683]['module']=='Model69EndpointChecks','last step')
            else:need(p.returncode!=0 and not (out/'receipt.json').exists() and 'compiler failure' in p.stderr,'admission accepted')
            outcomes.append({'mode':mode,'exit':p.returncode})
            if out.exists():shutil.rmtree(out)
        need(not marker.exists(),'site hook executed')
        lines=events.read_text().splitlines();need(sum(x.startswith('compile ') for x in lines)==685 and sum(x.startswith('deps ') for x in lines)==685,'child event counts')
        print(json.dumps({'status':'PASS_FAKE_342_STEP_SUCCESSOR_LOOP','outcomes':outcomes,'fake_compiles':685,'fake_dependency_queries':685,'site_hook_executed':False,'scope':'Actual pinned launcher loop and guards with injected fake Lean dependency executable and fake monitoring/compilation; not a Lean build or resource-control test.'},indent=2))
if __name__=='__main__':main()
