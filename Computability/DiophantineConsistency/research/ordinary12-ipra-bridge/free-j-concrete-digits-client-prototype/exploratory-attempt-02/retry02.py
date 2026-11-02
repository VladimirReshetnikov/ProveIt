import importlib.util,json,os,sys
from pathlib import Path
m=Path('Computability/DiophantineConsistency/research/ordinary12-ipra-bridge/free-j-current-denominator-composition/replay.py').resolve();spec=importlib.util.spec_from_file_location('monitor',m);monitor=importlib.util.module_from_spec(spec);spec.loader.exec_module(monitor)
root=Path('/tmp/ipra-freej-concrete-digits-explore/src');lib=Path('/tmp/ipra-freej-concrete-digits-explore/lib');scan=json.loads(Path('Computability/DiophantineConsistency/research/ordinary12-ipra-bridge/free-j-concrete-digits-closure-plan/scan.json').read_text());env=os.environ.copy()
for k in tuple(env):
 if k.startswith('PYTHON') or k in ('LEAN_SRC_PATH','LEAN_SYSROOT','LD_LIBRARY_PATH','LD_PRELOAD','LD_AUDIT'):env.pop(k,None)
env['LEAN_PATH']=str(lib)+':/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib'
for name in ['FreeJConcreteDigitsClient']:
 src=root/'DiophantineConsistency'/(name+'.lean');obj=lib/'DiophantineConsistency'/(name+'.olean');log=Path('/tmp/ipra-freej-concrete-digits-explore')/(name+'.retry02.log')
 if obj.exists() or obj.is_symlink():raise ValueError(('output occupied',name))
 cmd=['/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean','-M3000','-j1','-DElab.async=false',f'--root={root}',str(src),'-o',str(obj)]
 code,peak,reason=monitor.monitored(cmd,env,log);print(name,'exit',code,'reason',reason,'peak',peak,flush=True)
 if code or reason:sys.exit(code or 1)
