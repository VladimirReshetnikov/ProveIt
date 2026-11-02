import importlib.util,os,sys,shutil
from pathlib import Path
OUT=Path('/tmp/ipra-fixed-graph-digits-explore');SRC=OUT/'src';LIB=OUT/'lib';SRC.mkdir();spec=importlib.util.spec_from_file_location('monitor',Path('Computability/DiophantineConsistency/research/ordinary12-ipra-bridge/free-j-current-denominator-composition/replay.py').resolve());m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m);m.overlay(Path('/tmp/ipra-compact-mask-finish-explore/lib'),LIB)
env=os.environ.copy()
for k in tuple(env):
 if k.startswith('PYTHON') or k in ('LD_PRELOAD','LD_LIBRARY_PATH','LD_AUDIT','LEAN_SRC_PATH','LEAN_SYSROOT'):env.pop(k,None)
env['LEAN_PATH']=str(LIB)+':/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib'
base=Path('Computability/DiophantineConsistency/research/ordinary12-ipra-bridge')
sources=[('CompactFixedBeta',Path('/tmp/ipra-compact-mask-bounds-explore/CompactFixedBeta.lean')),('CompactSymbolicPorts',base/'compact44-symbolic-ports-prototype/CompactSymbolicPorts.lean'),('CompactFixedGraphDigits',Path('/tmp/ipra-compact-mask-bounds-explore/CompactFixedGraphDigits.lean'))]
for n,orig in sources:
 src=SRC/'DiophantineConsistency'/(n+'.lean');src.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(orig,src);obj=LIB/'DiophantineConsistency'/(n+'.olean');log=OUT/(n+'.log')
 if os.path.lexists(obj):raise ValueError('object collision')
 cmd=['/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean','-M3000','-j1','-DElab.async=false',f'--root={SRC}',str(src),'-o',str(obj)]
 code,peak,reason=m.monitored(cmd,env,log);print(n,'exit',code,'reason',reason,'peak',peak,flush=True)
 if code or reason:sys.exit(code or 1)
