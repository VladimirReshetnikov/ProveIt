import importlib.util,json,os,shutil,sys,hashlib
from pathlib import Path
BASE=Path('Computability/DiophantineConsistency/research/ordinary12-ipra-bridge').resolve();PLAN=BASE/'compact44-symbolic-graph-closure-plan/scan.json';PREFIX=Path('/tmp/ipra-freej-concrete-digits-client-pair-01/author/lib');OUT=Path('/tmp/ipra-symbolic-graph-join-explore-01');ROOT=OUT/'src';LIB=OUT/'lib';MON=BASE/'free-j-current-denominator-composition/replay.py'
spec=importlib.util.spec_from_file_location('monitor',MON);m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
if ROOT.exists() or LIB.exists():raise ValueError('fresh outputs required')
ROOT.mkdir();m.overlay(PREFIX,LIB); scan=json.loads(PLAN.read_text());env=os.environ.copy()
for k in tuple(env):
 if k.startswith('PYTHON') or k in ('LD_PRELOAD','LD_LIBRARY_PATH','LD_AUDIT','LEAN_SRC_PATH','LEAN_SYSROOT'):env.pop(k,None)
env['LEAN_PATH']=str(LIB)+':/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib'
for row in scan['modules']:
 name=row['module'];rel=Path(*name.split('.'));src=ROOT/rel.with_suffix('.lean');src.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(row['source'],src)
 if hashlib.sha256(src.read_bytes()).hexdigest()!=row['source_sha256']:raise ValueError(('source drift',name))
 obj=LIB/rel.with_suffix('.olean');obj.parent.mkdir(parents=True,exist_ok=True);log=OUT/(name.split('.')[-1]+'.log')
 if os.path.lexists(obj):raise ValueError(('object already present',name))
 cmd=['/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean','-M3000','-j1','-DElab.async=false',f'--root={ROOT}',str(src),'-o',str(obj)]
 code,peak,reason=m.monitored(cmd,env,log);print(name,'exit',code,'reason',reason,'peak',peak,flush=True)
 if code or reason:sys.exit(code or 1)
