#!/usr/bin/env python3
"""Independent v3 wiring and duplicate-dependency policy review; no launches."""
import hashlib,importlib.util,json,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit('Use python3 -I -S -B without optimization')
def need(x,s):
    if not x:raise RuntimeError(s)
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
base=Path(__file__).resolve().parents[2];repo=Path(__file__).resolve().parents[4]
driver=base/'research/current14-printed-port-extension-driver-v3';coord=base/'research/current14-printed-port-extension-coordinator-v3';client=base/'research/current14-structured-endpoint-coherent-runner-v3'
rp=driver/'controls-receipt.json';receipt=json.loads(rp.read_text());need(receipt['status']=='PASS' and receipt['deps_controls_exit']==0 and not receipt['deps_controls_stderr'],'author receipt')
need(len(receipt['sha256'])==14,'author receipt inventory')
for name,h in receipt['sha256'].items():need(sha(repo/name)==h,'frozen source drift '+name)
need(json.loads(receipt['deps_controls_stdout'])['status']=='PASS','author dependency controls')
# Independently exercise the shared API with the unmodified retained real lines.
spec=importlib.util.spec_from_file_location('v3_policy_independent',driver/'deps.py');policy=importlib.util.module_from_spec(spec);spec.loader.exec_module(policy)
raw=base/'reviews/current14-extension-v2-failure/first-deps.stdout';lines=raw.read_text().splitlines()
need(len(lines)==5 and lines[0]==lines[1] and len(set(lines))==4,'retained duplicate changed')
direct={'Init':{'path':lines[0]},'DiophantineConsistency.WangTiles942TableData':{'path':lines[2]},
        'DiophantineConsistency.WangTiles942Data':{'path':lines[3]},'Mathlib.Tactic':{'path':lines[4]}}
need(policy.validate(lines,direct)=={'Init':2,'DiophantineConsistency.WangTiles942TableData':1,'DiophantineConsistency.WangTiles942Data':1,'Mathlib.Tactic':1},'real duplicate rejected')
def reject(values,ds=direct):
    try:policy.validate(values,ds)
    except ValueError:return True
    raise RuntimeError('unexpected acceptance')
checks={'third_Init':reject([lines[0],*lines]),'non_Init_duplicate':reject(lines+[lines[2]]),
        'conflicting_Init_path':reject(lines+['/other/Init.olean']),
        'dot_spelling':reject(lines+[lines[0].replace('/Init.olean','/./Init.olean')]),
        'missing_declared_direct':reject(lines[:-1]),'unrecorded_extra':reject(lines+['/other/Other.olean'])}
counts={'Init':1};
try:policy.duplicate({'Init':{'path':'/package/Init.olean'}},counts,'Init','/toolchain/Init.olean')
except ValueError:checks['stream_conflicting_Init']=True
else:raise RuntimeError('stream conflict accepted')
# Check that the same helper gates each stage and that the failure paths are distinct.
ds=(driver/'driver.py').read_text();cs=(coord/'coordinator.py').read_text();vs=(coord/'verify.py').read_text();rs=(client/'runner.py').read_text();ss=(client/'extension_supervisor.py').read_text()
for token in ('from deps import duplicate, validate as validate_dependencies','if duplicate(direct,counts,module,path):continue',
              'validate_dependencies(dep_stdout.splitlines(),direct)',"'deps_sha256':digest(HERE/'deps.py')",
              "OUT=Path('/tmp/current14-printed-port-extension-v3-20261104')"):
    need(token in ds,'driver wiring '+token)
for token in ('from deps import validate as validate_dependencies',"validate_dependencies(Path(rec['deps_stdout']).read_text().splitlines(),rec['direct_inputs'])"):
    need(token in vs,'terminal verifier wiring '+token)
for token in ("'deps_sha256':DEPS_SHA", "OUT=Path('/tmp/current14-printed-port-extension-coordinator-v3-20261104')"):
    need(token in cs,'coordinator wiring '+token)
for token in ('if driver.duplicate(direct,counts,module,path):continue','driver.validate_dependencies(deps_text.splitlines(),direct)',
              "SUP_OUT=Path('/tmp/current14-printed-port-coordinator-supervisor-v3-20261104')",
              "OUT=Path('/tmp/current14-structured-endpoint-coherent-v3-20261104')"):
    need(token in rs,'client wiring '+token)
need('current14-printed-port-extension-coordinator-v3/coordinator.py' in ss and
     '/tmp/current14-printed-port-extension-coordinator-v3-20261104' in ss,'supervisor routing')
coord_control=json.loads((coord/'controls-observation.json').read_text());client_control=json.loads((client/'controls-observation.json').read_text())
need(coord_control['status']==client_control['status']=='PASS','component controls status')
for key in ('third_init_rejected','duplicate_project_rejected','alternate_init_rejected'):
    need(key in coord_control['controls'],'coordinator negative control '+key)
ind=json.loads((Path(__file__).parent/'nonempty-result.json').read_text())
need(ind['status']=='PASS_V3_SYNTHETIC_NONEMPTY_ROUTES' and ind['script_sha256']==sha(Path(__file__).parent/'nonempty-controls.py') and
     ind['deps_sha256']==sha(driver/'deps.py') and ind['verifier_sha256']==sha(coord/'verify.py'),'independent synthetic controls')
result={'status':'PASS_V3_SOURCE_AND_SYNTHETIC_REVIEW','script_sha256':sha(__file__),
 'author_controls_receipt_sha256':sha(rp),'reviewed_file_count':len(receipt['sha256']),
 'driver_sha256':sha(driver/'driver.py'),'deps_sha256':sha(driver/'deps.py'),'coordinator_sha256':sha(coord/'coordinator.py'),
 'verifier_sha256':sha(coord/'verify.py'),'supervisor_sha256':sha(client/'extension_supervisor.py'),'client_runner_sha256':sha(client/'runner.py'),
 'real_failed_stdout_sha256':sha(raw),'independent_synthetic_sha256':sha(Path(__file__).parent/'nonempty-result.json'),
 'independent_policy_controls':checks,
 'scope':'Source wiring, retained duplicate log and synthetic controls only; no Lean, retry, actual extension or supervisor outer exit.'}
print(json.dumps(result,indent=2,sort_keys=True))
