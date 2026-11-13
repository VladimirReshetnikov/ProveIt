#!/usr/bin/env python3
"""Read-only diagnosis of retained duplicate-Init failure; no Lean launch."""
import hashlib,json,re,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit('Use python3 -I -S -B without optimization')
def need(b,s):
    if not b:raise RuntimeError(s)
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
base=Path(__file__).resolve().parents[2]; ext=Path('/tmp/current14-printed-port-extension-20261104');coord=Path('/tmp/current14-printed-port-extension-coordinator-v2-20261104');sup=Path('/tmp/current14-printed-port-coordinator-supervisor-20261104');manifest=base/'research/current14-printed-port-extension-plan/kernel-manifest.json'
source=ext/'src/DiophantineConsistency/WangTiles942Core.lean';out=ext/'logs/000-DiophantineConsistency_WangTiles942Core.deps.stdout';err=ext/'logs/000-DiophantineConsistency_WangTiles942Core.deps.stderr'
pins={ext/'state.json':'3aa586de1bdc9ef3bc31e19294fdecc2245fe9c83323f555090044f4923e5d36',
 source:'27eae9953d2938690af39d5b52b30520bc99d8e013181962c38b7810c82e5304',out:'05a3e9b79ec533e62ad69e139b9a2e4d405281e44a97971ac0e635b6b1e79da4',err:'e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855',
 coord/'state.json':'ac196bdbeb554dd1eabf0d73b0b6f33d96d2e5ee6b78e3acb94813696a79e27e',coord/'extension-process.log':'1bbbba68a1c1614c75905ee869eb2ba88393eb3e1dba6d799c535ab0d083e0b1',
 sup/'receipt.json':'89e0ae47869b55a7fd478a98c2db9359ddf297fc67eae36826baad91970115a0',sup/'coordinator.log':'795c1d797fb62335b0c9112cb77b81ceaf51616d203b54b9afb98fbccbb43859',
 manifest:'4809f9cb3572bb0bdc47b22fd6a0c0e277c215d7aa322fd1847e8e63152fd6b2'}
for p,h in pins.items():need(sha(p)==h,'evidence drift '+str(p))
state=json.loads((ext/'state.json').read_text());outer=json.loads((coord/'state.json').read_text());receipt=json.loads((sup/'receipt.json').read_text())
need(state['status']=='FAILED' and state['index']==0 and state['module']=='DiophantineConsistency.WangTiles942Core' and state['records']==[] and "('duplicate import', 'Init')" in state['failure'],'failure scope')
need(outer['status']=='FAILED' and outer['child_exit']==1 and receipt['status']=='FAILED' and receipt['child_exit']==1 and receipt['coordinator_state_sha256']==sha(coord/'state.json'),'outer failure evidence')
lines=out.read_text().splitlines();need(len(lines)==5 and lines[0]==lines[1] and lines[0].endswith('/Init.olean') and len(set(lines))==4 and not err.read_bytes(),'dependency lines')
source_imports=re.findall(r'^import\s+(\S+)\s*$',source.read_text(),re.M)
expected=json.loads(manifest.read_text())['sources']['DiophantineConsistency.WangTiles942Core']['imports']
need(source_imports==expected and len(expected)==3 and 'Init' not in expected,'source import list')
need(all(Path(p).is_absolute() and Path(p).is_file() for p in lines),'dependency path missing')
outj={'status':'PASS_DIAGNOSIS_ONLY','script_sha256':sha(__file__),
 'failed_extension_state_sha256':pins[ext/'state.json'],'supervisor_receipt_sha256':pins[sup/'receipt.json'],
 'source_sha256':pins[source],'deps_stdout_sha256':pins[out],'deps_stderr_sha256':pins[err],
 'declared_imports':source_imports,'dependency_line_count':len(lines),'distinct_path_count':len(set(lines)),
 'repeated_lexical_path':lines[0],'supervisor_observed_coordinator_exit':receipt['child_exit'],
 'scope':'Read-only retained failure diagnosis; no new build, no claim about why Lean emitted the duplicate, no supervisor-session outer exit claim.'}
print(json.dumps(outj,indent=2,sort_keys=True))
