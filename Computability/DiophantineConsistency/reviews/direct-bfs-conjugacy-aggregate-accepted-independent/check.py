#!/usr/bin/env python3
"""Independent accepted aggregate receipt and all direct provider checks, no Lean replay."""
from pathlib import Path
import hashlib,json,re,subprocess,sys
D=Path(__file__).resolve().parents[2];R=D/'research';P=R/'direct-bfs-lean-conjugacy-aggregate-retry-prototype';inner=P/'observations/directbfsaggregateretry-attempt01';outer=P/'observations/outer-attempt01'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def j(p):return json.loads(Path(p).read_text())
source=P/'DirectBFSCoverageAggregate.lean';runner=P/'run.py';wrapper=P/'run-outer.py';t=j(inner/'terminal.json');o=j(outer/'terminal.json');h='1bc094f1934b8df7b54f0e7bfbadfba8c2b95cc30c0038dca5c5952761e705ef'
assert sha(runner)==o['runner_sha256']==t['pins']['runner']==h and sha(wrapper)==o['wrapper_sha256']
assert o['exit']==0 and sha(outer/'stdout')==o['stdout_sha256'] and sha(outer/'stderr')==o['stderr_sha256']
assert Path(o['command'][1]).resolve()==runner.resolve() and t['exit']==0 and t['reason'] is None
assert t['pins']==t['after'] and t['direct_imports']==t['direct_imports_after']
assert sha(source)==sha(inner/'source.txt')==t['pins']['source']=='3439657a35a3817564113158e9a4b155a19e7801b725ea2bfe4eda7d23bda47b'
assert sha(inner/'stdout')==t['stdout_sha256'] and sha(inner/'stderr')==t['stderr_sha256']
assert (inner/'stdout').read_bytes() in (outer/'stdout').read_bytes()
obj=Path(t['output_root'])/'DirectBFSCoverageAggregate.olean'
assert sha(obj)==t['object_sha256']=='1e8286158838654f19d7de3ba4ca45b99b72eda814546188e0a982b6c84af02b'
logs=(inner/'stdout').read_text()+(inner/'stderr').read_text()
assert not re.search(r'\b(?:error|warning)(?:\([^)]*\))?:|sorryAx',logs)
for kind in ['rows','inverse','horizontal','vertical','inversebounds','horizontalbounds','verticalbounds']:
 assert logs.count(f"'DirectBFSCoverageAggregate.{kind}_all' depends on axioms: [propext]")==1
imports=re.findall(r'^import\s+(\S+)$',source.read_text(),re.M);assert len(imports)==60 and imports==[x['module'] for x in t['direct_imports']]
print('outer',sha(outer/'terminal.json'),'inner',sha(inner/'terminal.json'),'object',sha(obj))
for x in t['direct_imports']:
 selected=next(Path(d)/(x['module'].replace('.','/')+'.olean') for d in t['lean_path'].split(':') if (Path(d)/(x['module'].replace('.','/')+'.olean')).is_file())
 assert str(selected.resolve())==x['path'] and sha(selected)==x['sha256'] and sha(selected) in t['pins']['extra']
 print(x['module'],x['path'],x['sha256'])
assert len(t['stage_receipts'])==59
for item in t['stage_receipts']:assert sha(item['path'])==item['sha256']
full=R/'direct-bfs-lean-conjugacy-coverage-prototype/observations/full01/result.json';assert sha(full)==t['full_summary_sha256']
assert t['command'][1:4]==['-M3000','-j1','-DElab.async=false'] and t['elapsed']<180
assert len(t['preflight']['lean'])<2 and t['preflight']['mem_available_kib']>=8*1024**2
assert all(len(s['lean'])<=2 and s['mem_available_kib']>=8*1024**2 for s in t['samples'])
check=D/'reviews/direct-bfs-conjugacy-full-sweep-independent/check.py';subprocess.run([sys.executable,'-I','-S','-B',str(check)],check=True,stdout=subprocess.DEVNULL)
print('PASS 60 selected direct imports, 59 stage receipts, full01 independent check, seven [propext] reports; no Lean replay')
