#!/usr/bin/env python3
"""Read-only verification of contextual endpoint evidence; no clone or Lean."""
import ast,hashlib,json,os,subprocess,sys
from pathlib import Path
if not __debug__ or os.environ.get('PYTHONOPTIMIZE') or not sys.flags.isolated or not sys.flags.no_site:raise RuntimeError('requires nonoptimized python3 -I -S')
ROOT=Path(__file__).resolve().parents[4];HERE=Path(__file__).resolve().parent;BASE=ROOT/'Computability/DiophantineConsistency';P=BASE/'reviews/historical-endpoint-contextual-audit';EP=BASE/'reviews/thirteen-model-endpoint-successor-pair-independent-audit';PLAN=BASE/'research/thirteen-model-endpoint-closure';SOURCE=BASE/'Lean/DiophantineConsistency/ModelCarrierCurrent.lean'
H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
for name in ['README.md','CHECK.json','terminal-observation.json','prepare.py','contextual-endpoint.py','sparse-patterns.txt']:
 p=P/name;rel=p.relative_to(ROOT).as_posix();old=subprocess.run(['git','show','3974b37053:'+rel],cwd=ROOT,capture_output=True,check=True).stdout
 if old!=p.read_bytes():raise ValueError(('packet drift',name))
assert H(P/'CHECK.json')=='d0308098d2d7816c0c8bf72c8c78227718a17984da34e35c1fb8a6f497d50f5e'
assert H(P/'prepare.py')=='f0f9d69d633425ea6f16cbc63b9abb4de560f5a3919004fffee490782ae3a4bb'
assert H(P/'contextual-endpoint.py')=='a8a04953d66f0df7af61647e82f01e2120d86861c017b8c9bf2bfccce71b14db'
assert H(P/'sparse-patterns.txt')=='42493869ab7a51e631c74c02ffe8e558ce353ba25d7208b3d9c8ecf05041a4dc'
assert H(EP/'audit.py')=='ec4892d88e69a9f53d3d93d48ce9e43cc8a5f9631ed4a885af17a40011858681'
assert H(HERE/'contextual-output.json')==H(EP/'CHECK.json')=='50c18ab38d6393cf784e658b5626bb6ec3cb490dc1652f5b5dcfa2b1adca1cce'
tree=ast.parse((P/'contextual-endpoint.py').read_text());assigns=[]
for n in ast.walk(tree):
 if isinstance(n,(ast.Assign,ast.AnnAssign,ast.AugAssign)):
  targets=n.targets if isinstance(n,ast.Assign) else [n.target]
  for t in targets:
   if isinstance(t,ast.Attribute) and isinstance(t.value,ast.Name) and t.value.id=='m':assigns.append(t.attr)
assert assigns==['PARENTAUDIT'],assigns
oldhash='3f76453da57164d06bd338928d0e3d587df46851c77d5cbc4fbf858119719076';livehash='f0a4898f545a932b135783799ae0d44179fbcbcb08e5d97eaced4515740e990f'
blob=subprocess.run(['git','show','435062d125:'+SOURCE.relative_to(ROOT).as_posix()],cwd=ROOT,capture_output=True,check=True).stdout
assert hashlib.sha256(blob).hexdigest()==oldhash==H('/tmp/ipra-thirteen-endpoint-source-01/src/DiophantineConsistency/ModelCarrierCurrent.lean')
assert H(SOURCE)==livehash
base=json.loads(Path('/tmp/ipra-ordinary12-coexistence-source-03/manifest.json').read_bytes());survey=json.loads((PLAN/'source-manifest.json').read_bytes());plan=json.loads((PLAN/'frontier-plan.json').read_bytes());rows=dict(base['sources']);rows.update(survey['sources']);mismatch=[]
for n,h in plan['all_selected_source_hashes'].items():
 p=ROOT/rows[n]['workspace_path'];actual=H(p) if p.is_file() else None
 if actual!=h:mismatch.append((n,h,actual))
assert mismatch==[('DiophantineConsistency.ModelCarrierCurrent',oldhash,livehash)] and len(plan['all_selected_source_hashes'])==1145
print(json.dumps({'status':'PASS_INDEPENDENT_CONTEXTUAL_ENDPOINT_EVIDENCE','reviewed_commit':'3974b37053','independent_preparation_session':69682,'independent_preparation_exit':0,'independent_contextual_session':71389,'independent_contextual_exit':0,'contextual_stdout_sha256':H(HERE/'contextual-output.json'),'selected_source_count':1145,'live_source_mismatch_count':1,'rebound_globals':assigns,'scope':'Independent fresh historical-source view and exact-original endpoint audit with only PARENTAUDIT rebound. Not an unchanged live full-chain pass, current-source validation, Lean build, or iPRA proof.'},indent=2))
