#!/usr/bin/env python3
"""Owned source/config-template review only; no captured helper execution."""
import ast,hashlib,json
from pathlib import Path
P=Path('/tmp/k215-phase19-publication-draft');O=Path('/tmp/k215-phase19-capture-peer');R=Path('/home/codex/.codex/worktrees/ec20/Proofs')
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
read=lambda p:json.loads(Path(p).read_text())
def pin(p):p=Path(p);return {'path':str(p),'sha256':sha(p),'bytes':p.stat().st_size}
expected={'capture-final.py':'480a76e3fe9598fb3d5f3d75b1a52771cb27a100d6b4bdcf1ad4025f696711cd','build_config-final.py':'583b59da71860cb142c6662a812a1cd5c276bd9427886133c34b3a2a39976d17'}
for n,h in expected.items():
 assert sha(P/n)==h
 tree=ast.parse((P/n).read_text())
 for node in ast.walk(tree):
  if isinstance(node,ast.Call):
   if isinstance(node.func,ast.Name):assert node.func.id not in {'eval','exec','compile','__import__'}
   if isinstance(node.func,ast.Attribute):assert node.func.attr not in {'extract','extractall','system','Popen','run','check_call','check_output'}
  if isinstance(node,ast.Import):assert all(x.name in {'argparse','gzip','hashlib','json','re','tarfile'} for x in node.names)
  if isinstance(node,ast.ImportFrom):assert node.module in {'pathlib','io'}
config=read(P/'capture-config.template.json');assert config['status']=='DRAFT_PENDING_ACTUAL_RESULTS_DO_NOT_CAPTURE'
files=config['files'];assert len(files)==80 and len({r['logical'] for r in files})==80
for r in files+config['external_boundaries']:assert sha(r['source'])==r['sha256']
base=R/'Computability/BusyBeaver/Research/ZFC/k225-formal/verification/k215/simplification/phase18/lean'
core={'README.md','capture-config.json','capture.json','capture.py','check-plan.json','check.py','evidence.tar.gz','index.json','result-review.json','result.json','review_actual.py'}
assert len(config['external_boundaries'])==11 and {r['source'] for r in config['external_boundaries']}=={str(base/n) for n in core}
assert not any(Path(r['source']).is_relative_to(base) for r in files)
prod=str(R/'Computability/BusyBeaver/Research/ZFC/k225-formal/generate_l2dom.py')
assert any(r.get('historical_source')==prod and r['sha256']=='ed95a235509219df22cf07aa59d732d249d724571a3537cb436359487136fc64' for r in files)
assert any(r.get('historical_source')==prod and r['sha256']=='4453ac9a3745b4525575945d0aab506f270bbbbbbcf52c09a160f6c60f2ecd38' for r in files)
failed=Path('/tmp/k215-phase19-check/old-baseline-v3-run1');attempts=list((failed/'attempts').iterdir());assert len(attempts)==10
covered={r['source'] for r in files}
for attempt in attempts:
 paths=[p for p in attempt.iterdir() if p.suffix in {'.lean','.json','.log'}];assert len(paths)==3
 assert {str(p) for p in paths}<=covered
failed_metadata=[failed/n for n in ['before.json','inventory.json','completed.json','toolchain.json']]+[Path('/tmp/k215-phase19-check')/n for n in ['old-baseline-v3-outer.json','old-baseline-v3.stdout','old-baseline-v3.stderr','old-plan.json','build-old.py','old-freeze.json']]
assert {str(p) for p in failed_metadata}<=covered
report={'status':'PASS_SOURCE_HELPERS_AND_TEMPLATE_REVIEW_RUNTIME_BINDINGS_PENDING','helpers':[pin(P/n) for n in expected],'template':pin(P/'capture-config.template.json'),'external_boundary_manifest':pin(P/'phase18-boundaries.json'),'source_rows':80,'external_boundaries':11,'source_before_after_snapshots':16,'failed_attempt_triples':10,'failed_runtime_metadata':10,'expected_runtime_raw_files':562,'runtime_raw_formula':'2×226 workspace sources + (12+16)×3 accepted fresh source/log/record files + 2×3 candidate audit files + 2×10 metadata files','reviewed_properties':['Exact candidate and baseline receipt schemas gated before capture.','Baseline old canonical producer pin resolves through ed95 snapshot alias while current candidate producer4453 remains exact.','All candidate current present pins must bind; baseline pins may bind verified historical snapshots.','Only explicitly named inert files; no object paths or prior packet internal aliases; 11 exact phase18 external boundaries.','New-only output, content-addressed deduplicated blobs, sorted USTAR members and zero metadata; gzip mtime0.','Archive members rehashed by extraction into memory only; no filesystem extraction or supplied-code execution.','Failed old-baseline-v3 retains all ten attempt triples and original metadata; unaccepted Control219 raw remains historical context.'],'limits':'Final runtime-bindings JSON and the generated concrete capture config still require source/map review before capture. This receipt approves the named helper source and existing template only; it is not a capture result.','no_builder_capture_Lean_or_supplied_helper_execution':True,'no_canonical_or_staging_writes':True}
(O/'source-review.json').write_text(json.dumps(report,indent=2,ensure_ascii=False)+'\n');print(json.dumps({'status':report['status'],'review':pin(O/'source-review.json')},indent=2))
