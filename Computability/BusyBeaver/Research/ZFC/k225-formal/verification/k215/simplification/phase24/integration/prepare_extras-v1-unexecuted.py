"""Owned bounded inert publication history; no compiler/code execution or objects."""
from pathlib import Path
import argparse,hashlib,json
p=argparse.ArgumentParser();p.add_argument('--out',type=Path,required=True);a=p.parse_args()
assert a.out.is_absolute() and not a.out.exists() and not a.out.is_symlink()
allowed={'.json','.py','.md','.diff','.patch','.txt','.lean','.log','.stdout','.stderr'}
rows={}
def add(path,role,pin=None):
 path=Path(path).absolute();assert path.is_file() and not path.is_symlink()
 assert 'objects' not in path.parts and path.suffix in allowed,path
 b=path.read_bytes();h=hashlib.sha256(b).hexdigest()
 if pin is not None:assert h==pin,path
 row={'path':str(path),'sha256':h,'role':role}
 if str(path) in rows:assert rows[str(path)]['sha256']==h
 else:rows[str(path)]=row
manifest=Path('/tmp/k215-phase24-capture-draft-v2/diagnostic-extras.json')
add(manifest,'explicit_diagnostic_history_manifest','809329e9830a51cb5e3e48df9dfe255fbc28c9f5ca23c0729d45d70bedbdbe48')
for row in json.loads(manifest.read_text())['files']:add(row['path'],row['role'],row['sha256'])
groups={
 '/tmp/k215-phase24-native-leads':'initial_native_source_proposal',
 '/tmp/k215-phase24-logic-leads':'adopted_logic_source_proposal',
 '/tmp/k215-phase24-machine-leads':'adopted_selector_source_proposal',
 '/tmp/k215-phase24-upstream':'attributed_upstream_runtime_source',
 '/tmp/k215-phase24-tools-v1':'unexecuted_helper_preparation_history',
 '/tmp/k215-phase24-tools-v2':'reviewed_executed_runtime_assets',
 '/tmp/k215-phase24-native-repair-v1':'rejected_first_predicate_annotation_history',
 '/tmp/k215-phase24-native-repair-v2':'final_typed_reflexive_annotation_repair',
 '/tmp/k215-phase24-source-peer':'source_reviews_and_upstream_coordination',
 '/tmp/k215-phase24-final-source-plan-peer':'final_source_and_plan_binding_review',
 '/tmp/k215-phase24-machine-peer':'independent_selector_source_review',
 '/tmp/k215-phase24-sources-v1':'original_uncompiled_source_specification',
 '/tmp/k215-phase24-sources-v2':'intermediate_predicate_source_specification',
 '/tmp/k215-phase24-sources-v3':'final_source_specification',
 '/tmp/k215-phase24-check-v1':'unexecuted_original_full_plan',
 '/tmp/k215-phase24-check-v2':'unexecuted_intermediate_full_plan',
 '/tmp/k215-phase24-capture-draft-v1':'unexecuted_previous_capture_draft',
 '/tmp/k215-phase24-capture-draft-v2':'reviewed_current_capture_controls',
 '/tmp/k215-phase24-docs-draft':'original_pending_documentation',
 '/tmp/k215-phase24-docs-draft-v2':'final_source_pending_documentation',
 '/tmp/k215-phase24-parent-docs-draft':'pending_parent_documentation',
 '/tmp/k215-phase24-publication-readback-draft':'owned_postcopy_reader_source',
}
for directory,role in groups.items():
 directory=Path(directory);assert directory.is_dir(),directory
 for path in sorted(directory.rglob('*')):
  if path.is_file() and 'objects' not in path.parts and path.suffix in allowed:add(path,role)
for name in ['run_once.py','candidate-plan.json','freeze.json','candidate-preflight-outer.json','candidate-preflight.stdout','candidate-preflight.stderr','candidate-preflight-run1/preflight.json']:
 add(Path('/tmp/k215-phase24-check-v3')/name,'final_full_plan_or_metadata_preflight')
# Current full-run receipts/workspaces are added by build_config, after actual PASS.
for path in sorted(Path(__file__).parent.iterdir()):
 if path.is_file() and path!=a.out and path.suffix in allowed and not path.name.startswith('capture-') and not path.name.startswith('config-'):add(path,'owned_integration_source_or_receipt')
for name in ['tools-peer.json','diagnostic-plan-peer.json','capture-tools-peer.json','source-adoption-v1.json']:
 add('/tmp/k215-phase24-'+name,'source_helper_or_preparation_review')
add(__file__,'owned_history_manifest_builder')
with a.out.open('x') as f:json.dump({'status':'EXPLICIT_INERT_SOURCE_AND_RAW_HISTORY_EXTRAS','files':list(rows.values()),'objects_included':False,'compiler_execution':False,'scope':'All four terminal diagnostics, reviewed source/control packages and preparation history. Full acceptance is separate; old phase23 leaf remains external.'},f,indent=2);f.write('\n')
print(json.dumps({'files':len(rows),'manifest':str(a.out),'sha256':hashlib.sha256(a.out.read_bytes()).hexdigest()}))
