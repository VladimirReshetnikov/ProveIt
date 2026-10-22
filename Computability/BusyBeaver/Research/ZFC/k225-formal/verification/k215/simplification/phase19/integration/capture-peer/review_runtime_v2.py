#!/usr/bin/env python3
"""Own ten-row runtime-binding delta review, without builder/capture execution."""
import hashlib,json
from pathlib import Path
P=Path('/tmp/k215-phase19-publication-draft');O=Path('/tmp/k215-phase19-capture-peer')
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
read=lambda p:json.loads(Path(p).read_text())
def pin(p):p=Path(p);return {'path':str(p),'sha256':sha(p),'bytes':p.stat().st_size}
old=read(P/'runtime-bindings-final.json');new=read(P/'runtime-bindings-final-v2.json')
assert sha(P/'runtime-bindings-final-v2.json')=='bda9d6166791dafb1940fde8772af4b0f09c0211811d30b6e146b6984a009ff3'
assert {k:v for k,v in old.items() if k!='extra_files'}=={k:v for k,v in new.items() if k!='extra_files'}
assert new['extra_files'][:31]==old['extra_files'] and len(new['extra_files'])==41
added=new['extra_files'][31:];assert len(added)==10
assert {Path(r['source']).parent.name for r in added}=={'k215-phase19-expanded-runner-peer','k215-phase19-warning-peer','k215-phase19-concrete-peer','k215-phase19-docs-peer'}
for r in added:
 p=Path(r['source']);assert p.is_absolute() and p.is_file() and not p.is_symlink() and 'objects' not in p.parts
 assert p.suffix in {'.md','.json','.py'}
assert len({r['logical'] for r in new['extra_files']})==41
cfg=read(P/'capture-config.template.json');names={r['logical'] for r in cfg['files']}
assert not names&{r['logical'] for r in added}
report={'status':'PASS_RUNTIME_BINDINGS_V2_TEN_CONTEXT_ROW_DELTA_REVIEW','prior_source_review':pin(O/'final-source-review.json'),'prior_bindings':pin(P/'runtime-bindings-final.json'),'runtime_bindings_v2':pin(P/'runtime-bindings-final-v2.json'),'added_rows':[dict(r,**pin(r['source'])) for r in added],'only_ten_extras_added':True,'helper_template_and_runtime_bindings_unchanged':True,'expected_raw_files':562,'expected_workspace_sources':452,'expected_context_rows':133,'expected_logical_entries':713,'external_boundaries':11,'findings':[],'scope':'Final expanded-runner, warning, concrete-map and docs source review context added only. Actual generated config and archive remain separate root-owned actions.','no_builder_capture_Lean_generator_or_archived_code_execution':True,'no_canonical_or_staging_writes':True}
(O/'runtime-v2-review.json').write_text(json.dumps(report,indent=2,ensure_ascii=False)+'\n');print(json.dumps({'status':report['status'],'review':pin(O/'runtime-v2-review.json')},indent=2))
