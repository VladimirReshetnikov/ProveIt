#!/usr/bin/env python3
"""Verify inert pins and freeze this audit's reproducible evidence."""
from pathlib import Path
import hashlib
import json

HERE=Path(__file__).resolve().parent
PACKET=Path('/workspace/shared/sandpile-repeated-target-20261004')
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
author=json.loads((PACKET/'evidence/manifest.json').read_text())
verified={}
for rel,expected in author['repeated_packet_files'].items():
    assert not Path(rel).is_absolute() and '..' not in Path(rel).parts
    observed=sha(PACKET/rel);assert observed==expected,rel
    verified[rel]=observed
predecessors={}
for rel,expected in author['approved_predecessor_pins_verified'].items():
    observed=sha(Path('/workspace/shared')/rel);assert observed==expected,rel
    predecessors[rel]=observed
assert verified['evidence/polynomial-dag.json']=='7bbc522a7e8ff8af23dd9f4b01b8fa783515b1e1de6941dc9a11e85c92f81ea6'
for name in ('source','arithmetic'):
    receipt=json.loads((HERE/(name+'-audit-receipt.json')).read_text())
    assert receipt['checker_sha256']==sha(HERE/('audit_'+name+'.py'))
    assert receipt['verdict']=='PASS'
semantic_expected={
 'report.md':'91490b88882044f06a4c874351059046d079c72bb3015c594d556099c95f7599',
 'independent_checks.py':'c0b837bdb83b3677a88e1cfc75189d540462cc16f27887291fe1970a3f49e60d',
 'independent-check-results.json':'4d7fe582a53138e1c7d42e0a1d2011bee6a58740c2e9827655072830ea1e86ff'}
for rel,h in semantic_expected.items():assert sha(HERE/'semantic-challenge'/rel)==h,rel
own={str(p.relative_to(HERE)):sha(p) for p in sorted(HERE.rglob('*'))
     if p.is_file() and p.name not in ('audit-manifest.json','freeze-audit-run.log')}
external=Path('/workspace/shared/sandpile-universality-interface-20261004')
corollary={name:sha(external/name) for name in ('REVIEW.md','PRIMARY_SOURCE.md','SOURCE_PINS.json')}
result={'verdict':'PASS','date':'2026-10-04',
 'theorem':'Exact ordinary finite legal target firing on the fixed base-32 physical tile/patch and signed-target interface; repeated firings permitted; no endpoint stability required.',
 'core_dependency':'Pinned constructive Pell matiyasevic and eq_pow_of_pell theorems; no new Lean run.',
 'counts':{'positive_witnesses':3865,'residuals':2251,'gates':17275,'exact_degree':18,'power':138,'subset':34,'and':8,'spread':6},
 'source_exact_checks':{'residuals':2251,'macro_interfaces':186,'ports':44,'all_nodes_live':True,'complete_SOS':True},
 'submitted_files_verified_unchanged':verified,
 'author_manifest_sha256':sha(PACKET/'evidence/manifest.json'),
 'approved_predecessors_verified_unchanged':predecessors,
 'independent_audit_files':own,
 'external_conditional_corollary_review_pins':corollary,
 'corollary_scope':'Computable many-one composition only, additionally conditional on published physical vertex simulation with disclosed initializer corrections; no paid raw-program compiler or fresh physical-graph audit.',
 'submitted_or_upstream_programs_executed_or_imported':False,'lean_run':False,'article_produced':False,
 'full_combined_physical_Pell_witness_materialized':False,
 'negative_control':'The full-radix slack relaxation falsely accepts initial [0,7]; the submitted lower-half mask rejects it.',
 'unresolved_core_findings':[]}
(HERE/'audit-manifest.json').write_text(json.dumps(result,sort_keys=True,indent=2)+'\n')
print(json.dumps({'verdict':'PASS','core_packet_files_unchanged':len(verified),'predecessor_files_unchanged':len(predecessors),'audit_files_pinned':len(own),'audit_report_sha256':sha(HERE/'AUDIT.md'),'audit_manifest_sha256':sha(HERE/'audit-manifest.json')},sort_keys=True,indent=2))
