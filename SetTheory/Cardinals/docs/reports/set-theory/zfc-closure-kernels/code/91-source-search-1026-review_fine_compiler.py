#!/usr/bin/env python3
"""Independent reviewer for source-static facts and exact core macro support."""
from pathlib import Path
import hashlib,importlib.util,json,sys
ROOT=Path(__file__).resolve().parents[2]
FINE=ROOT/'work/fine_grammar'
RUNTIME=FINE/'runtime'
CODE=RUNTIME/'code'
REF=RUNTIME/'reference/context246/code'
sys.path[:0]=[str(CODE),str(REF)]
import audit_fine_grammar as audit
import rebuild_machines as rebuild
import check_macro_inductions as macro

def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
reviewed=[CODE/'audit_fine_grammar.py',CODE/'build_fine_machine.py']
before={p.name:sha(p) for p in reviewed}
source,terminals,names,allowed,encode=audit.make_vocabulary()
assert len(terminals)==44
assert all(w and all(c.isalnum() for c in w) for w in terminals)
# Exact full-table proof of reusable unary and list traversal rules.
table_path=FINE/'validation-trial/machine_old.tm'
macro.TABLE=rebuild.read_table(table_path)[0]
macro.prove_blocks();word=macro.prove_word_identity();macros=macro.prove_macros();marks=macro.prove_marks()
assert len(macro.BLOCK_PROOFS)==4 and len(macros)==3 and len(marks)==9
rows=set()
for result in list(macro.BLOCK_PROOFS.values())+macros+marks:
 for step in result['trace']:
  if 'state' in step:rows.add((step['state'],step['read']))
old=rebuild.read_table(RUNTIME/'reference/context246/machine/zfc_prefix246_old.tm')[0]
assert all(macro.TABLE[q,b]==old[q,b] for q,b in rows)
assert before=={p.name:sha(p) for p in reviewed}
result=dict(status='PASS_CODE_REVIEW_AND_EXACT_MACRO_REPLAY',reviewed_sources_sha256=before,
 table_sha256=sha(table_path),closed_atoms=44,fine_alphabet_symbols=len(set(''.join(terminals))),
 block_proofs=len(macro.BLOCK_PROOFS),complete_register_macros=len(macros),register_selectors=len(marks),
 core_rows_used=sorted(rows),word_identity=word,
 mathematical_scope='Symbolic unary and structural list inductions preserve arbitrary contexts; no finite register bound.',
 unchanged_source_assessment='The exact leaf-order, pinned-source comparison, RM branch bisimulation, all-instruction affine replay and exact blank tape replay provide the required gates for finer closed-token reassociation.',
 ax_override_boundary='An AX override changes the represented source and cannot inherit the original exact numerical register-program bisimulation. Supply a modified source explicitly, check emitted control against it, and separately prove the calculus/consistency transport.',
 limitations=['This script does not prove Python checker soundness in a proof assistant.','The trial whole-tape replay and residual pointer normalization must still be run for any final candidate.','The source code reviewer is an ordinary mathematical/code review, not a static correctness proof of all programs.'])
(Path(__file__).resolve().parent/'fine-compiler-review.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items() if k!='core_rows_used'},indent=2))
