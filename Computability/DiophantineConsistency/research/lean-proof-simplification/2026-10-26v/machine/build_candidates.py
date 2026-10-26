#!/usr/bin/env python3
"""Build uncompiled proof-body-only proposals from immutable source snapshots."""
from pathlib import Path
import hashlib, json, difflib, re
HERE=Path(__file__).resolve().parent
ROOT=HERE.parent
SRC=ROOT/'sources/Computability/DiophantineConsistency/Lean/DiophantineConsistency'
BASE='Computability/DiophantineConsistency/Lean/DiophantineConsistency'
rows=[
 dict(id='M1',module='WangMachineAction',name='act_next_none_iff',
      body='  rw [← stateNumber_injective.eq_iff, act_stateNumber a ha, stateNumber_none]\n',
      mechanism='Transport the halt equality through the already injective state-number encoding.'),
 dict(id='M2',module='WangMachineStep',name='color_action',
      body='  by_cases ho : x = cfg.head\n  · subst x\n    simp [color, (moved_head_ne a.move cfg.head).symm]\n  · simp [color, ho, Tape.read_write_of_ne cfg.tape ho a.write]\n',
      mechanism='Split on the write site only; the tape frame rule leaves destination classification symbolic.'),
 dict(id='M3',module='WangMachineTraceBounds',name='run_read_of_abs_ge',
      body='  exact run_read_outside M t x (le_abs\'.mp hx)\n',
      mechanism='Use the existing ordered-group absolute-value view matching the outside-interval premise.'),
]
metrics=[]
imports=[]
decls=[]
for row in rows:
    text=(SRC/(row['module']+'.lean')).read_text()
    start=text.index('theorem '+row['name']+' ')
    stop=text.index('\n\n',start)
    old=text[start:stop]+'\n'
    head,old_body=old.split(':= by\n',1)
    new=head+':= by\n'+row['body']
    patched=text[:start]+new.rstrip('\n')+text[stop:]
    p=HERE/'patched'/BASE/(row['module']+'.lean')
    p.parent.mkdir(parents=True,exist_ok=True);p.write_text(patched)
    patch=''.join(difflib.unified_diff(text.splitlines(True),patched.splitlines(True),fromfile='a/'+BASE+'/'+row['module']+'.lean',tofile='b/'+BASE+'/'+row['module']+'.lean'))
    (HERE/(row['id']+'-'+row['name']+'.patch')).write_text(patch)
    imports.append('import DiophantineConsistency.'+row['module'])
    decls.append(new.replace('theorem '+row['name']+' ','theorem '+row['name']+'_candidate ',1))
    metric={**row,'source_start_line':text[:start].count('\n')+1,'source_end_line':text[:stop].count('\n')+1,
            'before_declaration_nonblank':sum(bool(x.strip()) for x in old.splitlines()),
            'after_declaration_nonblank':sum(bool(x.strip()) for x in new.splitlines()),
            'before_body_nonblank':sum(bool(x.strip()) for x in old_body.splitlines()),
            'after_body_nonblank':sum(bool(x.strip()) for x in row['body'].splitlines()),
            'source_sha256':hashlib.sha256(text.encode()).hexdigest(),
            'patched_sha256':hashlib.sha256(patched.encode()).hexdigest(),
            'statement_preserved_byte_for_byte':head==new.split(':= by\n',1)[0],
            'validation':'uncompiled; no Lean or Lake installed; static review only'}
    metric.pop('body');metrics.append(metric)
preamble='''
/-!
Uncompiled source-exact candidates for ProveIt commit
22e020937caa81d0cb72a4f63071d6c0bcc1eba9.
The three imported original target theorems are NEVER used in their replacements.
Only earlier independently proved helpers are used. No new assumptions or axioms.
-/
namespace DiophantineConsistency.Round3MachineCandidates

open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open WangMachineEncoding WangMachineAction WangMachineStep WangMachineTraceBounds

'''
tests='''
-- The target<216 guard is material, not decorative.
example : (KDense215.act (false, false, 215)).next = none :=
  (act_next_none_iff_candidate _ (by decide)).mpr rfl

example : stateNumber (KDense215.act (false, false, 216)).next ≠ 216 := by decide

-- Old/new-head projections remain consequences of the same three-way formula.
example (cfg : Config 215) (a : Action 215) :
    color ({state := a.next, head := a.move.apply cfg.head,
      tape := Tape.write cfg.tape cfg.head a.write} : Config 215) cfg.head =
      a.write.toNat := by
  simpa only [if_neg (moved_head_ne a.move cfg.head).symm, if_pos rfl] using
    color_action_candidate cfg a cfg.head

example (cfg : Config 215) (a : Action 215) :
    color ({state := a.next, head := a.move.apply cfg.head,
      tape := Tape.write cfg.tape cfg.head a.write} : Config 215)
        (a.move.apply cfg.head) =
      headColor a.next (Tape.read cfg.tape (a.move.apply cfg.head)) := by
  simpa only [if_pos rfl] using
    color_action_candidate cfg a (a.move.apply cfg.head)

-- In particular, time zero retains every integer position, not only nonzero x.
example {n : ℕ} (M : Machine n) (x : ℤ) : Tape.read (M.run 0).tape x = false :=
  run_read_of_abs_ge_candidate M 0 x (abs_nonneg x)

end DiophantineConsistency.Round3MachineCandidates

#print axioms DiophantineConsistency.Round3MachineCandidates.act_next_none_iff_candidate
#print axioms DiophantineConsistency.Round3MachineCandidates.color_action_candidate
#print axioms DiophantineConsistency.Round3MachineCandidates.run_read_of_abs_ge_candidate
'''
(HERE/'MachineCandidates.lean').write_text('\n'.join(imports)+'\n'+preamble+'\n'.join(decls)+tests)
(HERE/'metrics.json').write_text(json.dumps({'pin':'22e020937caa81d0cb72a4f63071d6c0bcc1eba9','method':'nonblank declaration/body lines, same exact headers; excludes surrounding comments/imports/audits equally','candidates':metrics,'totals':{k:sum(r[k] for r in metrics) for k in ['before_declaration_nonblank','after_declaration_nonblank','before_body_nonblank','after_body_nonblank']}},indent=2)+'\n')
print(json.dumps(metrics,indent=2))
