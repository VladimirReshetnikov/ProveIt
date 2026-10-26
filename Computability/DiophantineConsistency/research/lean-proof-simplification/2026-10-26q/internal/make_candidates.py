#!/usr/bin/env python3
"""Recreate exact source candidates; no repository file is modified."""
import argparse,difflib,hashlib,json,re,subprocess
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('--repo',required=True);p.add_argument('--out',required=True);a=p.parse_args()
repo=Path(a.repo).resolve();out=Path(a.out).resolve();out.mkdir(parents=True,exist_ok=True)
pin='9bd29079d5e1c6cc1c0bcaee6cb57d59b835cba9'
paths={
 'addition':'Computability/DiophantineConsistency/Lean/DiophantineConsistency/ObjectAdditionCancellation.lean',
 'multiplication':'Computability/DiophantineConsistency/Lean/DiophantineConsistency/ObjectNaturalZero.lean',
 'internal_sat':'SetTheory/BoundedConsistency/Lean/BoundedZFCConsistency/InternalSat.lean',
 'cases':'SetTheory/BoundedConsistency/Lean/BoundedZFCConsistency/NaturalCases.lean',
}
original={k:subprocess.check_output(['git','show',pin+':'+v],cwd=repo).decode() for k,v in paths.items() if k!='cases'}
addition=original['addition']
s=addition.index('private def zeroSumStage : Form :=')
e=addition.index('/-- There is no cancellation between two internal nonnegative summands. -/')
addition=addition[:s]+addition[e:]
s=addition.index('    let ee : Nat → V := fun _ => vempty H',addition.index('theorem addRel_zero_iff'))
e=addition.index('  · rintro ⟨rfl,rfl⟩',s)
addition=addition[:s]+'''    rcases nat_zero_or_succ H y hxy.2.1 with rfl | ⟨n,hn,rfl⟩
    · exact ⟨(addRel_unique H hxy (addRel_zero H hxy.1)).symm,rfl⟩
    · obtain ⟨b,hb⟩ := addRel_total H hxy.1 hn
      have he : vempty H=vsucc H b := addRel_unique H hxy (addRel_succ H hb)
      have hmem := vsucc_self H b
      rw [← he] at hmem
      exact False.elim (vempty_spec H b hmem)
'''+addition[e:]
multiplication=original['multiplication']
s=multiplication.index('private def zeroProductStage : Form :=')
e=multiplication.index('theorem mulRel_zero_iff',s)
multiplication=multiplication[:s]+multiplication[e:]
s=multiplication.index('    let ee : Nat → V := fun _ => vempty H')
e=multiplication.index('  · rintro (rfl | rfl)',s)
multiplication=multiplication[:s]+'''    rcases nat_zero_or_succ H y hy with rfl | ⟨n,hn,rfl⟩
    · exact Or.inr rfl
    · obtain ⟨b,hb⟩ := mulRel_total H hx hn
      have he : vempty H=addValue H b x := mulRel_unique H hxy (mulRel_succ H hb)
      have hadd : AddRel H b x (vempty H) :=
        he.symm ▸ addValue_rel H (mulRel_result_nat H hb) hx
      exact Or.inl ((addRel_zero_iff H b x).mp hadd).2
'''+multiplication[e:]
minimal={'addition':addition.replace('import DiophantineConsistency.ObjectAdditionLaws\n','import DiophantineConsistency.ObjectAdditionLaws\nimport BoundedZFCConsistency.InternalSat\n',1),'multiplication':multiplication}
internal_sat=original['internal_sat']
s=internal_sat.index('/-! ## Case analysis on internal natural numbers')
e=internal_sat.index('/-! ## Internal environments -/',s)
moved=internal_sat[s:e]
cases='''import BoundedZFCConsistency.OmegaRecursion
import BoundedZFCConsistency.CodePredicate

/-! Early zero/successor decomposition for arbitrary internal naturals.
The following block is moved unchanged from InternalSat. -/
namespace LeanProofs.BoundedZFCConsistency
open SetTheory SetTheory.Form
universe u
variable {V : Type u} {mem : V → V → Prop}

'''+moved+'''end LeanProofs.BoundedZFCConsistency
'''
internal_sat=(internal_sat[:s]+internal_sat[e:]).replace('import BoundedZFCConsistency.OmegaRecursion\n','import BoundedZFCConsistency.NaturalCases\n',1)
production={'addition':addition.replace('import DiophantineConsistency.ObjectAdditionLaws\n','import DiophantineConsistency.ObjectAdditionLaws\nimport BoundedZFCConsistency.NaturalCases\n',1),'multiplication':multiplication,'internal_sat':internal_sat,'cases':cases}
metrics={'snapshot':pin,'scope':'Physical source and UTF-8 byte changes against the raw pinned snapshot only; not incremental savings after hypothetical application of all earlier proposals.','variants':{}}
def lines(s):return len(s.splitlines())
def digest(s):return hashlib.sha256(s.encode()).hexdigest()
for name,contents in [('minimal',minimal),('production',production)]:
 patches=[];rows=[]
 for k,new in contents.items():
  old=original.get(k,'');rel=paths[k]
  dest=out/name/rel;dest.parent.mkdir(parents=True,exist_ok=True);dest.write_text(new)
  if old:
   base=out/'baseline'/rel;base.parent.mkdir(parents=True,exist_ok=True);base.write_text(old)
  patches.extend(difflib.unified_diff(old.splitlines(True),new.splitlines(True),fromfile=('a/'+rel if old else '/dev/null'),tofile='b/'+rel))
  rows.append({'path':rel,'old_lines':lines(old),'new_lines':lines(new),'delta_lines':lines(new)-lines(old),'old_bytes':len(old.encode()),'new_bytes':len(new.encode()),'delta_bytes':len(new.encode())-len(old.encode()),'old_sha256':digest(old) if old else None,'new_sha256':digest(new)})
 patch=out/(name+'.patch');patch.write_text(''.join(patches))
 check=subprocess.run(['git','apply','--check',str(patch)],cwd=out/'baseline',text=True,capture_output=True)
 metrics['variants'][name]={'files':rows,'delta_lines':sum(r['delta_lines'] for r in rows),'delta_bytes':sum(r['delta_bytes'] for r in rows),'patch_check':{'returncode':check.returncode,'stdout':check.stdout,'stderr':check.stderr},'actual_lean_modules_compiled':False}
for key,decl in [('addition','addRel_zero_iff'),('multiplication','mulRel_zero_iff')]:
 def header(s):return s[s.index('theorem '+decl):s.index(':= by',s.index('theorem '+decl))]
 assert header(original[key])==header(production[key]),decl
assert 'private def cancellationStage' in production['addition']
assert 'omega_ind H cancellationStage' in production['addition']
assert 'zeroSumStage' not in production['addition']
assert 'zeroProductStage' not in production['multiplication']
assert moved in cases
metrics['public_target_headers_unchanged']=True
metrics['cancellation_induction_retained']=True
metrics['zero_or_successor_block_moved_byte_identically']=True
metrics['new_cases_imports']=['BoundedZFCConsistency.OmegaRecursion','BoundedZFCConsistency.CodePredicate']
(out/'metrics.json').write_text(json.dumps(metrics,indent=2)+'\n')
print(json.dumps(metrics,indent=2))
