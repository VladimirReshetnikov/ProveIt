#!/usr/bin/env python3
"""Re-pin the two inline consistency-transfer proofs at stage 317."""
from hashlib import sha256
import json
from pathlib import Path
HERE=Path(__file__).resolve().parent;REPO=HERE.parents[4]
OLD_CONE=HERE.parent/'compact12-ipra-expanded-cone-rebuild-stage276-source-retry/cone-repinned.json'
FAILED=HERE.parent/'compact12-ipra-expanded-cone-rebuild-stage317/observations/batch-064/stage-0317'
SOURCE=REPO/'Logic/Interpretability/ZFCinPA/Lean/ZFCinPA/LSchema.lean'
OLD='f7edf5e44ae544506a97859e7ab8937f9d69ff6b89cc821350dfb1b6f1be09f5';NEW='c68dbfb6e9b152ab71654de3a2b2cf3559ebe1f8e616edabd12e24209ea568f2'
def sha(p):return sha256(Path(p).read_bytes()).hexdigest()
def main():
 out=HERE/'cone-repinned.json'
 if out.exists():raise RuntimeError('refusing to overwrite re-pin')
 for p,h in ((OLD_CONE,'aa2ec030a843382be4dc6fe621174d80d46bf9799d9b52d1616dac52661a9699'),(FAILED/'source.lean',OLD),(FAILED/'terminal.json','88bfb2bc6571cc5ec5a42057d3a13f0df0c280ea7c257347f1170c7e91abfc0d'),(FAILED/'compile.log','35d364ee6cecd56d40079806c8dbb9818518b118b9a2a1af1e186c1ca5b4c0c2'),(SOURCE,NEW)):
  if sha(p)!=h:raise RuntimeError(f'input drift: {p}')
 before=(FAILED/'source.lean').read_text();after=SOURCE.read_text()
 for dst,src,hname in [('𝗭𝗙𝗖','𝗭𝗙','hZFC'),('𝗭𝗙','𝗭𝗙𝗖','hZF')]:
  old=f'''theorem consistent_{'ZFC_of_ZF' if dst=='𝗭𝗙𝗖' else 'ZF_of_ZFC'} (h : ({src} : SetTheory).Consistent W) :
    ({dst} : SetTheory).Consistent W :=
  InternalInterpretation.consistent_of_falsum_transfer provable_falsum_{'ZF_of_ZFC' if dst=='𝗭𝗙𝗖' else 'ZFC_of_ZF'} h'''
  new=f'''theorem consistent_{'ZFC_of_ZF' if dst=='𝗭𝗙𝗖' else 'ZF_of_ZFC'} (h : ({src} : SetTheory).Consistent W) :
    ({dst} : SetTheory).Consistent W := by
  have e : (⌜(⊥ : Sentence ℒₛₑₜ)⌝ : W) = ^⊥ := by
    simp [LO.FirstOrder.Sentence.quote_def, LO.FirstOrder.Semiformula.quote_def]
  intro {hname}
  apply h
  unfold LO.FirstOrder.Theory.Consistent at *
  rw [e] at {hname} ⊢
  exact provable_falsum_{'ZF_of_ZFC' if dst=='𝗭𝗙𝗖' else 'ZFC_of_ZF'} {hname}'''
  if before.count(old)!=1:raise RuntimeError('unexpected source pattern')
  before=before.replace(old,new,1)
 if before!=after:raise RuntimeError('unexpected source edit')
 t=json.loads((FAILED/'terminal.json').read_text());log=(FAILED/'compile.log').read_text()
 if t['exit_code']!=1 or t['object_sha256'] is not None or not t['guards_unchanged'] or log.count('Unknown identifier `InternalInterpretation.consistent_of_falsum_transfer`')!=2:raise RuntimeError('failure receipt mismatch')
 cone=json.loads(OLD_CONE.read_text());row=cone['candidate_sources']['ZFCinPA.LSchema']
 if row['source_sha256']!=OLD or cone['topological_candidate'][316]!='ZFCinPA.LSchema':raise RuntimeError('old cone target mismatch')
 row['source_sha256']=NEW;row['source_bytes']=len(SOURCE.read_bytes());cone['stage317_source_correction']={'module':'ZFCinPA.LSchema','old_sha256':OLD,'new_sha256':NEW,'old_cone_sha256':sha(OLD_CONE),'failed_terminal_sha256':sha(FAILED/'terminal.json'),'failed_log_sha256':sha(FAILED/'compile.log'),'edit':'inline the two consistency transfer proofs'}
 out.write_text(json.dumps(cone,indent=2,sort_keys=True)+'\n');(HERE/'corrected-source.lean').write_bytes(SOURCE.read_bytes());print(json.dumps({'cone_sha256':sha(out),'source_sha256':NEW}))
if __name__=='__main__':main()
