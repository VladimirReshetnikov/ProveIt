#!/usr/bin/env python3
"""Re-pin the inline consistency-transfer proof at stage 419."""
from hashlib import sha256
import json
from pathlib import Path
HERE=Path(__file__).resolve().parent;REPO=HERE.parents[4]
OLD_CONE=HERE.parent/'compact12-ipra-expanded-cone-rebuild-stage317-source-retry/cone-repinned.json'
FAILED=HERE.parent/'compact12-ipra-expanded-cone-rebuild-stage419/observations/batch-084/stage-0419'
SOURCE=REPO/'Logic/Interpretability/ZFCinPA/Lean/ZFCinPA/QSchema.lean'
OLD='80c040905d9d0565f17f6cce8d8036549096088fc2a3559d9c7f6f752b8caa0a';NEW='0a8ffaa78ef63fe51f4b9c35ddea5ee28908204a4e4a06376b43c285c88ca0c1'
def sha(p):return sha256(Path(p).read_bytes()).hexdigest()
def main():
 out=HERE/'cone-repinned.json'
 if out.exists():raise RuntimeError('refusing to overwrite re-pin')
 for p,h in ((OLD_CONE,'eb5a8a3c8efb7b1d936d4c77ba2c6d201aff6d03f23c9e1697dd2b518aefcbf2'),(FAILED/'source.lean',OLD),(FAILED/'terminal.json','e767354a4e1bc253cb0dde92ea4a72d5ef1fb42f2d4a2f73c6797047510e941f'),(FAILED/'compile.log','028258a888e8d7c81c61b543c5a6a888988ceb6fcf51bd41b874c1b8213d2b6d'),(SOURCE,NEW)):
  if sha(p)!=h:raise RuntimeError(f'input drift: {p}')
 before=(FAILED/'source.lean').read_text();after=SOURCE.read_text()
 old='''theorem consistent_ZF_of_native (h : qTheory.Consistent V) :
    (𝗭𝗙 : SetTheory).Consistent V :=
  InternalInterpretation.consistent_of_falsum_transfer provable_falsum_native_of_ZF h'''
 new='''theorem consistent_ZF_of_native (h : qTheory.Consistent V) :
    (𝗭𝗙 : SetTheory).Consistent V := by
  have e : (⌜(⊥ : Sentence ℒₛₑₜ)⌝ : V) = ^⊥ := by
    simp [LO.FirstOrder.Sentence.quote_def, LO.FirstOrder.Semiformula.quote_def]
  intro hZF
  apply h
  unfold LO.FirstOrder.Theory.Consistent at *
  rw [e] at hZF ⊢
  exact provable_falsum_native_of_ZF hZF'''
 if before.count(old)!=1 or before.replace(old,new,1)!=after:raise RuntimeError('unexpected source edit')
 t=json.loads((FAILED/'terminal.json').read_text());log=(FAILED/'compile.log').read_text()
 if t['exit_code']!=1 or t['object_sha256'] is not None or not t['guards_unchanged'] or log.count('Unknown identifier `InternalInterpretation.consistent_of_falsum_transfer`')!=1:raise RuntimeError('failure receipt mismatch')
 cone=json.loads(OLD_CONE.read_text());row=cone['candidate_sources']['ZFCinPA.QSchema']
 if row['source_sha256']!=OLD or cone['topological_candidate'][418]!='ZFCinPA.QSchema':raise RuntimeError('old cone target mismatch')
 row['source_sha256']=NEW;row['source_bytes']=len(SOURCE.read_bytes());cone['stage419_source_correction']={'module':'ZFCinPA.QSchema','old_sha256':OLD,'new_sha256':NEW,'old_cone_sha256':sha(OLD_CONE),'failed_terminal_sha256':sha(FAILED/'terminal.json'),'failed_log_sha256':sha(FAILED/'compile.log'),'edit':'inline the consistency transfer proof'}
 out.write_text(json.dumps(cone,indent=2,sort_keys=True)+'\n');(HERE/'corrected-source.lean').write_bytes(SOURCE.read_bytes());print(json.dumps({'cone_sha256':sha(out),'source_sha256':NEW}))
if __name__=='__main__':main()
