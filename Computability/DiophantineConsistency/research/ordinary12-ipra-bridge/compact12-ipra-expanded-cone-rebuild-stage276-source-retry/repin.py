#!/usr/bin/env python3
"""Re-pin a single inline consistency-transfer proof at stage 276."""
from hashlib import sha256
import json
from pathlib import Path
HERE = Path(__file__).resolve().parent
REPO = HERE.parents[4]
OLD_CONE = HERE.parent / 'compact12-ipra-expanded-cone-rebuild-stage64-retry/cone-repinned.json'
FAILED = HERE.parent / 'compact12-ipra-expanded-cone-rebuild-stage276/observations/batch-056/stage-0276'
SOURCE = REPO / 'Logic/Interpretability/ZFCinPA/Lean/ZFCinPA/NativeSchema.lean'
OLD_SHA='266f7f619e3f01fc0a64c38036b14a5854c7264fef0cceb999a437fefab99982'
NEW_SHA='d6042135723adce366def247894e63cd3ad5d05d1dc57256718e6c82100f3210'
CONE_SHA='c9f4190a0d8807e5643f245a59ca53b23e52ca6c1dc1c1b74a5028651da049ec'
TERMINAL_SHA='763980f5977e32502f7c14ab67d05ee09d26232d499652496e33a1c342a955a8'
LOG_SHA='fd6622abe8021e5e334d9e8033af6737724e858dccf7a719d7f3e1f2bf2a8abb'
MODULE='ZFCinPA.NativeSchema'
def sha(p): return sha256(Path(p).read_bytes()).hexdigest()
def main():
    out=HERE/'cone-repinned.json'
    if out.exists(): raise RuntimeError('refusing to overwrite re-pin')
    for p,expected in ((OLD_CONE,CONE_SHA),(FAILED/'source.lean',OLD_SHA),(FAILED/'terminal.json',TERMINAL_SHA),(FAILED/'compile.log',LOG_SHA),(SOURCE,NEW_SHA)):
        if sha(p)!=expected: raise RuntimeError(f'input drift: {p}')
    before=(FAILED/'source.lean').read_text();after=SOURCE.read_text()
    old='''theorem consistent_ZF_of_native (h : nativeTheory.Consistent V) :
    (𝗭𝗙 : SetTheory).Consistent V :=
  InternalInterpretation.consistent_of_falsum_transfer provable_falsum_native_of_ZF h'''
    new='''theorem consistent_ZF_of_native (h : nativeTheory.Consistent V) :
    (𝗭𝗙 : SetTheory).Consistent V := by
  have e : (⌜(⊥ : Sentence ℒₛₑₜ)⌝ : V) = ^⊥ := by
    simp [LO.FirstOrder.Sentence.quote_def, LO.FirstOrder.Semiformula.quote_def]
  intro hZF
  apply h
  unfold LO.FirstOrder.Theory.Consistent at *
  rw [e] at hZF ⊢
  exact provable_falsum_native_of_ZF hZF'''
    if before.count(old)!=1 or before.replace(old,new,1)!=after: raise RuntimeError('unexpected source edit')
    terminal=json.loads((FAILED/'terminal.json').read_text());log=(FAILED/'compile.log').read_text()
    if terminal['exit_code']!=1 or terminal['success'] or terminal['object_sha256'] is not None or not terminal['guards_unchanged'] or 'Unknown identifier `InternalInterpretation.consistent_of_falsum_transfer`' not in log: raise RuntimeError('failed receipt mismatch')
    cone=json.loads(OLD_CONE.read_text());row=cone['candidate_sources'][MODULE]
    if row['source_sha256']!=OLD_SHA or cone['topological_candidate'][275]!=MODULE: raise RuntimeError('old cone target mismatch')
    row['source_sha256']=NEW_SHA;row['source_bytes']=len(SOURCE.read_bytes())
    cone['stage276_source_correction']={'module':MODULE,'old_sha256':OLD_SHA,'new_sha256':NEW_SHA,'old_cone_sha256':CONE_SHA,'failed_terminal_sha256':TERMINAL_SHA,'failed_log_sha256':LOG_SHA,'edit':'inline proof of consistency transfer without the newer helper declaration'}
    out.write_text(json.dumps(cone,indent=2,sort_keys=True)+'\n');(HERE/'corrected-source.lean').write_bytes(SOURCE.read_bytes());print(json.dumps({'cone_sha256':sha(out),'source_sha256':NEW_SHA}))
if __name__=='__main__': main()
