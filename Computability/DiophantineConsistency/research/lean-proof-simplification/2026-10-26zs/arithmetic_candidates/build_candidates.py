from pathlib import Path
import difflib,json,hashlib

def require(condition, message="Required check failed"):
    if not condition:
        raise RuntimeError(message)

root=Path(__file__).resolve().parent
src=root/'source/CurrentPackingRank2011.lean'
s=src.read_text(); require(hashlib.sha256(s.encode()).hexdigest() == '614f47e52f31dfc199f98387e5c720f1ae51fb0725ce8d9f21223b540a30c546', 'Immutable source hash mismatch')
start=s.index('  have hJ :=',s.index('theorem fourBlocks_cast')); end=s.index('\nomit [NeZero N] in',start)
old=s[start:end]; new='''  have hJ := CurrentNativePacking2011.repunit_pos (N:=N)
  have hHJ : 1 ≤ highPort*repunit width N := Nat.mul_pos highPort_pos hJ
  have hCq : C ≤ q N := by omega
  have hFq : F+1 ≤ q N := by omega
  have hb := congrArg (fun n : ℕ => (n : ℤ))
    (CurrentNativePacking2011.repunit_balance (N:=N))
  push_cast at hb
  unfold fourBlocks rank NativeRankVariation.windowRank
  push_cast [Nat.cast_sub (by omega : 1 ≤ C),Nat.cast_sub hHJ,
    Nat.cast_sub hCq,Nat.cast_sub (by omega : 1 ≤ q N-F),
    Nat.cast_sub (by omega : F ≤ q N)]
  linear_combination -(q N : ℤ) * hb
'''
require(len(old.splitlines()) == 23)
out=root/'fourblocks_certificate'; (out/'candidate').mkdir(parents=True,exist_ok=True)
(out/'candidate/CurrentPackingRank2011.lean').write_text(s[:start]+new+s[end:])
(out/'fourblocks_certificate.patch').write_text(''.join(difflib.unified_diff(s.splitlines(True),(s[:start]+new+s[end:]).splitlines(True),fromfile='a/Computability/DiophantineConsistency/Lean/DiophantineConsistency/CurrentPackingRank2011.lean',tofile='b/Computability/DiophantineConsistency/Lean/DiophantineConsistency/CurrentPackingRank2011.lean')))
metrics={'snapshot':'9d9d1123b39927d30363f1dcd53c23f0575c30ee','status':'UNCOMPILED; SELECTED local wrapper-detour cleanup; source-only review passed; novelty cleared at closing 451b548a','old_proof_lines':len(old.splitlines()),'new_proof_lines':len(new.splitlines()),'net_removed_lines':len(old.splitlines())-len(new.splitlines()),'old_module_lines':len(s.splitlines()),'new_module_lines':len((s[:start]+new+s[end:]).splitlines()),'old_proof_bytes':len(old.encode()),'new_proof_bytes':len(new.encode()),'helper_lines':0,'added_imports':0,'source_sha256':hashlib.sha256(s.encode()).hexdigest()}
(out/'metrics.json').write_text(json.dumps(metrics,indent=2)+'\n');print(json.dumps(metrics,indent=2));print((out/'fourblocks_certificate.patch').read_text())
# Independent second client cleanup, with combined artifact for review.
start2=s.index('  have hu :',s.index('theorem rank_gt_twice_window')); end2=s.index('\ntheorem fourBlocks_population',start2)
old2=s[start2:end2]
new2='''  have hc : 2*(width*N) < q N^3 := by
    rw [q_binary,← pow_mul]
    have h : (width*N)*3 < 2^((width*N)*3) := Nat.lt_two_pow_self
    omega
  have hn := hc.trans_le (fourBlocks_ge_cube C F hC hCF)
  have hz : ((2*(width*N) : ℕ) : ℤ) < (fourBlocks N C F : ℤ) := by exact_mod_cast hn
  rwa [fourBlocks_cast C F hC hCF] at hz
'''
require(len(old2.splitlines()) == 11)
out2=root/'rank_growth'; (out2/'candidate').mkdir(parents=True,exist_ok=True)
t2=s[:start2]+new2+s[end2:]
(out2/'candidate/CurrentPackingRank2011.lean').write_text(t2)
(out2/'rank_growth.patch').write_text(''.join(difflib.unified_diff(s.splitlines(True),t2.splitlines(True),fromfile='a/Computability/DiophantineConsistency/Lean/DiophantineConsistency/CurrentPackingRank2011.lean',tofile='b/Computability/DiophantineConsistency/Lean/DiophantineConsistency/CurrentPackingRank2011.lean')))
m2={'snapshot':metrics['snapshot'],'status':'UNCOMPILED; EXCLUDED from new credit: prior systematic power-normalization mechanism','old_proof_lines':len(old2.splitlines()),'new_proof_lines':len(new2.splitlines()),'net_removed_lines':len(old2.splitlines())-len(new2.splitlines()),'old_proof_bytes':len(old2.encode()),'new_proof_bytes':len(new2.encode()),'helper_lines':0,'added_imports':0,'source_sha256':metrics['source_sha256']}
(out2/'metrics.json').write_text(json.dumps(m2,indent=2)+'\n')
combined=s[:start]+new+s[end:start2]+new2+s[end2:]
co=root/'combined';(co/'candidate').mkdir(parents=True,exist_ok=True)
(co/'candidate/CurrentPackingRank2011.lean').write_text(combined)
(co/'combined.patch').write_text(''.join(difflib.unified_diff(s.splitlines(True),combined.splitlines(True),fromfile='a/Computability/DiophantineConsistency/Lean/DiophantineConsistency/CurrentPackingRank2011.lean',tofile='b/Computability/DiophantineConsistency/Lean/DiophantineConsistency/CurrentPackingRank2011.lean')))
mc={'snapshot':metrics['snapshot'],'status':'UNCOMPILED; COMPARISON ONLY: includes excluded growth cleanup','old_affected_proof_lines':len(old.splitlines())+len(old2.splitlines()),'new_affected_proof_lines':len(new.splitlines())+len(new2.splitlines()),'net_removed_lines':len(s.splitlines())-len(combined.splitlines()),'old_affected_proof_bytes':len(old.encode())+len(old2.encode()),'new_affected_proof_bytes':len(new.encode())+len(new2.encode()),'old_module_lines':len(s.splitlines()),'new_module_lines':len(combined.splitlines()),'helper_lines':0,'added_imports':0,'source_sha256':metrics['source_sha256'],'candidate_sha256':hashlib.sha256(combined.encode()).hexdigest()}
(co/'metrics.json').write_text(json.dumps(mc,indent=2)+'\n')
print(json.dumps(m2,indent=2));print(json.dumps(mc,indent=2))
