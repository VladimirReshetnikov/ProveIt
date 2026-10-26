from pathlib import Path
import re,difflib,json,hashlib,argparse
parser=argparse.ArgumentParser()
parser.add_argument('--repo',type=Path,required=True)
parser.add_argument('--output-dir',type=Path,default=Path(__file__).resolve().parent)
args=parser.parse_args()
root=args.repo
base=root/'Computability/DiophantineConsistency/Lean/DiophantineConsistency'
out=args.output_dir
out.mkdir(parents=True,exist_ok=True)
path=base/'CurrentControllerUnits2011.lean'
src=path.read_text()
start=src.index('/-- Exact power reduction at the first fixed prime')
end=src.index('theorem q_cast_47')
old=src[start:end]
new='''/-- A fixed point of one power map stays fixed under every iterate, including zero. -/
private theorem pow_pow_fixed {M : Type*} [Monoid M] (x : M) (a n : ℕ)
    (h : x^a=x) : x^(a^n)=x := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ,pow_mul,ih,h]

/-- The first literal residue is fixed by raising to the auxiliary power. -/
theorem power_dimension_47 (n : ℕ) :
    ((B^(dimension n) : ℕ) : ZMod 47) = (B : ZMod 47) := by
  simpa only [dimension,Nat.cast_pow] using
    pow_pow_fixed (B : ZMod 47) auxiliary n (by rw [B_cast_47]; unfold auxiliary; reduce_mod_char)

theorem power_dimension_2011 (n : ℕ) :
    ((B^(dimension n) : ℕ) : ZMod 2011) = (B : ZMod 2011) := by
  simpa only [dimension,Nat.cast_pow] using
    pow_pow_fixed (B : ZMod 2011) auxiliary n (by rw [B_cast_2011]; unfold auxiliary; reduce_mod_char)

theorem power_dimension_auxiliary (n : ℕ) :
    ((B^(dimension n) : ℕ) : ZMod auxiliary) = (B : ZMod auxiliary) := by
  simpa only [dimension,Nat.cast_pow] using
    pow_pow_fixed (B : ZMod auxiliary) auxiliary n (by rw [B_cast_auxiliary]; unfold auxiliary; reduce_mod_char)

'''
newsrc=(src[:start]+new+src[end:]).replace('import Mathlib.FieldTheory.Finite.Basic\n','').replace('prime. Both exponents may be zero. The fixed-prime power reductions use the\nchecked orders; the auxiliary-prime reduction is Frobenius, not an LTE claim.', 'prime. Both exponents may be zero. Three checked one-step power residues\nare propagated by one monoid fixed-point lemma at every exponent.')
(out/'CurrentControllerUnits2011.proposed.lean').write_text(newsrc)
patch=''.join(difflib.unified_diff(src.splitlines(True),newsrc.splitlines(True),fromfile='a/Computability/DiophantineConsistency/Lean/DiophantineConsistency/CurrentControllerUnits2011.lean',tofile='b/Computability/DiophantineConsistency/Lean/DiophantineConsistency/CurrentControllerUnits2011.lean'))
(out/'controller-power-fixed.patch').write_text(patch)
# A standalone comparison copies the exact relevant definitions and the original and replacement
# declarations, with dependency namespace names shortened. All arithmetic facts are checked here.
data=(base/'CurrentControllerData2011.lean').read_text()
part=data[data.index('theorem B_eq'):data.index('private theorem mod_of_cast')]
# Keep only the exact facts needed for original and replacement proofs. Do not use arbitrary axioms.
names=['B_eq','prime_auxiliary','order_coprime_47','order_coprime_2011','two_pow_47','two_pow_2011','proper_power_2011_2','proper_power_2011_3','proper_power_2011_67','two_order_47','two_order_2011','B_order_47','B_order_2011','B_cast_47','B_cast_2011','B_cast_auxiliary']
starts=list(re.finditer(r'^theorem ([A-Za-z0-9_]+)',part,re.M))
kept=[]
for i,m in enumerate(starts):
    if m.group(1) in names:
        kept.append(part[m.start():starts[i+1].start() if i+1<len(starts) else len(part)].rstrip())
fixture='''import Mathlib.FieldTheory.Finite.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar

/-! Exact arithmetic comparison fixture.  The controller's radix, B, auxiliary,
    dimension and the used source data facts are retained.  No theorem is assumed.
    This checks the three replaced proofs, not production clients or the full K dependency. -/
namespace ProofSimplification.ControllerPowerComparison
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
namespace CurrentMasks2011
def width : ℕ := 94517
def radix : ℕ := 2^47
end CurrentMasks2011
def d : ℕ := CurrentMasks2011.width
def B : ℕ := CurrentMasks2011.radix^2011
def auxiliary : ℕ := 120199
def dimension (n : ℕ) : ℕ := auxiliary^n
instance : NeZero auxiliary := ⟨by decide⟩
'''+ '\n\n'.join(kept) +'''

attribute [local irreducible] B

theorem auxiliary_modEq_23 : auxiliary ≡ 1 [MOD 23] := by decide
theorem auxiliary_modEq_402 : auxiliary ≡ 1 [MOD 402] := by decide

namespace Before
'''+old+'''
#print axioms power_dimension_47
#print axioms power_dimension_2011
#print axioms power_dimension_auxiliary
end Before

namespace After
'''+new+'''
#print axioms pow_pow_fixed
#print axioms power_dimension_47
#print axioms power_dimension_2011
#print axioms power_dimension_auxiliary

-- The zero exponent is explicitly supported by the public conclusions.
example : ((B^(dimension 0) : ℕ) : ZMod 47) = B := power_dimension_47 0
example : ((B^(dimension 0) : ℕ) : ZMod 2011) = B := power_dimension_2011 0
example : ((B^(dimension 0) : ℕ) : ZMod auxiliary) = B := power_dimension_auxiliary 0
end After
end ProofSimplification.ControllerPowerComparison
'''
(out/'ControllerPowerComparison.lean').write_text(fixture)
def nonempty(s):return sum(bool(l.strip()) for l in s.splitlines())
metrics={'source_commit':'e1c8914bc7064d9a8e7c06171a18069a949badd0','source_path':str(path.relative_to(root)),
 'source_sha256':hashlib.sha256(src.encode()).hexdigest(),'original_file_lines':len(src.splitlines()),'proposed_file_lines':len(newsrc.splitlines()),'net_physical_lines_removed':len(src.splitlines())-len(newsrc.splitlines()),'original_region_lines':len(old.splitlines()),'new_region_lines_including_helper':len(new.splitlines()),'original_nonempty_lines':nonempty(src),'proposed_nonempty_lines':nonempty(newsrc),'original_nonempty_code_lines':nonempty(re.sub(r'/\-.*?\-/','',src,flags=re.S)), 'proposed_nonempty_code_lines':nonempty(re.sub(r'/\-.*?\-/','',newsrc,flags=re.S)), 'validation_scope':'PowerFixedPoint generic/literal checks passed; exact source-shaped fixtures not validated after local I/O stall; production imports and clients not rebuilt'}
(out/'power-metrics.json').write_text(json.dumps(metrics,indent=2)+'\n')
print(json.dumps(metrics,indent=2))
