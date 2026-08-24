from mpmath import mp, mpf, log, floor
mp.dps = 80
th = log(3) / log(2)

# Ladder of enclosures: (lowerNum, lowerDen) with 2^Lp < 3^Lq (so Lp/Lq < theta),
# (upperNum, upperDen) with 3^Uq < 2^Up (so Up/Uq > theta).  Tier = (lower, upper) pair.
lowers = [(569, 359), (1054, 665), (25781, 16266), (50508, 31867), (176251, 111202), (478245, 301739)]
uppers = [(485, 306), (1539, 971), (24727, 15601), (125743, 79335), (301994, 190537)]
for p, q in lowers:
    assert 2 ** p < 3 ** q, (p, q)
for p, q in uppers:
    assert 3 ** q < 2 ** p, (p, q)

LO, HI = 4096, 8192
rows = []
tiers = {}
tierlist = []
for m in range(LO, HI):
    if m & (m - 1) == 0:
        rows.append((0, 0)); continue
    a = int(floor(mpf(m) ** th))
    # exact verification that a = floor(m^theta): a^? we only need the certificate inequalities.
    lo = next(i for i, (p, q) in enumerate(lowers) if pow(a, q) < pow(m, p))
    up = next(i for i, (p, q) in enumerate(uppers) if pow(m, p) < pow(a + 1, q))
    key = (lo, up)
    if key not in tiers:
        tiers[key] = len(tierlist); tierlist.append(key)
    rows.append((a, tiers[key]))
assert len(rows) == HI - LO
print("tiers:", tierlist)
import collections
print(collections.Counter(t for _, t in rows))

def fmt_rows(rows):
    out = []
    line = "   "
    for i, (a, t) in enumerate(rows):
        s = f" ({a}, {t}),"
        if len(line) + len(s) > 96:
            out.append(line); line = "   "
        line += s
    out.append(line)
    txt = "\n".join(out)
    return txt.rstrip(",")

maxexp = max(max(lowers[l][0], uppers[u][0]) for (l, u) in tierlist)
thr = (maxexp // 10000 + 2) * 10000

tier_arms = []
spec_disj = []
bases = []
for t, (l, u) in enumerate(tierlist):
    Lp, Lq = lowers[l]; Up, Uq = uppers[u]
    tier_arms.append(f"  | {t} => decide (a ^ {Lq} < m ^ {Lp}) && decide (m ^ {Up} < (a + 1) ^ {Uq})")
    spec_disj.append(f"    (a ^ {Lq} < m ^ {Lp} ∧ m ^ {Up} < (a + 1) ^ {Uq})")
    bases.append(f"set_option exponentiation.threshold {thr} in\nprivate theorem lower_base8192_t{t} : 2 ^ {Lp} < 3 ^ {Lq} := by norm_num\n"
                 f"set_option exponentiation.threshold {thr} in\nprivate theorem upper_base8192_t{t} : 3 ^ {Uq} < 2 ^ {Up} := by norm_num")
nt = len(tierlist)

def ors(k, n):
    # proof term selecting the k-th disjunct of an n-fold right-nested Or
    if n == 1: return "h"
    if k == 0: return "Or.inl h"
    inner = ors(k - 1, n - 1)
    return f"Or.inr ({inner})"

spec_arms = []
for t in range(nt):
    spec_arms.append(f"  | {t} =>\n    simp only [tieredCheck8192, Bool.and_eq_true, decide_eq_true_eq] at h\n    exact {ors(t, nt)}")
spec_arms.append(f"  | _ + {nt} =>\n    simp [tieredCheck8192] at h")

rc = " | ".join(["hc"] * nt)
final_cases = "\n".join(
    f"    · exact cert_contradiction8192 hpowm h₃ hapos hmpos hxnonneg\n        (by norm_num) (by norm_num) lower_base8192_t{t} upper_base8192_t{t} hc.1 hc.2"
    for t in range(nt))

lean = f'''import ExponentialIdentities.TwoBaseIntegerExponent.FiniteCheck4096

namespace LeanProofs.TwoBaseIntegerExponent

open Set

/-!
This file extends the exact finite verification from `4096` to `8192`: any real exponent with
`2 ^ x` and `3 ^ x` both integral and `2 ^ x < 8192` is an integer, so a nonintegral solution
must satisfy `x ≥ 13`.

The architecture is that of `FiniteCheck4096`.  For each nonpower-of-two `m` with
`4096 ≤ m < 8192` the table records `a = ⌊m ^ (log 3 / log 2)⌋` and a tier selecting a pair of
rational enclosures of `log 3 / log 2`; the lower enclosures are continued-fraction
convergents and one semiconvergent (`478245/301739`, needed only for `m = 5143, 6714`), the
upper enclosures are convergents.  The two integer power comparisons `a ^ Lq < m ^ Lp` and
`m ^ Up < (a + 1) ^ Uq`, together with the tier base enclosures `2 ^ Lp < 3 ^ Lq` and
`3 ^ Uq < 2 ^ Up`, trap `m ^ (log 3 / log 2)` strictly between consecutive integers.  The
table was generated with `mpmath` and every row re-verified with exact Python big-integer
arithmetic before being replayed by the kernel through `decide`.
-/

set_option maxRecDepth 200000 in
/-- Per-value certificates for `4096 ≤ m < 8192`: entry `i` holds
`(⌊(4096 + i) ^ (log 3 / log 2)⌋, tier)`, with a dummy `(0, 0)` at the power of two. -/
private def certTable8192 : List (ℕ × ℕ) := [
{fmt_rows(rows)}
]

/-- The tiered pair of integer power comparisons for the certificate `(m, a)`. -/
private def tieredCheck8192 (t m a : ℕ) : Bool :=
  match t with
{chr(10).join(tier_arms)}
  | _ + {nt} => false

/-- Row check: index `i` corresponds to `m = 4096 + i`; the power of two `4096` is exempt. -/
private def certOne8192 (i a t : ℕ) : Bool :=
  (i == 0) || (decide (0 < a) && tieredCheck8192 t (4096 + i) a)

/-- Sequential check of all rows starting at index `i`. -/
private def checkFrom8192 : ℕ → List (ℕ × ℕ) → Bool
  | _, [] => true
  | i, (a, t) :: rest => certOne8192 i a t && checkFrom8192 (i + 1) rest

set_option maxRecDepth 200000 in
set_option maxHeartbeats 80000000 in
set_option exponentiation.threshold {thr} in
private theorem certTable8192_all : checkFrom8192 0 certTable8192 = true := by decide

set_option maxRecDepth 200000 in
private theorem certTable8192_length : certTable8192.length = {HI - LO} := by decide

private theorem checkFrom8192_spec {{rows : List (ℕ × ℕ)}} {{i0 : ℕ}}
    (h : checkFrom8192 i0 rows = true) :
    ∀ j, j < rows.length →
      certOne8192 (i0 + j) (rows.getD j (0, 0)).1 (rows.getD j (0, 0)).2 = true := by
  induction rows generalizing i0 with
  | nil =>
    intro j hj
    simp at hj
  | cons head tail ih =>
    intro j hj
    obtain ⟨a, t⟩ := head
    simp only [checkFrom8192, Bool.and_eq_true] at h
    cases j with
    | zero => simpa using h.1
    | succ j' =>
      have htail := ih h.2 j' (Nat.lt_of_succ_lt_succ (by simpa using hj))
      have harith : i0 + (j' + 1) = i0 + 1 + j' := by omega
      simpa [List.getD_cons_succ, harith] using htail

private theorem certOne8192_spec {{i a t : ℕ}} (h : certOne8192 i a t = true) :
    i = 0 ∨ (0 < a ∧ tieredCheck8192 t (4096 + i) a = true) := by
  simp only [certOne8192, Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true,
    decide_eq_true_eq] at h
  tauto

private theorem tieredCheck8192_spec {{t m a : ℕ}} (h : tieredCheck8192 t m a = true) :
{" ∨" + chr(10)}'''.rstrip(" ∨\n") if False else None

# build the spec statement separately for clarity
spec_stmt = " ∨\n".join(spec_disj)
lean = f'''import ExponentialIdentities.TwoBaseIntegerExponent.FiniteCheck4096

namespace LeanProofs.TwoBaseIntegerExponent

open Set

/-!
This file extends the exact finite verification from `4096` to `8192`: any real exponent with
`2 ^ x` and `3 ^ x` both integral and `2 ^ x < 8192` is an integer, so a nonintegral solution
must satisfy `x ≥ 13`.

The architecture is that of `FiniteCheck4096`.  For each nonpower-of-two `m` with
`4096 ≤ m < 8192` the table records `a = ⌊m ^ (log 3 / log 2)⌋` and a tier selecting a pair of
rational enclosures of `log 3 / log 2`; the lower enclosures are continued-fraction
convergents and one semiconvergent (`478245/301739`, needed only for `m = 5143, 6714`), the
upper enclosures are convergents.  The two integer power comparisons `a ^ Lq < m ^ Lp` and
`m ^ Up < (a + 1) ^ Uq`, together with the tier base enclosures `2 ^ Lp < 3 ^ Lq` and
`3 ^ Uq < 2 ^ Up`, trap `m ^ (log 3 / log 2)` strictly between consecutive integers.  The
table was generated with `mpmath` and every row re-verified with exact Python big-integer
arithmetic before being replayed by the kernel through `decide`.
-/

set_option maxRecDepth 200000 in
/-- Per-value certificates for `4096 ≤ m < 8192`: entry `i` holds
`(⌊(4096 + i) ^ (log 3 / log 2)⌋, tier)`, with a dummy `(0, 0)` at the power of two. -/
private def certTable8192 : List (ℕ × ℕ) := [
{fmt_rows(rows)}
]

/-- The tiered pair of integer power comparisons for the certificate `(m, a)`. -/
private def tieredCheck8192 (t m a : ℕ) : Bool :=
  match t with
{chr(10).join(tier_arms)}
  | _ + {nt} => false

/-- Row check: index `i` corresponds to `m = 4096 + i`; the power of two `4096` is exempt. -/
private def certOne8192 (i a t : ℕ) : Bool :=
  (i == 0) || (decide (0 < a) && tieredCheck8192 t (4096 + i) a)

/-- Sequential check of all rows starting at index `i`. -/
private def checkFrom8192 : ℕ → List (ℕ × ℕ) → Bool
  | _, [] => true
  | i, (a, t) :: rest => certOne8192 i a t && checkFrom8192 (i + 1) rest

set_option maxRecDepth 200000 in
set_option maxHeartbeats 80000000 in
set_option exponentiation.threshold {thr} in
private theorem certTable8192_all : checkFrom8192 0 certTable8192 = true := by decide

set_option maxRecDepth 200000 in
private theorem certTable8192_length : certTable8192.length = {HI - LO} := by decide

private theorem checkFrom8192_spec {{rows : List (ℕ × ℕ)}} {{i0 : ℕ}}
    (h : checkFrom8192 i0 rows = true) :
    ∀ j, j < rows.length →
      certOne8192 (i0 + j) (rows.getD j (0, 0)).1 (rows.getD j (0, 0)).2 = true := by
  induction rows generalizing i0 with
  | nil =>
    intro j hj
    simp at hj
  | cons head tail ih =>
    intro j hj
    obtain ⟨a, t⟩ := head
    simp only [checkFrom8192, Bool.and_eq_true] at h
    cases j with
    | zero => simpa using h.1
    | succ j' =>
      have htail := ih h.2 j' (Nat.lt_of_succ_lt_succ (by simpa using hj))
      have harith : i0 + (j' + 1) = i0 + 1 + j' := by omega
      simpa [List.getD_cons_succ, harith] using htail

private theorem certOne8192_spec {{i a t : ℕ}} (h : certOne8192 i a t = true) :
    i = 0 ∨ (0 < a ∧ tieredCheck8192 t (4096 + i) a = true) := by
  simp only [certOne8192, Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true,
    decide_eq_true_eq] at h
  tauto

private theorem tieredCheck8192_spec {{t m a : ℕ}} (h : tieredCheck8192 t m a = true) :
{spec_stmt} := by
  match t with
{chr(10).join(spec_arms)}

/-! ### Base enclosures for the tiers -/

{chr(10).join(bases)}

/-! ### From certificates to the analytic contradiction -/

private theorem mul_log_lt_mul_log_of_pow_lt8192
    {{a b p q : ℕ}} (ha : 0 < a) (hb : 0 < b) (hpow : a ^ p < b ^ q) :
    (p : ℝ) * Real.log (a : ℝ) < (q : ℝ) * Real.log (b : ℝ) := by
  have hpowR : (a : ℝ) ^ p < (b : ℝ) ^ q := by exact_mod_cast hpow
  have hlog := Real.strictMonoOn_log
    (by simpa only [Set.mem_Ioi] using (show 0 < (a : ℝ) ^ p by positivity))
    (by simpa only [Set.mem_Ioi] using (show 0 < (b : ℝ) ^ q by positivity)) hpowR
  simpa only [Real.log_pow] using hlog

private theorem no_integer_between_consecutive_naturals8192
    {{y : ℝ}} {{a : ℕ}}
    (hy : y ∈ Set.range ((↑) : ℤ → ℝ))
    (hlow : (a : ℝ) < y) (hupp : y < (a + 1 : ℕ)) : False := by
  obtain ⟨z, rfl⟩ := hy
  have hzlow : (a : ℤ) < z := by exact_mod_cast hlow
  have hzupp : z < (a : ℤ) + 1 := by exact_mod_cast hupp
  omega

private theorem cert_contradiction8192
    {{x : ℝ}} {{m a lowerNum lowerDen upperNum upperDen : ℕ}}
    (h₂ : (2 : ℝ) ^ x = (m : ℝ))
    (h₃ : (3 : ℝ) ^ x ∈ Set.range ((↑) : ℤ → ℝ))
    (ha : 0 < a) (hmpos : 0 < m) (hxnonneg : 0 ≤ x)
    (hlowerDenPos : 0 < lowerDen) (hupperDenPos : 0 < upperDen)
    (hlowerBase : 2 ^ lowerNum < 3 ^ lowerDen)
    (hupperBase : 3 ^ upperDen < 2 ^ upperNum)
    (hmLower : a ^ lowerDen < m ^ lowerNum)
    (hmUpper : m ^ upperNum < (a + 1) ^ upperDen) : False := by
  have hlogm := congrArg Real.log h₂
  rw [Real.log_rpow (by norm_num : (0 : ℝ) < 2)] at hlogm
  have hcommonLower :
      (lowerNum : ℝ) * Real.log 2 < lowerDen * Real.log 3 :=
    mul_log_lt_mul_log_of_pow_lt8192 (by norm_num) (by norm_num) hlowerBase
  have hcommonUpper :
      (upperDen : ℝ) * Real.log 3 < upperNum * Real.log 2 :=
    mul_log_lt_mul_log_of_pow_lt8192 (by norm_num) (by norm_num) hupperBase
  have hmLowerLog :
      (lowerDen : ℝ) * Real.log a < lowerNum * Real.log m :=
    mul_log_lt_mul_log_of_pow_lt8192 ha hmpos hmLower
  have hmUpperLog :
      (upperNum : ℝ) * Real.log m < upperDen * Real.log ((a + 1 : ℕ) : ℝ) :=
    mul_log_lt_mul_log_of_pow_lt8192 hmpos (by omega) hmUpper
  have hlowerDenPosR : (0 : ℝ) < lowerDen := by exact_mod_cast hlowerDenPos
  have hupperDenPosR : (0 : ℝ) < upperDen := by exact_mod_cast hupperDenPos
  have hLowerLog : Real.log a < x * Real.log 3 := by
    apply lt_of_mul_lt_mul_left _ hlowerDenPosR.le
    calc
      (lowerDen : ℝ) * Real.log a < lowerNum * Real.log m := hmLowerLog
      _ = x * (lowerNum * Real.log 2) := by rw [← hlogm]; ring
      _ ≤ x * (lowerDen * Real.log 3) := mul_le_mul_of_nonneg_left hcommonLower.le hxnonneg
      _ = lowerDen * (x * Real.log 3) := by ring
  have hUpperLog : x * Real.log 3 < Real.log ((a + 1 : ℕ) : ℝ) := by
    apply lt_of_mul_lt_mul_left _ hupperDenPosR.le
    calc
      (upperDen : ℝ) * (x * Real.log 3) = x * (upperDen * Real.log 3) := by ring
      _ ≤ x * (upperNum * Real.log 2) := mul_le_mul_of_nonneg_left hcommonUpper.le hxnonneg
      _ = upperNum * Real.log m := by rw [← hlogm]; ring
      _ < upperDen * Real.log ((a + 1 : ℕ) : ℝ) := hmUpperLog
  have hLower : (a : ℝ) < (3 : ℝ) ^ x := by
    rw [Real.lt_rpow_iff_log_lt (by positivity) (by norm_num : (0 : ℝ) < 3)]
    exact hLowerLog
  have hUpper : (3 : ℝ) ^ x < (a + 1 : ℕ) := by
    rw [Real.rpow_lt_iff_lt_log (by norm_num : (0 : ℝ) < 3) (by positivity)]
    exact hUpperLog
  exact no_integer_between_consecutive_naturals8192 h₃ hLower hUpper

private theorem integer_of_two_rpow_eq_pow_two8192 {{x : ℝ}} {{m k : ℕ}}
    (hm : m = 2 ^ k) (hpowm : (2 : ℝ) ^ x = (m : ℝ)) :
    x ∈ Set.range ((↑) : ℤ → ℝ) := by
  refine ⟨k, ?_⟩
  have hx : x = (k : ℝ) := by
    apply (Real.strictMono_rpow_of_base_gt_one (by norm_num : (1 : ℝ) < 2)).injective
    show (2 : ℝ) ^ x = (2 : ℝ) ^ (k : ℝ)
    rw [hpowm, hm, Real.rpow_natCast]
    push_cast
    ring
  rw [hx]
  push_cast
  ring

/-- If both powers are integral and `2 ^ x < 8192`, then `x` is an integer. -/
theorem integer_of_two_three_rpow_integer_of_two_rpow_lt_8192 {{x : ℝ}}
    (h₂ : (2 : ℝ) ^ x ∈ Set.range ((↑) : ℤ → ℝ))
    (h₃ : (3 : ℝ) ^ x ∈ Set.range ((↑) : ℤ → ℝ))
    (hlt : (2 : ℝ) ^ x < 8192) :
    x ∈ Set.range ((↑) : ℤ → ℝ) := by
  by_cases hsmall : (2 : ℝ) ^ x < 4096
  · exact integer_of_two_three_rpow_integer_of_two_rpow_lt_4096 h₂ h₃ hsmall
  obtain ⟨z, hz⟩ := h₂
  have hp : 0 < (2 : ℝ) ^ x := Real.rpow_pos_of_pos (by norm_num) _
  have hzpos : 0 < z := by exact_mod_cast (hz.symm ▸ hp)
  have hzloR : (4096 : ℝ) ≤ (z : ℝ) := by
    calc
      (4096 : ℝ) ≤ 2 ^ x := not_lt.mp hsmall
      _ = (z : ℝ) := hz.symm
  have hzlo : 4096 ≤ z := by exact_mod_cast hzloR
  have hzhi : z < 8192 := by exact_mod_cast (hz.symm ▸ hlt)
  have hxnonneg : 0 ≤ x := IntegerExponent.nonneg_of_two_rpow_integer ⟨z, hz⟩
  lift z to ℕ using hzpos.le with m hmcast
  have hmlo : 4096 ≤ m := by exact_mod_cast hzlo
  have hmhi : m < 8192 := by exact_mod_cast hzhi
  have hpowm : (2 : ℝ) ^ x = (m : ℝ) := hz.symm
  have hidx : m - 4096 < certTable8192.length := by
    rw [certTable8192_length]
    omega
  have hcert := checkFrom8192_spec certTable8192_all (m - 4096) hidx
  rw [Nat.zero_add] at hcert
  rcases certOne8192_spec hcert with h0 | ⟨hapos, htier⟩
  · exact integer_of_two_rpow_eq_pow_two8192 (show m = 2 ^ 12 by norm_num; omega) hpowm
  · exfalso
    rw [show 4096 + (m - 4096) = m from by omega] at htier
    have hmpos : 0 < m := by omega
    rcases tieredCheck8192_spec htier with {rc}
{final_cases}

/-- In exponent coordinates, every nonintegral two-base solution is at least `13`. -/
theorem thirteen_le_of_not_integer_of_two_three_rpow_integer {{x : ℝ}}
    (h₂ : (2 : ℝ) ^ x ∈ Set.range ((↑) : ℤ → ℝ))
    (h₃ : (3 : ℝ) ^ x ∈ Set.range ((↑) : ℤ → ℝ))
    (hx : x ∉ Set.range ((↑) : ℤ → ℝ)) :
    (13 : ℝ) ≤ x := by
  have h8192 : (8192 : ℝ) ≤ (2 : ℝ) ^ x :=
    not_lt.mp fun hlt ↦ hx
      (integer_of_two_three_rpow_integer_of_two_rpow_lt_8192 h₂ h₃ hlt)
  apply (Real.strictMono_rpow_of_base_gt_one (by norm_num : (1 : ℝ) < 2)).le_iff_le.mp
  norm_num [Real.rpow_natCast]
  exact h8192

/-- Every nonintegral natural two-base candidate value is at least `8192`. -/
theorem le_of_twoBaseNonintegerCandidate_8192 {{m : ℕ}}
    (hm : TwoBaseNaturalCandidate m) (hnp : ¬ ∃ n : ℕ, m = 2 ^ n) :
    8192 ≤ m := by
  by_contra hlt
  have hlt' : m < 8192 := by omega
  obtain ⟨h₂, h₃⟩ := hm.integer_powers
  have hmR : (2 : ℝ) ^ twoBaseCandidateExponent m = (m : ℝ) :=
    two_rpow_twoBaseCandidateExponent hm.1
  have hltR : (2 : ℝ) ^ twoBaseCandidateExponent m < 8192 := by
    rw [hmR]
    exact_mod_cast hlt'
  obtain ⟨z, hz⟩ :=
    integer_of_two_three_rpow_integer_of_two_rpow_lt_8192 h₂ h₃ hltR
  have hznonneg : 0 ≤ z := by
    have h0 : (0 : ℝ) ≤ twoBaseCandidateExponent m :=
      IntegerExponent.nonneg_of_two_rpow_integer h₂
    exact_mod_cast hz.symm ▸ h0
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hznonneg
  refine absurd ⟨n, ?_⟩ hnp
  have hpow : (m : ℝ) = ((2 ^ n : ℕ) : ℝ) := by
    calc
      (m : ℝ) = (2 : ℝ) ^ twoBaseCandidateExponent m := hmR.symm
      _ = (2 : ℝ) ^ ((n : ℕ) : ℝ) := by rw [← hz]; norm_num
      _ = ((2 ^ n : ℕ) : ℝ) := by rw [Real.rpow_natCast]; norm_cast
  exact_mod_cast hpow

end LeanProofs.TwoBaseIntegerExponent
'''
out = "C:/ProveIt/Analysis/ExponentialIdentities/Lean/ExponentialIdentities/TwoBaseIntegerExponent/FiniteCheck8192.lean"
open(out, "w", encoding="utf-8", newline="\n").write(lean)
print("written", out, "tiers", nt, "thr", thr)
