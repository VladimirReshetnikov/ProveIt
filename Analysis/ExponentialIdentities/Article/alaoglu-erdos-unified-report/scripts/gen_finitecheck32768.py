"""Generate FiniteCheck32768.lean.

Design change from FiniteCheck16384: each row carries its own enclosure exponents
(a, Lp, Lq, Up, Uq) and the enclosure facts 2^Lp < 3^Lq, 3^Uq < 2^Up are checked inside the
same `decide` as the row comparisons.  That removes the tier `match`, the per-tier base
theorems, and the 36-fold disjunction spec of the earlier modules; the whole certificate is
one uniform Boolean predicate.
"""
import sys, json
from decimal import Decimal, getcontext
import gmpy2
from gmpy2 import mpz

getcontext().prec = 140
THETA = Decimal(3).ln() / Decimal(2).ln()

LO, HI, CHUNK, POW2 = 16384, 32768, 4096, 16384

def cf_terms(x, n):
    out = []
    for _ in range(n):
        a = int(x); out.append(a)
        f = x - a
        if f == 0: break
        x = 1 / f
    return out

terms = cf_terms(THETA, 45)
conv, pm1, qm1, pm2, qm2 = [], 1, 0, 0, 1
for a in terms:
    p, q = a * pm1 + pm2, a * qm1 + qm2
    conv.append((p, q)); pm2, qm2, pm1, qm1 = pm1, qm1, p, q

CAP = 20_000_000
def is_lower(p, q): return mpz(2) ** p < mpz(3) ** q

lowers, uppers = [], []
for i in range(1, len(conv)):
    p, q = conv[i]
    if p > CAP: break
    (lowers if is_lower(p, q) else uppers).append((p, q))
    if i + 1 < len(terms):
        pp, qq = conv[i - 1]
        for k in range(1, terms[i + 1]):
            sp, sq = pp + k * p, qq + k * q
            if sp > CAP: break
            (lowers if is_lower(sp, sq) else uppers).append((sp, sq))

def pareto(lst, lower):
    out, best = [], None
    for p, q in sorted(set(lst)):
        g = (THETA - Decimal(p) / Decimal(q)) if lower else (Decimal(p) / Decimal(q) - THETA)
        if g <= 0: continue
        if best is None or g < best:
            out.append((p, q)); best = g
    return out

L, U = pareto(lowers, True), pareto(uppers, False)

rows = []
for m in range(LO, HI):
    if m == POW2:
        rows.append((m, 0, 1, 1, 2, 1))       # exempt row; harmless valid enclosure data
        continue
    logm = Decimal(m).ln()
    a = int((THETA * logm).exp())
    lo_need = Decimal(a).ln() / logm
    hi_need = Decimal(a + 1).ln() / logm
    lo = next(e for e in L if Decimal(e[0]) / Decimal(e[1]) > lo_need)
    up = next(e for e in U if Decimal(e[0]) / Decimal(e[1]) < hi_need)
    rows.append((m, a, lo[0], lo[1], up[0], up[1]))

print(f"rows: {len(rows)}", flush=True)

# ------------------------------------------------------------------ exact verification
print("exact GMP verification of every row (including enclosure facts) ...", flush=True)
maxexp = 0
for n, (m, a, Lp, Lq, Up, Uq) in enumerate(rows):
    if m == POW2:
        assert mpz(2) ** Lp < mpz(3) ** Lq and mpz(3) ** Uq < mpz(2) ** Up
        continue
    if not (mpz(2) ** Lp < mpz(3) ** Lq): sys.exit(f"lower encl fails m={m}")
    if not (mpz(3) ** Uq < mpz(2) ** Up): sys.exit(f"upper encl fails m={m}")
    if not (mpz(a) ** Lq < mpz(m) ** Lp): sys.exit(f"lower cert fails m={m}")
    if not (mpz(m) ** Up < mpz(a + 1) ** Uq): sys.exit(f"upper cert fails m={m}")
    maxexp = max(maxexp, Lp, Up)
    if n % 4000 == 0: print(f"   {n}/{len(rows)}", flush=True)
print(f"ALL ROWS VERIFIED EXACTLY.  largest exponent {maxexp:,}", flush=True)

hardest = max((r for r in rows if r[0] != POW2), key=lambda r: r[2])
THRESH = maxexp + 100_000

# ------------------------------------------------------------------ enclosure index
ENC, ENCL = {}, []
for (_m, _a, Lp, Lq, Up, Uq) in rows:
    k = (Lp, Lq, Up, Uq)
    if k not in ENC:
        ENC[k] = len(ENCL); ENCL.append(k)
print(f"distinct enclosure quadruples: {len(ENCL)}", flush=True)

# ------------------------------------------------------------------ emit
o = []; w = o.append
w("import ExponentialIdentities.TwoBaseIntegerExponent.FiniteCheck16384")
w("")
w("namespace LeanProofs.TwoBaseIntegerExponent")
w("")
w("open Set")
w("")
w("/-!")
w("This file extends the exact finite verification from `16384` to `32768`: any real exponent")
w("with `2 ^ x` and `3 ^ x` both integral and `2 ^ x < 32768` is an integer, so a nonintegral")
w("solution must satisfy `x ≥ 15`.")
w("")
w("For each `m` with `16384 ≤ m < 32768` the table records `a = ⌊m ^ (log 3 / log 2)⌋` together")
w("with the four exponents of a pair of rational enclosures `Lp / Lq < log 3 / log 2 < Up / Uq`")
w("taken from the continued-fraction convergent and semiconvergent ladder.  The row is accepted")
w("when all four exact integer comparisons")
w("")
w("* `2 ^ Lp < 3 ^ Lq`   (the lower enclosure really is below `log 3 / log 2`),")
w("* `3 ^ Uq < 2 ^ Up`   (the upper enclosure really is above it),")
w("* `a ^ Lq < m ^ Lp`,")
w("* `m ^ Up < (a + 1) ^ Uq`")
w("")
w("hold, and these together trap `m ^ (log 3 / log 2)` strictly between `a` and `a + 1`, so it")
w("is not an integer and `3 ^ x` cannot be one either.")
w("")
w("Unlike `FiniteCheck4096`--`FiniteCheck16384`, the enclosure facts are checked inside the same")
w("`decide` as the row comparisons rather than being proved separately per tier.  Each row is")
w("therefore self-contained: there is no tier `match`, no per-tier base theorem, and no")
w("disjunctive tier spec.  The table is split into four chunks of `4096` rows, each replayed by")
w(f"its own `decide`, so no single kernel evaluation has to hold the whole run.  The hardest row")
w(f"is `m = {hardest[0]}`, needing the enclosure `{hardest[2]} / {hardest[3]}`.")
w("")
w("The table was produced with high-precision decimal arithmetic and every row, enclosure facts")
w("included, was re-verified with exact GMP big-integer arithmetic before being replayed by the")
w("kernel through `decide`.  No `native_decide` is used.")
w("-/")
w("")

w("/-- The enclosure quadruples `(Lp, Lq, Up, Uq)` used by the table.  Row `j` of a chunk")
w("names one of these by index; nothing about the list matters to the proof beyond the four")
w("inequalities checked per row. -/")
w("private def encl32768 : List (ℕ × ℕ × ℕ × ℕ) := [")
_line = "    "
for _k, _e in enumerate(ENCL):
    _piece = f"({_e[0]}, {_e[1]}, {_e[2]}, {_e[3]})" + ("," if _k < len(ENCL) - 1 else "")
    if len(_line) + len(_piece) + 1 > 100:
        w(_line.rstrip()); _line = "    "
    _line += _piece + " "
w(_line.rstrip()); w("]"); w("")

for c in range(4):
    chunk = rows[c * CHUNK:(c + 1) * CHUNK]
    w("set_option maxRecDepth 400000 in")
    w(f"/-- Certificates for `{LO + c*CHUNK} ≤ m < {LO + (c+1)*CHUNK}`: entry `j` is")
    w(f"`(a, e)` for `m = {LO + c*CHUNK} + j`, where `e` indexes `encl32768`. -/")
    w(f"private def certTable32768_{c} : List (ℕ × ℕ) := [")
    items = [f"({a}, {ENC[(Lp, Lq, Up, Uq)]})" for (_m, a, Lp, Lq, Up, Uq) in chunk]
    line = "    "
    for k, it in enumerate(items):
        piece = it + ("," if k < len(items) - 1 else "")
        if len(line) + len(piece) + 1 > 100:
            w(line.rstrip()); line = "    "
        line += piece + " "
    w(line.rstrip()); w("]"); w("")

w("/-- All checks for one row.  Index `i` corresponds to `m = 16384 + i`; the power of two")
w("`16384` at index `0` is exempt. -/")
w("private def certOne32768 (i a e : ℕ) : Bool :=")
w("  (i == 0) ||")
w("    (let q := encl32768.getD e (0, 0, 0, 0)")
w("     decide (0 < a) && decide (0 < q.2.1) && decide (0 < q.2.2.2) &&")
w("      decide (2 ^ q.1 < 3 ^ q.2.1) && decide (3 ^ q.2.2.2 < 2 ^ q.2.2.1) &&")
w("      decide (a ^ q.2.1 < (16384 + i) ^ q.1) &&")
w("      decide ((16384 + i) ^ q.2.2.1 < (a + 1) ^ q.2.2.2))")
w("")
w("/-- Sequential check of all rows starting at index `i`. -/")
w("private def checkFrom32768 : ℕ → List (ℕ × ℕ) → Bool")
w("  | _, [] => true")
w("  | i, (a, e) :: rest =>")
w("    certOne32768 i a e && checkFrom32768 (i + 1) rest")
w("")
for c in range(4):
    w("set_option maxRecDepth 400000 in")
    w("set_option maxHeartbeats 1000000000 in")
    w(f"set_option exponentiation.threshold {THRESH} in")
    w(f"private theorem certTable32768_{c}_all :")
    w(f"    checkFrom32768 {c * CHUNK} certTable32768_{c} = true := by decide")
    w("")
for c in range(4):
    w("set_option maxRecDepth 400000 in")
    w(f"private theorem certTable32768_{c}_length :")
    w(f"    certTable32768_{c}.length = {CHUNK} := by decide")
    w("")

w("""private theorem checkFrom32768_spec {rows : List (ℕ × ℕ)} {i0 : ℕ}
    (h : checkFrom32768 i0 rows = true) :
    ∀ j, j < rows.length →
      certOne32768 (i0 + j) (rows.getD j (0, 0)).1 (rows.getD j (0, 0)).2 = true := by
  induction rows generalizing i0 with
  | nil =>
    intro j hj
    simp at hj
  | cons head tail ih =>
    intro j hj
    obtain ⟨a, e⟩ := head
    simp only [checkFrom32768, Bool.and_eq_true] at h
    cases j with
    | zero => simpa using h.1
    | succ j' =>
      have htail := ih h.2 j' (Nat.lt_of_succ_lt_succ (by simpa using hj))
      have harith : i0 + (j' + 1) = i0 + 1 + j' := by omega
      simpa [List.getD_cons_succ, harith] using htail

private theorem certOne32768_spec {i a e : ℕ} (h : certOne32768 i a e = true) :
    i = 0 ∨ (∃ Lp Lq Up Uq : ℕ,
      0 < a ∧ 0 < Lq ∧ 0 < Uq ∧ 2 ^ Lp < 3 ^ Lq ∧ 3 ^ Uq < 2 ^ Up ∧
      a ^ Lq < (16384 + i) ^ Lp ∧ (16384 + i) ^ Up < (a + 1) ^ Uq) := by
  simp only [certOne32768, Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true,
    decide_eq_true_eq] at h
  rcases h with h | h
  · exact Or.inl h
  · exact Or.inr ⟨_, _, _, _, h.1.1.1.1.1.1, h.1.1.1.1.1.2, h.1.1.1.1.2,
      h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

/-! ### From certificates to the analytic contradiction -/

private theorem mul_log_lt_mul_log_of_pow_lt32768
    {a b p q : ℕ} (ha : 0 < a) (hb : 0 < b) (hpow : a ^ p < b ^ q) :
    (p : ℝ) * Real.log (a : ℝ) < (q : ℝ) * Real.log (b : ℝ) := by
  have hpowR : (a : ℝ) ^ p < (b : ℝ) ^ q := by exact_mod_cast hpow
  have hlog := Real.strictMonoOn_log
    (by simpa only [Set.mem_Ioi] using (show 0 < (a : ℝ) ^ p by positivity))
    (by simpa only [Set.mem_Ioi] using (show 0 < (b : ℝ) ^ q by positivity)) hpowR
  simpa only [Real.log_pow] using hlog

private theorem no_integer_between_consecutive_naturals32768
    {y : ℝ} {a : ℕ}
    (hy : y ∈ Set.range ((↑) : ℤ → ℝ))
    (hlow : (a : ℝ) < y) (hupp : y < (a + 1 : ℕ)) : False := by
  obtain ⟨z, rfl⟩ := hy
  have hzlow : (a : ℤ) < z := by exact_mod_cast hlow
  have hzupp : z < (a : ℤ) + 1 := by exact_mod_cast hupp
  omega

private theorem cert_contradiction32768
    {x : ℝ} {m a lowerNum lowerDen upperNum upperDen : ℕ}
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
    mul_log_lt_mul_log_of_pow_lt32768 (by norm_num) (by norm_num) hlowerBase
  have hcommonUpper :
      (upperDen : ℝ) * Real.log 3 < upperNum * Real.log 2 :=
    mul_log_lt_mul_log_of_pow_lt32768 (by norm_num) (by norm_num) hupperBase
  have hmLowerLog :
      (lowerDen : ℝ) * Real.log a < lowerNum * Real.log m :=
    mul_log_lt_mul_log_of_pow_lt32768 ha hmpos hmLower
  have hmUpperLog :
      (upperNum : ℝ) * Real.log m < upperDen * Real.log ((a + 1 : ℕ) : ℝ) :=
    mul_log_lt_mul_log_of_pow_lt32768 hmpos (by omega) hmUpper
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
  exact no_integer_between_consecutive_naturals32768 h₃ hLower hUpper

private theorem integer_of_two_rpow_eq_pow_two32768 {x : ℝ} {m k : ℕ}
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
""")

# ---- main theorem with four-chunk dispatch
w("/-- If both powers are integral and `2 ^ x < 32768`, then `x` is an integer. -/")
w("theorem integer_of_two_three_rpow_integer_of_two_rpow_lt_32768 {x : ℝ}")
w("    (h₂ : (2 : ℝ) ^ x ∈ Set.range ((↑) : ℤ → ℝ))")
w("    (h₃ : (3 : ℝ) ^ x ∈ Set.range ((↑) : ℤ → ℝ))")
w("    (hlt : (2 : ℝ) ^ x < 32768) :")
w("    x ∈ Set.range ((↑) : ℤ → ℝ) := by")
w("  by_cases hsmall : (2 : ℝ) ^ x < 16384")
w("  · exact integer_of_two_three_rpow_integer_of_two_rpow_lt_16384 h₂ h₃ hsmall")
w("  obtain ⟨z, hz⟩ := h₂")
w("  have hp : 0 < (2 : ℝ) ^ x := Real.rpow_pos_of_pos (by norm_num) _")
w("  have hzpos : 0 < z := by exact_mod_cast (hz.symm ▸ hp)")
w("  have hzloR : (16384 : ℝ) ≤ (z : ℝ) := by")
w("    calc")
w("      (16384 : ℝ) ≤ 2 ^ x := not_lt.mp hsmall")
w("      _ = (z : ℝ) := hz.symm")
w("  have hzlo : 16384 ≤ z := by exact_mod_cast hzloR")
w("  have hzhi : z < 32768 := by exact_mod_cast (hz.symm ▸ hlt)")
w("  have hxnonneg : 0 ≤ x := IntegerExponent.nonneg_of_two_rpow_integer ⟨z, hz⟩")
w("  lift z to ℕ using hzpos.le with m hmcast")
w("  have hmlo : 16384 ≤ m := by exact_mod_cast hzlo")
w("  have hmhi : m < 32768 := by exact_mod_cast hzhi")
w("  have hpowm : (2 : ℝ) ^ x = (m : ℝ) := hz.symm")
w("  have hmpos : 0 < m := by omega")
for c in range(4):
    off = c * CHUNK
    lo_m, hi_m = LO + off, LO + off + CHUNK
    cond = f"m < {hi_m}"
    if c == 0:
        w(f"  by_cases hc{c} : {cond}")
    else:
        w(f"  by_cases hc{c} : {cond}")
    w(f"  · have hidx : m - {lo_m} < certTable32768_{c}.length := by")
    w(f"      rw [certTable32768_{c}_length]")
    w("      omega")
    w(f"    have hcert := checkFrom32768_spec certTable32768_{c}_all (m - {lo_m}) hidx")
    w(f"    rcases certOne32768_spec hcert with h0 |")
    w(f"      ⟨_Lp, _Lq, _Up, _Uq, hapos, hLqpos, hUqpos, hlb, hub, hlo, hhi⟩")
    if c == 0:
        w("    · exact integer_of_two_rpow_eq_pow_two32768")
        w("        (show m = 2 ^ 14 by norm_num; omega) hpowm")
    else:
        w("    · exfalso")
        w("      omega")
    w("    · exfalso")
    w(f"      rw [show {LO} + ({off} + (m - {lo_m})) = m from by omega] at hlo hhi")
    w("      exact cert_contradiction32768 hpowm h₃ hapos hmpos hxnonneg")
    w("        hLqpos hUqpos hlb hub hlo hhi")
w("  · exfalso")
w("    omega")
w("")

w("/-- In exponent coordinates, every nonintegral two-base solution is at least `15`. -/")
w("theorem fifteen_le_of_not_integer_of_two_three_rpow_integer {x : ℝ}")
w("    (h₂ : (2 : ℝ) ^ x ∈ Set.range ((↑) : ℤ → ℝ))")
w("    (h₃ : (3 : ℝ) ^ x ∈ Set.range ((↑) : ℤ → ℝ))")
w("    (hx : x ∉ Set.range ((↑) : ℤ → ℝ)) :")
w("    (15 : ℝ) ≤ x := by")
w("  have h32768 : (32768 : ℝ) ≤ (2 : ℝ) ^ x :=")
w("    not_lt.mp fun hlt ↦ hx")
w("      (integer_of_two_three_rpow_integer_of_two_rpow_lt_32768 h₂ h₃ hlt)")
w("  apply (Real.strictMono_rpow_of_base_gt_one (by norm_num : (1 : ℝ) < 2)).le_iff_le.mp")
w("  norm_num [Real.rpow_natCast]")
w("  exact h32768")
w("")
w("/-- Every nonintegral natural two-base candidate value is at least `32768`. -/")
w("theorem le_of_twoBaseNonintegerCandidate_32768 {m : ℕ}")
w("    (hm : TwoBaseNaturalCandidate m) (hnp : ¬ ∃ n : ℕ, m = 2 ^ n) :")
w("    32768 ≤ m := by")
w("  by_contra hlt")
w("  have hlt' : m < 32768 := by omega")
w("  obtain ⟨h₂, h₃⟩ := hm.integer_powers")
w("  have hmR : (2 : ℝ) ^ twoBaseCandidateExponent m = (m : ℝ) :=")
w("    two_rpow_twoBaseCandidateExponent hm.1")
w("  have hltR : (2 : ℝ) ^ twoBaseCandidateExponent m < 32768 := by")
w("    rw [hmR]")
w("    exact_mod_cast hlt'")
w("  obtain ⟨z, hz⟩ :=")
w("    integer_of_two_three_rpow_integer_of_two_rpow_lt_32768 h₂ h₃ hltR")
w("  have hznonneg : 0 ≤ z := by")
w("    have h0 : (0 : ℝ) ≤ twoBaseCandidateExponent m :=")
w("      IntegerExponent.nonneg_of_two_rpow_integer h₂")
w("    exact_mod_cast hz.symm ▸ h0")
w("  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hznonneg")
w("  refine absurd ⟨n, ?_⟩ hnp")
w("  have hpow : (m : ℝ) = ((2 ^ n : ℕ) : ℝ) := by")
w("    calc")
w("      (m : ℝ) = (2 : ℝ) ^ twoBaseCandidateExponent m := hmR.symm")
w("      _ = (2 : ℝ) ^ ((n : ℕ) : ℝ) := by rw [← hz]; norm_num")
w("      _ = ((2 ^ n : ℕ) : ℝ) := by rw [Real.rpow_natCast]; norm_cast")
w("  exact_mod_cast hpow")
w("")
w("end LeanProofs.TwoBaseIntegerExponent")

path = sys.argv[1] if len(sys.argv) > 1 else "FiniteCheck32768.lean"
with open(path, "w", encoding="utf-8", newline="\n") as f:
    f.write("\n".join(o) + "\n")
print(f"wrote {path}: {len(o)} lines, threshold {THRESH:,}")
