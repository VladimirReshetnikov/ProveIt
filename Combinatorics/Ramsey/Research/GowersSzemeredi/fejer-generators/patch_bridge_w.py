"""Bridge + audit additions for the polynomial base budget (Notes L.16m)."""
from pathlib import Path

GS = Path(r'C:\ProveIt\.claude\worktrees\q-fabius-deformations-merge-9bc27b\Combinatorics\Ramsey\Lean\GowersSzemeredi')
p = GS / 'Proofs18CoverFejerAllDegrees.lean'
s = p.read_text(encoding='utf-8')
imp = 'import GowersSzemeredi.Proofs18CoverFejerHeadlineU\n'
assert imp in s and 'Proofs18CoverFejerHeadlineW' not in s
s = s.replace(imp, imp + 'import GowersSzemeredi.Proofs18CoverFejerHeadlineW\n', 1)

EXPL = '''    (fun k => ⌈multiaffinePartitionK (k + 1) (2 ^ (k + 1))⌉₊)
    (fun k => (k + 1) * multiaffinePartitionP (k + 1) (2 ^ (k + 1)))
    (fun k => two_le_ceil_multiaffinePartitionK (k + 1) (2 ^ (k + 1)))
    (fun k => Nat.mul_pos (Nat.succ_pos k) (multiaffinePartitionP_pos _ _))
    (fun k _ => section16RecurrenceProfileWith_explicit k)
    (fun k => explicit_family_constants_poly_le k)'''

ADD = '''
/-! ### The polynomial base budget: `d + 3`, `L + 1` (Notes L.16m) -/

/-- **The explicit family constants are at most `2^(2^(4k+16))`**, a double
logarithm linear in `k` (the tower `2^(2^(2^(k+5)))` of
`explicit_family_constants_le` is the same estimate, weakened). -/
theorem explicit_family_constants_poly_le (k : Nat) :
    ((⌈multiaffinePartitionK (k + 1) (2 ^ (k + 1))⌉₊ : Nat) : Real) +
        (((k + 1) * multiaffinePartitionP (k + 1) (2 ^ (k + 1)) : Nat) : Real) ≤
      2 ^ ((2 : Nat) ^ (4 * k + 16)) := by
  have hU : uniformSchmidtK (k + 1) ≤ 2 ^ (schmidtKExp k + k + 2) := by
    have h := uniformSchmidtK_le_of (k := k + 1) (B := 2 ^ schmidtKExp k) fun j =>
      (schmidtMonomialK_le_gen j).trans
        (pow_le_pow_right₀ (by norm_num) (schmidtKExp_mono (by have := j.isLt; omega)))
    push_cast at h
    exact h.trans (uniform_base_le k (schmidtKExp k)).1
  have hMK := multiaffinePartitionK_le_of hU (uniform_base_le k (schmidtKExp k)).2 (2 ^ (k + 1))
  have hPu : uniformSchmidtP (k + 1) ≤ 1 + (k + 1) * schmidtPBnd k :=
    uniformSchmidtP_le_of fun j =>
      (schmidtMonomialP_le_gen j).trans (schmidtPBnd_mono (by have := j.isLt; omega))
  exact family_constants_poly_le k hMK hPu (multiaffinePartitionP_le_pow (k + 1) (2 ^ (k + 1)))

/-- **Theorem 18.1 at every degree `d ≥ 11` with `d + 3` in place of `d + 10`.** -/
theorem theorem_18_1_d3_eleven_le {d : Nat} (hd : 11 ≤ d) : Theorem181AtSharp 3 d := by
  obtain ⟨K, p, hpp, hp, hK, hpB⟩ := progressionPhasePartition_explicit
  exact theorem_18_1_d3_eleven_le_of_profiles_poly
EXPL hpp hp hK hpB hd

/-- **Theorem 18.1 at every degree `d ≥ 8` with `d + 4` in place of `d + 10`.** -/
theorem theorem_18_1_d4_eight_le {d : Nat} (hd : 8 ≤ d) : Theorem181AtSharp 4 d := by
  obtain ⟨K, p, hpp, hp, hK, hpB⟩ := progressionPhasePartition_explicit
  exact theorem_18_1_d4_eight_le_of_profiles_poly
EXPL hpp hp hK hpB hd

/-- **Theorem 18.2 at every length `L ≥ 13` with `L + 1` in place of `L + 9`.** -/
theorem theorem_18_2_L1_thirteen_le {L : Nat} (hL : 13 ≤ L) : Theorem182AtSharp 1 L :=
  theorem_18_2_L1_thirteen_le_of_profiles_poly
EXPL hL

/-- **Corollary 18.7 at every length `L ≥ 13` with `L + 1`.** -/
theorem corollary_18_7_L1_thirteen_le {L : Nat} (hL : 13 ≤ L) : Corollary187AtSharp 1 L :=
  (theorem_18_2_L1_thirteen_le hL).corollary_18_7

/-- **Theorem 18.2 at every length `L ≥ 10` with `L + 2` in place of `L + 9`.** -/
theorem theorem_18_2_L2_ten_le {L : Nat} (hL : 10 ≤ L) : Theorem182AtSharp 2 L :=
  theorem_18_2_L2_ten_le_of_profiles_poly
EXPL hL

/-- **Corollary 18.7 at every length `L ≥ 10` with `L + 2`.** -/
theorem corollary_18_7_L2_ten_le {L : Nat} (hL : 10 ≤ L) : Corollary187AtSharp 2 L :=
  (theorem_18_2_L2_ten_le hL).corollary_18_7

/-- **Van der Waerden numbers for long progressions**: for `k ≥ 13` and
`r ≥ 2`, `W(k, r) ≤ 2^2^r^2^2^(k+1)`. -/
theorem van_der_waerden_L1 {k : Nat} (hk : 13 ≤ k) {r : Nat} (hr : 2 ≤ r) (N : Nat)
    (hN : szemerediThresholdAt 1 (1 / (r : Real)) k ≤ N) (color : Nat → Fin r) :
    HasMonochromaticAP N r color k :=
  (theorem_18_2_L1_thirteen_le hk).van_der_waerden hr N hN color

/-- **Van der Waerden numbers**: for `k ≥ 10` and `r ≥ 2`,
`W(k, r) ≤ 2^2^r^2^2^(k+2)`. -/
theorem van_der_waerden_L2_ten_le {k : Nat} (hk : 10 ≤ k) {r : Nat} (hr : 2 ≤ r) (N : Nat)
    (hN : szemerediThresholdAt 2 (1 / (r : Real)) k ≤ N) (color : Nat → Fin r) :
    HasMonochromaticAP N r color k :=
  (theorem_18_2_L2_ten_le hk).van_der_waerden hr N hN color

/-- **Theorem 1.3 with constant `2^(-2^(k+1))` for every `k ≥ 13`** (printed:
`2^(-2^(k+9))`). -/
theorem theorem_1_3_L1_thirteen_le : Theorem13AtFrom 1 13 :=
  theorem13AtFrom_of_sharp fun _ hk => theorem_18_2_L1_thirteen_le hk

/-- **Theorem 1.3 with constant `2^(-2^(k+2))` for every `k ≥ 10`.** -/
theorem theorem_1_3_L2_ten_le : Theorem13AtFrom 2 10 :=
  theorem13AtFrom_of_sharp fun _ hk => theorem_18_2_L2_ten_le hk

'''.replace('EXPL', EXPL)
s = s.replace('\nend LeanProofs.GowersSzemeredi', ADD + 'end LeanProofs.GowersSzemeredi')
d1 = """* the polynomial Bohr radius (Notes L.16l): **`L + 2` for every `L ≥ 13`**
  (`theorem_18_2_L2_thirteen_le`), with van der Waerden and Theorem 1.3 at
  `k + 2` from `k = 13`. -/"""
assert d1 in s
s = s.replace(d1, d1[:-4] + """;
* the polynomial base budget (Notes L.16m): **`d + 3` for every `d ≥ 11`**
  (`theorem_18_1_d3_eleven_le`), `d + 4` for `d ≥ 8`, **`L + 1` for every
  `L ≥ 13`** (`theorem_18_2_L1_thirteen_le`), `L + 2` for `L ≥ 10`, with van
  der Waerden and Theorem 1.3 at `k + 1` from `k = 13` and at `k + 2` from
  `k = 10`. -/""", 1)
p.write_text(s, encoding='utf-8', newline='\n')

p = GS / 'CompletionAudit.lean'
s = p.read_text(encoding='utf-8')
a = '''example : LeanProofs.GowersSzemeredi.Theorem13AtFrom 2 13 :=
  LeanProofs.GowersSzemeredi.theorem_1_3_L2_thirteen_le
'''
assert s.count(a) == 1
s = s.replace(a, a + '''example : ∀ d, 11 ≤ d → LeanProofs.GowersSzemeredi.Theorem181AtSharp 3 d :=
  fun _ hd => LeanProofs.GowersSzemeredi.theorem_18_1_d3_eleven_le hd
example : ∀ d, 8 ≤ d → LeanProofs.GowersSzemeredi.Theorem181AtSharp 4 d :=
  fun _ hd => LeanProofs.GowersSzemeredi.theorem_18_1_d4_eight_le hd
example : ∀ L, 13 ≤ L → LeanProofs.GowersSzemeredi.Theorem182AtSharp 1 L :=
  fun _ hL => LeanProofs.GowersSzemeredi.theorem_18_2_L1_thirteen_le hL
example : ∀ L, 13 ≤ L → LeanProofs.GowersSzemeredi.Corollary187AtSharp 1 L :=
  fun _ hL => LeanProofs.GowersSzemeredi.corollary_18_7_L1_thirteen_le hL
example : ∀ L, 10 ≤ L → LeanProofs.GowersSzemeredi.Theorem182AtSharp 2 L :=
  fun _ hL => LeanProofs.GowersSzemeredi.theorem_18_2_L2_ten_le hL
example : ∀ L, 10 ≤ L → LeanProofs.GowersSzemeredi.Corollary187AtSharp 2 L :=
  fun _ hL => LeanProofs.GowersSzemeredi.corollary_18_7_L2_ten_le hL
example : LeanProofs.GowersSzemeredi.Theorem13AtFrom 1 13 :=
  LeanProofs.GowersSzemeredi.theorem_1_3_L1_thirteen_le
example : LeanProofs.GowersSzemeredi.Theorem13AtFrom 2 10 :=
  LeanProofs.GowersSzemeredi.theorem_1_3_L2_ten_le
''', 1)
b = '''    ``LeanProofs.GowersSzemeredi.theorem_1_3_L2_thirteen_le
  ]'''
assert s.count(b) == 1
s = s.replace(b, '''    ``LeanProofs.GowersSzemeredi.theorem_1_3_L2_thirteen_le,
    ``LeanProofs.GowersSzemeredi.explicit_family_constants_poly_le,
    ``LeanProofs.GowersSzemeredi.theorem_18_1_d3_eleven_le,
    ``LeanProofs.GowersSzemeredi.theorem_18_1_d4_eight_le,
    ``LeanProofs.GowersSzemeredi.theorem_18_2_L1_thirteen_le,
    ``LeanProofs.GowersSzemeredi.corollary_18_7_L1_thirteen_le,
    ``LeanProofs.GowersSzemeredi.theorem_18_2_L2_ten_le,
    ``LeanProofs.GowersSzemeredi.corollary_18_7_L2_ten_le,
    ``LeanProofs.GowersSzemeredi.van_der_waerden_L1,
    ``LeanProofs.GowersSzemeredi.van_der_waerden_L2_ten_le,
    ``LeanProofs.GowersSzemeredi.theorem_1_3_L1_thirteen_le,
    ``LeanProofs.GowersSzemeredi.theorem_1_3_L2_ten_le
  ]''', 1)
c = 'L+2 (L >= 13) with the van der Waerden bound and Theorem 1.3 at k+2 (k >= 13); only approved axioms."'
assert s.count(c) == 1
s = s.replace(c, 'L+2 (L >= 13) with the van der Waerden bound and Theorem 1.3 at k+2 (k >= 13), and from the polynomial base budget d+3 (d >= 11), d+4 (d >= 8), L+1 (L >= 13), L+2 (L >= 10) with the van der Waerden bound and Theorem 1.3 at k+1 (k >= 13) and k+2 (k >= 10); only approved axioms."', 1)
p.write_text(s, encoding='utf-8', newline='\n')
print('patched bridge and audit')
