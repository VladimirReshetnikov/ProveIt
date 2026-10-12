"""Bridge + audit additions for class constant 5/2 (Notes L.16n)."""
from pathlib import Path

GS = Path(r'C:\ProveIt\.claude\worktrees\q-fabius-deformations-merge-9bc27b\Combinatorics\Ramsey\Lean\GowersSzemeredi')
p = GS / 'Proofs18CoverFejerAllDegrees.lean'
s = p.read_text(encoding='utf-8')
imp = 'import GowersSzemeredi.Proofs18CoverFejerHeadlineW\n'
assert imp in s and 'Proofs18CoverFejerHeadlineX' not in s
s = s.replace(imp, imp + 'import GowersSzemeredi.Proofs18CoverFejerHeadlineX\n', 1)

EXPL = '''    (fun k => ⌈multiaffinePartitionK (k + 1) (2 ^ (k + 1))⌉₊)
    (fun k => (k + 1) * multiaffinePartitionP (k + 1) (2 ^ (k + 1)))
    (fun k => two_le_ceil_multiaffinePartitionK (k + 1) (2 ^ (k + 1)))
    (fun k => Nat.mul_pos (Nat.succ_pos k) (multiaffinePartitionP_pos _ _))
    (fun k _ => section16RecurrenceProfileWith_explicit k)
    (fun k => explicit_family_constants_poly_le k)'''

ADD = '''
/-! ### Class constant `5/2` and the polynomial Lemma 15.6: `d + 2`, `L + 0` (Notes L.16n) -/

/-- **Theorem 18.1 at every degree `d ≥ 17` with `d + 2` in place of `d + 10`.** -/
theorem theorem_18_1_d2_seventeen_le {d : Nat} (hd : 17 ≤ d) : Theorem181AtSharp 2 d := by
  obtain ⟨K, p, hpp, hp, hK, hpB⟩ := progressionPhasePartition_explicit
  exact theorem_18_1_d2_seventeen_le_of_profiles_poly
EXPL hpp hp hK hpB hd

/-- **Theorem 18.2 at every length `L ≥ 19` with no offset** (`L + 0` in place
of `L + 9`). -/
theorem theorem_18_2_L0_nineteen_le {L : Nat} (hL : 19 ≤ L) : Theorem182AtSharp 0 L :=
  theorem_18_2_L0_nineteen_le_of_profiles_poly
EXPL hL

/-- **Corollary 18.7 at every length `L ≥ 19` with no offset.** -/
theorem corollary_18_7_L0_nineteen_le {L : Nat} (hL : 19 ≤ L) : Corollary187AtSharp 0 L :=
  (theorem_18_2_L0_nineteen_le hL).corollary_18_7

/-- **Van der Waerden numbers for long progressions**: for `k ≥ 19` and
`r ≥ 2`, `W(k, r) ≤ 2^2^r^2^2^k`. -/
theorem van_der_waerden_L0 {k : Nat} (hk : 19 ≤ k) {r : Nat} (hr : 2 ≤ r) (N : Nat)
    (hN : szemerediThresholdAt 0 (1 / (r : Real)) k ≤ N) (color : Nat → Fin r) :
    HasMonochromaticAP N r color k :=
  (theorem_18_2_L0_nineteen_le hk).van_der_waerden hr N hN color

/-- **Theorem 1.3 with constant `2^(-2^k)` for every `k ≥ 19`** (printed:
`2^(-2^(k+9))`). -/
theorem theorem_1_3_L0_nineteen_le : Theorem13AtFrom 0 19 :=
  theorem13AtFrom_of_sharp fun _ hk => theorem_18_2_L0_nineteen_le hk

'''.replace('EXPL', EXPL)
s = s.replace('\nend LeanProofs.GowersSzemeredi', ADD + 'end LeanProofs.GowersSzemeredi')
d1 = """  der Waerden and Theorem 1.3 at `k + 1` from `k = 13` and at `k + 2` from
  `k = 10`. -/"""
assert d1 in s
s = s.replace(d1, d1[:-4] + """;
* class constant `5/2` beyond dimension `12` and the polynomial Lemma 15.6
  threshold (Notes L.16n): **`d + 2` for every `d ≥ 17`**
  (`theorem_18_1_d2_seventeen_le`) and **no offset at all, `L + 0`, for every
  `L ≥ 19`** (`theorem_18_2_L0_nineteen_le`), with `W(k, r) ≤ 2^2^r^2^2^k` and
  Theorem 1.3 at `2^(-2^k)` from `k = 19`. -/""", 1)
p.write_text(s, encoding='utf-8', newline='\n')

p = GS / 'CompletionAudit.lean'
s = p.read_text(encoding='utf-8')
a = '''example : LeanProofs.GowersSzemeredi.Theorem13AtFrom 2 10 :=
  LeanProofs.GowersSzemeredi.theorem_1_3_L2_ten_le
'''
assert s.count(a) == 1
s = s.replace(a, a + '''example : ∀ d, 17 ≤ d → LeanProofs.GowersSzemeredi.Theorem181AtSharp 2 d :=
  fun _ hd => LeanProofs.GowersSzemeredi.theorem_18_1_d2_seventeen_le hd
example : ∀ L, 19 ≤ L → LeanProofs.GowersSzemeredi.Theorem182AtSharp 0 L :=
  fun _ hL => LeanProofs.GowersSzemeredi.theorem_18_2_L0_nineteen_le hL
example : ∀ L, 19 ≤ L → LeanProofs.GowersSzemeredi.Corollary187AtSharp 0 L :=
  fun _ hL => LeanProofs.GowersSzemeredi.corollary_18_7_L0_nineteen_le hL
example : LeanProofs.GowersSzemeredi.Theorem13AtFrom 0 19 :=
  LeanProofs.GowersSzemeredi.theorem_1_3_L0_nineteen_le
''', 1)
b = '''    ``LeanProofs.GowersSzemeredi.theorem_1_3_L2_ten_le
  ]'''
assert s.count(b) == 1
s = s.replace(b, '''    ``LeanProofs.GowersSzemeredi.theorem_1_3_L2_ten_le,
    ``LeanProofs.GowersSzemeredi.theorem_18_1_d2_seventeen_le,
    ``LeanProofs.GowersSzemeredi.theorem_18_2_L0_nineteen_le,
    ``LeanProofs.GowersSzemeredi.corollary_18_7_L0_nineteen_le,
    ``LeanProofs.GowersSzemeredi.van_der_waerden_L0,
    ``LeanProofs.GowersSzemeredi.theorem_1_3_L0_nineteen_le
  ]''', 1)
c = 'k+1 (k >= 13) and k+2 (k >= 10); only approved axioms."'
assert s.count(c) == 1
s = s.replace(c, 'k+1 (k >= 13) and k+2 (k >= 10), and from class constant 5/2 d+2 (d >= 17) and L+0 (L >= 19) with the van der Waerden bound and Theorem 1.3 at k (k >= 19); only approved axioms."', 1)
p.write_text(s, encoding='utf-8', newline='\n')
print('patched bridge and audit')
