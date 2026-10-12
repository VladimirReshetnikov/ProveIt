"""Bridge + audit: Theorem 18.2 with the sharp partition constant (Notes L.16s)."""
from pathlib import Path

GS = Path(r'C:\ProveIt\.claude\worktrees\q-fabius-deformations-merge-9bc27b\Combinatorics\Ramsey\Lean\GowersSzemeredi')
p = GS / 'Proofs18CoverFejerAllDegrees.lean'
s = p.read_text(encoding='utf-8')
imp = 'import GowersSzemeredi.Proofs18CoverFejerLowDegrees4\n'
assert imp in s and 'Proofs18CoverFejerHeadlineK' not in s
s = s.replace(imp, imp + 'import GowersSzemeredi.Proofs18CoverFejerHeadlineK\n', 1)
EXPL = '''    (fun k => ⌈multiaffinePartitionK (k + 1) (2 ^ (k + 1))⌉₊)
    (fun k => (k + 1) * multiaffinePartitionP (k + 1) (2 ^ (k + 1)))
    (fun k => two_le_ceil_multiaffinePartitionK (k + 1) (2 ^ (k + 1)))
    (fun k => Nat.mul_pos (Nat.succ_pos k) (multiaffinePartitionP_pos _ _))
    (fun k _ => section16RecurrenceProfileWith_explicit k)
    (fun k => explicit_family_constants_poly_le k)'''
ADD = '\n/-! ### The partition constant, sharply (Notes L.16s) -/\n\n'
NAMES = []
PIN = ''
for c, lo, word in ((0, 14, 'fourteen'), (1, 11, 'eleven'), (2, 8, 'eight')):
    ADD += f'''/-- **Theorem 18.2 at every length `L ≥ {lo}` with `L + {c}` in place of `L + 9`.** -/
theorem theorem_18_2_L{c}_{word}_le {{L : Nat}} (hL : {lo} ≤ L) : Theorem182AtSharp {c} L :=
  theorem_18_2_L{c}_{word}_le_of_profiles_poly
{EXPL} hL

/-- **Corollary 18.7 at every length `L ≥ {lo}` with `L + {c}`.** -/
theorem corollary_18_7_L{c}_{word}_le {{L : Nat}} (hL : {lo} ≤ L) : Corollary187AtSharp {c} L :=
  (theorem_18_2_L{c}_{word}_le hL).corollary_18_7

/-- **Van der Waerden numbers**: for `k ≥ {lo}` and `r ≥ 2`, the bound of
Theorem 1.3 with `k + {c}`. -/
theorem van_der_waerden_L{c}_{word}_le {{k : Nat}} (hk : {lo} ≤ k) {{r : Nat}} (hr : 2 ≤ r) (N : Nat)
    (hN : szemerediThresholdAt {c} (1 / (r : Real)) k ≤ N) (color : Nat → Fin r) :
    HasMonochromaticAP N r color k :=
  (theorem_18_2_L{c}_{word}_le hk).van_der_waerden hr N hN color

/-- **Theorem 1.3 with `k + {c}` for every `k ≥ {lo}`.** -/
theorem theorem_1_3_L{c}_{word}_le : Theorem13AtFrom {c} {lo} :=
  theorem13AtFrom_of_sharp fun _ hk => theorem_18_2_L{c}_{word}_le hk

'''
    PIN += f'''example : ∀ L, {lo} ≤ L → LeanProofs.GowersSzemeredi.Theorem182AtSharp {c} L :=
  fun _ hL => LeanProofs.GowersSzemeredi.theorem_18_2_L{c}_{word}_le hL
example : ∀ L, {lo} ≤ L → LeanProofs.GowersSzemeredi.Corollary187AtSharp {c} L :=
  fun _ hL => LeanProofs.GowersSzemeredi.corollary_18_7_L{c}_{word}_le hL
example : LeanProofs.GowersSzemeredi.Theorem13AtFrom {c} {lo} :=
  LeanProofs.GowersSzemeredi.theorem_1_3_L{c}_{word}_le
'''
    NAMES += [f'theorem_18_2_L{c}_{word}_le', f'corollary_18_7_L{c}_{word}_le',
              f'van_der_waerden_L{c}_{word}_le', f'theorem_1_3_L{c}_{word}_le']
s = s.replace('\nend LeanProofs.GowersSzemeredi', ADD + 'end LeanProofs.GowersSzemeredi')
p.write_text(s, encoding='utf-8', newline='\n')

p = GS / 'CompletionAudit.lean'
s = p.read_text(encoding='utf-8')
a = '''example : LeanProofs.GowersSzemeredi.Theorem13AtFrom 2 9 :=
  LeanProofs.GowersSzemeredi.theorem_1_3_L2_nine_le
'''
assert s.count(a) == 1
s = s.replace(a, a + PIN, 1)
b = '''    ``LeanProofs.GowersSzemeredi.theorem_1_3_L2_nine_le
  ]'''
assert s.count(b) == 1
s = s.replace(b, '    ``LeanProofs.GowersSzemeredi.theorem_1_3_L2_nine_le,\n'
              + ',\n'.join(f'    ``LeanProofs.GowersSzemeredi.{n}' for n in NAMES) + '\n  ]', 1)
c = 'k+1 (k >= 12), k+2 (k >= 9); only approved axioms."'
assert s.count(c) == 1
s = s.replace(c, 'k+1 (k >= 12), k+2 (k >= 9), and with the sharp partition constant L+0 (L >= 14), '
              'L+1 (L >= 11), L+2 (L >= 8) with the van der Waerden bound and Theorem 1.3 at k (k >= 14), '
              'k+1 (k >= 11), k+2 (k >= 8); only approved axioms."', 1)
p.write_text(s, encoding='utf-8', newline='\n')
print('patched')
