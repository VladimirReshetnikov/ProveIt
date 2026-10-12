"""Bridge, audit and docs: Theorem 18.1 at d+3 from d = 8 via two-track split classes (Notes L.16x)."""
import sys
from pathlib import Path

R = Path(r'C:\ProveIt\.claude\worktrees\q-fabius-deformations-merge-9bc27b\Combinatorics\Ramsey')
GS = R / 'Lean/GowersSzemeredi'
mode = sys.argv[1]

if mode == 'lean':
    p = GS / 'Proofs18CoverFejerAllDegrees.lean'
    s = p.read_text(encoding='utf-8')
    imp = 'import GowersSzemeredi.Proofs18CoverFejerHeadlineJM\n'
    assert imp in s and 'Proofs18CoverFejerHeadlineJT' not in s
    s = s.replace(imp, imp + 'import GowersSzemeredi.Proofs18CoverFejerHeadlineJT\n', 1)
    s = s.replace('\nend LeanProofs.GowersSzemeredi', '''
/-! ### Two-track split classes (Notes L.16x) -/

/-- **Theorem 18.1 at every degree `d ≥ 8` with `d + 3` in place of `d + 10`.** -/
theorem theorem_18_1_d3_eight_le {d : Nat} (hd : 8 ≤ d) : Theorem181AtSharp 3 d := by
  obtain ⟨K, p, hpp, hp, hK, hpB⟩ := progressionPhasePartition_explicit
  exact theorem_18_1_d3_eight_le_of_profiles_poly
    (fun k => ⌈multiaffinePartitionK (k + 1) (2 ^ (k + 1))⌉₊)
    (fun k => (k + 1) * multiaffinePartitionP (k + 1) (2 ^ (k + 1)))
    (fun k => two_le_ceil_multiaffinePartitionK (k + 1) (2 ^ (k + 1)))
    (fun k => Nat.mul_pos (Nat.succ_pos k) (multiaffinePartitionP_pos _ _))
    (fun k _ => section16RecurrenceProfileWith_explicit k)
    (fun k => explicit_family_constants_poly_le k) hpp hp hK hpB hd

end LeanProofs.GowersSzemeredi''')
    p.write_text(s, encoding='utf-8', newline='\n')
    p = GS / 'CompletionAudit.lean'
    s = p.read_text(encoding='utf-8')
    a = '  fun _ hd => LeanProofs.GowersSzemeredi.theorem_18_1_d2_eleven_le hd\n'
    assert s.count(a) == 1
    s = s.replace(a, a + '''example : ∀ d, 8 ≤ d → LeanProofs.GowersSzemeredi.Theorem181AtSharp 3 d :=
  fun _ hd => LeanProofs.GowersSzemeredi.theorem_18_1_d3_eight_le hd
''', 1)
    b = '    ``LeanProofs.GowersSzemeredi.theorem_18_1_d2_eleven_le\n  ]'
    assert s.count(b) == 1
    s = s.replace(b, '    ``LeanProofs.GowersSzemeredi.theorem_18_1_d2_eleven_le,\n'
                  '    ``LeanProofs.GowersSzemeredi.theorem_18_1_d3_eight_le\n  ]', 1)
    c = 'Theorem 18.1 at d+2 (d >= 11); only approved axioms."'
    assert s.count(c) == 1
    s = s.replace(c, 'Theorem 18.1 at d+2 (d >= 11), and with two-track split classes Theorem 18.1 at '
                  'd+3 (d >= 8); only approved axioms."', 1)
    p.write_text(s, encoding='utf-8', newline='\n')
    print('lean patched')
else:
    p = R / 'Research/GowersSzemeredi/SECTION16_RESEARCH_NOTES.md'
    s = p.read_text(encoding='utf-8')
    anchor = "(dimension-two count `(11, 2^41)`) would also give `d + 3` from 8.\n"
    assert s.count(anchor) == 1
    s = s.replace(anchor, anchor + '''
**L.16x: two-track split classes (2026-10-12).** The width exponent of a split
class was the reciprocal of its count (`splitExp = splitCnt⁻¹`), so dimension
two had to take `(32, 2^48)` for both, while its count is `(n+1)^11·W^(2^41)`
and its exponent `((n+1)^29·W^(2^46))⁻¹`. In the step, the next class's
count uses only the lower count: the remainder count `Qr`, the samples `S`
and the piece bound `Pb`. Its width exponent uses the lower count for the
divisor, the width scale and `S`, and the lower exponent only for the
spectrum exponent `Eb`, the remainder exponent `Er` and the slice exponent
`Es`. `SplitUniformClass2 k V ac Dc ae De` keeps the two tracks apart.
* `Proofs16SplitTwoTrack`: `split_exp_inv_le_fejer2`, the width exponent of the
  next class from a two-track class (family exponent
  `sExpN2 = 1 + (sBqN ac + (sErN ae + ae)) + ae·(sSN ac + 1)`, parameter
  degree `fsExpW2`), the corpus proof with `Eb`, `Er`, `Es` on the exponent
  track and an inline slice bound at `(ae, De)`.
* `Proofs16SplitTwoTrackClasses`: `SplitUniformClass2`, `.toSplit` (to a split
  class at `(max ac ae, max Dc De)`), `splitUniformClass2_succ_fejer` (count
  `(sCountN ac, max (fsCountW ac Dc) (fejerStepThrDeg Dc))`),
  `splitUniformClass2_two` (dimension two at `(11, 2^41)` and `(29, 2^46)`),
  `splitQuad` with `split_quad_le_max`, a `gcongr` comparison showing the
  quadruple stays below the `max` pairs from `(32, 2^48)`, so the invariant
  at class constant `5/2` carries over. Also `splitUniformClass2_all` and the
  exact table `tDegT2`: `…, 122, 188, 288, 452, 742, 1277, 2300, 4294, 8225,
  16029, 31572` (dimensions 4–14), 6–16% below `tDegM`.
* `Proofs18Cover{Modulus,Density,Exponents}FejerJT`, `Proofs18CoverFejerHeadlineJT`
  (`assemble_jt.py`): the joint-slice chain over `tDegT2`. Theorem 18.1 at
  `d + 3` from `d = 8` (`theorem_18_1_d3_eight_le`).
The model `models/model_two_track.py` reproduces `tDegM` in its one-track
case. With the two tracks it predicts exactly this table.
''', 1)
    p.write_text(s, encoding='utf-8', newline='\n')
    p = R / 'FORMALIZATION_STATUS.txt'
    s = p.read_text(encoding='utf-8')
    a = "  (d+2, d >= 11). Stub-checked and pinned.\n"
    assert s.count(a) == 1
    s = s.replace(a, a + """  Two-track split classes (notes L.16x, Proofs16SplitTwoTrack,
  Proofs16SplitTwoTrackClasses, Proofs18Cover*FejerJT, Proofs18CoverFejerHeadlineJT):
  theorem_18_1_d3_eight_le (d+3, d >= 8). Stub-checked and pinned.
""", 1)
    p.write_text(s, encoding='utf-8', newline='\n')
    p = R / 'Research/GowersSzemeredi/joint-vertex-covers/joint-vertex-covers.tex'
    s = p.read_text(encoding='utf-8')
    for x, y in [
        (r'Theorem 18.1, $\alpha^{2^{2^{d+c}}}$ & $10$ & $4$ & $3$ ($d\ge9$) & $2$ ($d\ge11$) & \\',
         r'Theorem 18.1, $\alpha^{2^{2^{d+c}}}$ & $10$ & $4$ & $3$ ($d\ge8$) & $2$ ($d\ge11$) & \\'),
        (r'''suffices, and the class degrees drop by 4--6\%. This gives $d+2$ from
$d=11$.''',
         r'''suffices, and the class degrees drop by 4--6\%. This gives $d+2$ from
$d=11$. Keeping the count and the width exponent of a class on separate
tracks lets dimension two start from its count $(n+1)^{11}W^{2^{41}}$ rather
than the common $(n+1)^{32}W^{2^{48}}$; the class degrees drop by a further
6--16\%, and $d+3$ holds from $d=8$.'''),
        (r'''split step by $\max$ & \lean{theorem\_18\_1\_d2\_eleven\_le} (\lean{Proofs18TightClassesFejerM}, \lean{…HeadlineJM})\\''',
         r'''split step by $\max$ & \lean{theorem\_18\_1\_d2\_eleven\_le} (\lean{Proofs18TightClassesFejerM}, \lean{…HeadlineJM})\\
two-track classes & \lean{theorem\_18\_1\_d3\_eight\_le} (\lean{Proofs16SplitTwoTrackClasses}, \lean{…HeadlineJT})\\'''),
    ]:
        assert s.count(x) == 1, x[:80]
        s = s.replace(x, y)
    p.write_text(s, encoding='utf-8', newline='\n')
    print('docs patched')
