"""Bridge, audit and docs: Theorem 18.2 family at L+0 from L = 13 (Notes L.16y)."""
import sys
from pathlib import Path

R = Path(r'C:\ProveIt\.claude\worktrees\q-fabius-deformations-merge-9bc27b\Combinatorics\Ramsey')
GS = R / 'Lean/GowersSzemeredi'
mode = sys.argv[1]
EXPL = '''    (fun k => ⌈multiaffinePartitionK (k + 1) (2 ^ (k + 1))⌉₊)
    (fun k => (k + 1) * multiaffinePartitionP (k + 1) (2 ^ (k + 1)))
    (fun k => two_le_ceil_multiaffinePartitionK (k + 1) (2 ^ (k + 1)))
    (fun k => Nat.mul_pos (Nat.succ_pos k) (multiaffinePartitionP_pos _ _))
    (fun k _ => section16RecurrenceProfileWith_explicit k)
    (fun k => explicit_family_constants_poly_le k)'''

if mode == 'lean':
    p = GS / 'Proofs18CoverFejerAllDegrees.lean'
    s = p.read_text(encoding='utf-8')
    imp = 'import GowersSzemeredi.Proofs18CoverFejerHeadlineJT\n'
    assert imp in s and 'Proofs18CoverFejerHeadlineK3' not in s
    s = s.replace(imp, imp + 'import GowersSzemeredi.Proofs18CoverFejerHeadlineK3\n', 1)
    s = s.replace('\nend LeanProofs.GowersSzemeredi', f'''
/-! ### The tight dimension-two count (Notes L.16y) -/

/-- **Theorem 18.2 at every length `L ≥ 13` with no offset.** -/
theorem theorem_18_2_L0_thirteen_le {{L : Nat}} (hL : 13 ≤ L) : Theorem182AtSharp 0 L :=
  theorem_18_2_L0_thirteen_le_of_profiles_poly
{EXPL} hL

/-- **Corollary 18.7 at every length `L ≥ 13` with no offset.** -/
theorem corollary_18_7_L0_thirteen_le {{L : Nat}} (hL : 13 ≤ L) : Corollary187AtSharp 0 L :=
  (theorem_18_2_L0_thirteen_le hL).corollary_18_7

/-- **Van der Waerden numbers**: for `k ≥ 13` and `r ≥ 2`, `W(k, r) ≤ 2^2^r^2^2^k`. -/
theorem van_der_waerden_L0_thirteen_le {{k : Nat}} (hk : 13 ≤ k) {{r : Nat}} (hr : 2 ≤ r) (N : Nat)
    (hN : szemerediThresholdAt 0 (1 / (r : Real)) k ≤ N) (color : Nat → Fin r) :
    HasMonochromaticAP N r color k :=
  (theorem_18_2_L0_thirteen_le hk).van_der_waerden hr N hN color

/-- **Theorem 1.3 with constant `2^(-2^k)` for every `k ≥ 13`.** -/
theorem theorem_1_3_L0_thirteen_le : Theorem13AtFrom 0 13 :=
  theorem13AtFrom_of_sharp fun _ hk => theorem_18_2_L0_thirteen_le hk

end LeanProofs.GowersSzemeredi''')
    p.write_text(s, encoding='utf-8', newline='\n')
    p = GS / 'CompletionAudit.lean'
    s = p.read_text(encoding='utf-8')
    a = '  fun _ hd => LeanProofs.GowersSzemeredi.theorem_18_1_d3_eight_le hd\n'
    assert s.count(a) == 1
    s = s.replace(a, a + '''example : ∀ L, 13 ≤ L → LeanProofs.GowersSzemeredi.Theorem182AtSharp 0 L :=
  fun _ hL => LeanProofs.GowersSzemeredi.theorem_18_2_L0_thirteen_le hL
example : ∀ L, 13 ≤ L → LeanProofs.GowersSzemeredi.Corollary187AtSharp 0 L :=
  fun _ hL => LeanProofs.GowersSzemeredi.corollary_18_7_L0_thirteen_le hL
example : LeanProofs.GowersSzemeredi.Theorem13AtFrom 0 13 :=
  LeanProofs.GowersSzemeredi.theorem_1_3_L0_thirteen_le
''', 1)
    b = '    ``LeanProofs.GowersSzemeredi.theorem_18_1_d3_eight_le\n  ]'
    assert s.count(b) == 1
    s = s.replace(b, '    ``LeanProofs.GowersSzemeredi.theorem_18_1_d3_eight_le,\n'
                  '    ``LeanProofs.GowersSzemeredi.theorem_18_2_L0_thirteen_le,\n'
                  '    ``LeanProofs.GowersSzemeredi.corollary_18_7_L0_thirteen_le,\n'
                  '    ``LeanProofs.GowersSzemeredi.van_der_waerden_L0_thirteen_le,\n'
                  '    ``LeanProofs.GowersSzemeredi.theorem_1_3_L0_thirteen_le\n  ]', 1)
    c = 'Theorem 18.1 at d+3 (d >= 8); only approved axioms."'
    assert s.count(c) == 1
    s = s.replace(c, 'Theorem 18.1 at d+3 (d >= 8), and with the tight dimension-two count L+0 (L >= 13) '
                  'with the van der Waerden bound and Theorem 1.3 at k (k >= 13); only approved axioms."', 1)
    p.write_text(s, encoding='utf-8', newline='\n')
    print('lean patched')
else:
    p = R / 'Research/GowersSzemeredi/SECTION16_RESEARCH_NOTES.md'
    s = p.read_text(encoding='utf-8')
    anchor = "case. With the two tracks it predicts exactly this table.\n"
    assert s.count(anchor) == 1
    s = s.replace(anchor, anchor + '''
**L.16y: the dimension-two count, unrounded (2026-10-12).** After L.16x the
Theorem 18.1 thresholds no longer move under per-step savings or under the
exponent seed. The count seed now moves Theorem 18.2: `(11, 2^39)` gives
`L + 0` from 13 (`model_two_track.py`). The count's parameter degree is
about six times that of the face count `q_f`
(`uniTwoFejerCount_le_split`: `2^24 + 2·SB + 2·PB`). The corpus bounds `q_f`
by `u^(2^38)`, rounding twice: Lemma 16.3's exponent `10002` up to `2^14`
(`section16BaseFamilyBound_le_dyadic_power`), and then
`(2^23+1)·2^14 ≤ 2^38`. Unrounded, `q_f ≤ u^(10002·(2^23+1)) ≈ u^(2^36.29)`
(`polyPieceFaceCountW_fejer_le_tight`), and the count is at most
`(n+1)^11·W^(2^39)` (`uniTwoFejerCount_le_split_tight`; degree about
`2^38.87`). No sharpening of Lemma 16.3 is needed. Modules:
`Proofs16UniformCoverTwoTight` (`assemble_tight.py`, including the seed
`splitUniformClass2_two_tight`); `Proofs16SplitTwoTrackClassesT3`
(`assemble_t3.py`), the table `tDegT3`
`…, 120, 186, 286, 450, 740, 1275, 2298, 4292, 8223, 16027, 31570`; the joint-slice
chain `Proofs18Cover{Modulus,Density,Exponents}FejerJT3`; and
`Proofs18CoverFejerHeadlineK3` (`assemble_k3.py`), the K envelope over
`tDegT3`. In the bridge: Theorem 18.2 and Corollary 18.7 at `L + 0` from
`L = 13`, `W(k, r) ≤ 2^2^r^2^2^k` and Theorem 1.3 with density exponent
`2^(-2^k)` for `k ≥ 13`. Theorem 18.1 does not move.
''', 1)
    p.write_text(s, encoding='utf-8', newline='\n')
    p = R / 'FORMALIZATION_STATUS.txt'
    s = p.read_text(encoding='utf-8')
    a = "  theorem_18_1_d3_eight_le (d+3, d >= 8). Stub-checked and pinned.\n"
    assert s.count(a) == 1
    s = s.replace(a, a + """  Tight dimension-two count (notes L.16y, Proofs16UniformCoverTwoTight,
  Proofs16SplitTwoTrackClassesT3, Proofs18Cover*FejerJT3, Proofs18CoverFejerHeadlineK3):
  theorem_18_2_L0_thirteen_le (L+0, L >= 13), corollary_18_7_L0_thirteen_le,
  van_der_waerden_L0_thirteen_le, theorem_1_3_L0_thirteen_le. Stub-checked and pinned.
""", 1)
    p.write_text(s, encoding='utf-8', newline='\n')
    p = R / 'Research/GowersSzemeredi/joint-vertex-covers/joint-vertex-covers.tex'
    s = p.read_text(encoding='utf-8')
    for x, y in [
        (r'Theorem 18.2, $L+c$ & $9$ & $3$ & $2$ ($L\ge8$) & $1$ ($L\ge11$) & $0$ ($L\ge14$)\\',
         r'Theorem 18.2, $L+c$ & $9$ & $3$ & $2$ ($L\ge8$) & $1$ ($L\ge11$) & $0$ ($L\ge13$)\\'),
        (r'Corollary 18.7, $L+c$ & $9$ & $3$ & $2$ ($L\ge8$) & $1$ ($L\ge11$) & $0$ ($L\ge14$)\\',
         r'Corollary 18.7, $L+c$ & $9$ & $3$ & $2$ ($L\ge8$) & $1$ ($L\ge11$) & $0$ ($L\ge13$)\\'),
        (r'$W(k,r)\le2^{2^{r^{2^{2^{k+c}}}}}$ & $9$ & $3$ & $2$ ($k\ge8$) & $1$ ($k\ge11$) & $0$ ($k\ge14$)\\',
         r'$W(k,r)\le2^{2^{r^{2^{2^{k+c}}}}}$ & $9$ & $3$ & $2$ ($k\ge8$) & $1$ ($k\ge11$) & $0$ ($k\ge13$)\\'),
        (r'Theorem 1.3, $2^{-2^{k+c}}$ & $9$ & $3$ & $2$ ($k\ge8$) & $1$ ($k\ge11$) & $0$ ($k\ge14$)\\',
         r'Theorem 1.3, $2^{-2^{k+c}}$ & $9$ & $3$ & $2$ ($k\ge8$) & $1$ ($k\ge11$) & $0$ ($k\ge13$)\\'),
        (r'''than the common $(n+1)^{32}W^{2^{48}}$; the class degrees drop by a further
6--16\%, and $d+3$ holds from $d=8$.''',
         r'''than the common $(n+1)^{32}W^{2^{48}}$; the class degrees drop by a further
6--16\%, and $d+3$ holds from $d=8$. The dimension-two count itself is
$(n+1)^{11}W^{2^{39}}$ once Lemma~16.3's exponent $10002$ is kept instead
of being rounded to $2^{14}$, and with it Theorem~18.2, Corollary~18.7,
the van der Waerden bound and Theorem~1.3 hold with $L+0$ from $13$.'''),
        (r'''two-track classes & \lean{theorem\_18\_1\_d3\_eight\_le} (\lean{Proofs16SplitTwoTrackClasses}, \lean{…HeadlineJT})\\''',
         r'''two-track classes & \lean{theorem\_18\_1\_d3\_eight\_le} (\lean{Proofs16SplitTwoTrackClasses}, \lean{…HeadlineJT})\\
tight dimension two & \lean{theorem\_18\_2\_L0\_thirteen\_le}, \lean{theorem\_1\_3\_L0\_thirteen\_le} (\lean{…HeadlineK3})\\'''),
    ]:
        assert s.count(x) == 1, x[:80]
        s = s.replace(x, y)
    p.write_text(s, encoding='utf-8', newline='\n')
    print('docs patched')
