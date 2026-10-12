"""Bridge, audit and docs: Theorem 18.1 at d+2 from d = 11 via the max split step (Notes L.16w)."""
import sys
from pathlib import Path

R = Path(r'C:\ProveIt\.claude\worktrees\q-fabius-deformations-merge-9bc27b\Combinatorics\Ramsey')
GS = R / 'Lean/GowersSzemeredi'
mode = sys.argv[1]

if mode == 'lean':
    p = GS / 'Proofs18CoverFejerAllDegrees.lean'
    s = p.read_text(encoding='utf-8')
    imp = 'import GowersSzemeredi.Proofs16PolynomialFejerJ\n'
    assert imp in s and 'Proofs18CoverFejerHeadlineJM' not in s
    s = s.replace(imp, imp + 'import GowersSzemeredi.Proofs18CoverFejerHeadlineJM\n', 1)
    s = s.replace('\nend LeanProofs.GowersSzemeredi', '''
/-! ### The split step combined by `max` (Notes L.16w) -/

/-- **Theorem 18.1 at every degree `d ≥ 11` with `d + 2` in place of `d + 10`.** -/
theorem theorem_18_1_d2_eleven_le {d : Nat} (hd : 11 ≤ d) : Theorem181AtSharp 2 d := by
  obtain ⟨K, p, hpp, hp, hK, hpB⟩ := progressionPhasePartition_explicit
  exact theorem_18_1_d2_eleven_le_of_profiles_poly
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
    a = '  fun _ hk => LeanProofs.GowersSzemeredi.corollary_16_11_polynomial_fejerJ hk\n'
    assert s.count(a) == 1
    s = s.replace(a, a + '''example : ∀ d, 11 ≤ d → LeanProofs.GowersSzemeredi.Theorem181AtSharp 2 d :=
  fun _ hd => LeanProofs.GowersSzemeredi.theorem_18_1_d2_eleven_le hd
''', 1)
    b = '    ``LeanProofs.GowersSzemeredi.corollary_16_11_polynomial_fejerJ\n  ]'
    assert s.count(b) == 1
    s = s.replace(b, '    ``LeanProofs.GowersSzemeredi.corollary_16_11_polynomial_fejerJ,\n'
                  '    ``LeanProofs.GowersSzemeredi.theorem_18_1_d2_eleven_le\n  ]', 1)
    c = '(exponent 2^(2 tDegZ k + 7k + 38)); only approved axioms."'
    assert s.count(c) == 1
    s = s.replace(c, '(exponent 2^(2 tDegZ k + 7k + 38)), and with the split step combined by max '
                  'Theorem 18.1 at d+2 (d >= 11); only approved axioms."', 1)
    p.write_text(s, encoding='utf-8', newline='\n')
    print('lean patched')
else:
    p = R / 'Research/GowersSzemeredi/SECTION16_RESEARCH_NOTES.md'
    s = p.read_text(encoding='utf-8')
    anchor = "* The base envelope `EnvBound 3 62` of Theorem 18.2. The thresholds do not\n  move even at base 0.\n"
    assert s.count(anchor) == 1
    s = s.replace(anchor, anchor + '''
**L.16w: the split step combined by `max` (2026-10-12).** A split class
carries one family exponent `a` and one parameter degree `D` for its count,
its width exponent and its threshold. The step bounds the three separately,
then combined them by a sum: `splitStepA = sCountN + sExpN` and
`splitStepDFejer = countW + expW + thrDeg`. Every control of a split class
is monotone in `(a, D)`, so the `max` suffices
(`splitUniformClass_succ_fejer_max`; the step lemma is unchanged except for
its monotonicity targets). Since `max ≤ sum` (`splitStepAMax_le_sum`,
`splitStepDMaxWith_le_sum`), the invariants at class constants `4` and `5/2`
carry over unchanged. Only the exact table moves: `tDegM` is
`…, 134, 205, 317, 505, 842, 1472, 2684, 5057, 9746, 19064, 37637`
(dimensions 4–14) against `…, 136, 210, 326, 524, 881, 1550, 2841, 5371,
10375, 20323, 40154` for the sum, about 4–6% lower
(`Proofs18TightClassesFejerM`, `assemble_m.py`). Over these classes the
joint-slice chain (`Proofs18Cover{Modulus,Density,Exponents}FejerJM`,
`Proofs18CoverFejerHeadlineJM`, `assemble_jm.py`) gives Theorem 18.1 at
`d + 2` from `d = 11` (`theorem_18_1_d2_eleven_le`). The other thresholds do
not move. A split invariant with separate count and exponent exponents
(dimension-two count `(11, 2^41)`) would also give `d + 3` from 8.
''', 1)
    p.write_text(s, encoding='utf-8', newline='\n')
    p = R / 'FORMALIZATION_STATUS.txt'
    s = p.read_text(encoding='utf-8')
    a = "  corollary_16_11_polynomial_fejerJ (exponent 2^(2 tDegZ k + 7k + 38)).\n  Stub-checked and pinned.\n"
    assert s.count(a) == 1
    s = s.replace(a, a + """  Split step combined by max (notes L.16w, Proofs18TightClassesFejerM,
  Proofs18Cover*FejerJM, Proofs18CoverFejerHeadlineJM): theorem_18_1_d2_eleven_le
  (d+2, d >= 11). Stub-checked and pinned.
""", 1)
    p.write_text(s, encoding='utf-8', newline='\n')
    p = R / 'Research/GowersSzemeredi/joint-vertex-covers/joint-vertex-covers.tex'
    s = p.read_text(encoding='utf-8')
    for x, y in [
        (r'Theorem 18.1, $\alpha^{2^{2^{d+c}}}$ & $10$ & $4$ & $3$ ($d\ge9$) & $2$ ($d\ge12$) & \\',
         r'Theorem 18.1, $\alpha^{2^{2^{d+c}}}$ & $10$ & $4$ & $3$ ($d\ge9$) & $2$ ($d\ge11$) & \\'),
        (r'''This lowers the three Theorem~18.2 thresholds to $L+2$ from
8, $L+1$ from $11$ and $L+0$ from $14$.''' if False else r'''$11$ and $L+0$ from $14$. This is the limit of the method:''',
         r'''$11$ and $L+0$ from $14$. Finally, the split step bounds the count, the
width exponent and the threshold of the next class separately and combined
them by a sum; since every control is monotone in $(a,D)$, the maximum
suffices, and the class degrees drop by 4--6\%. This gives $d+2$ from
$d=11$. This is the limit of the method:'''),
        (r'''& \lean{theorem\_18\_2\_L2\_eight\_le}, \lean{polyPartConst\_le\_sharp} (\lean{Proofs18CoverFejerHeadlineK})\\''',
         r'''& \lean{theorem\_18\_2\_L2\_eight\_le}, \lean{polyPartConst\_le\_sharp} (\lean{Proofs18CoverFejerHeadlineK})\\
split step by $\max$ & \lean{theorem\_18\_1\_d2\_eleven\_le}, \lean{Proofs18TightClassesFejerM},\\
& \lean{Proofs18CoverFejerHeadlineJM}\\'''),
    ]:
        assert s.count(x) == 1, x[:80]
        s = s.replace(x, y)
    p.write_text(s, encoding='utf-8', newline='\n')
    print('docs patched')
