# Independent review: nine-variable complete-radical majorant

Reviewed component: `nine_full_radical/`.
Review date: 2026-10-24. Reviewer: independent Pell-reduction agent.

## Conclusion

**No mathematical defect found in the new majorant, its use in the norm
finalizer, or the claimed exact degree.** The delivered construction has nine
strictly positive unknowns, degree **1,158,228**, and **726** live binary
arithmetic operations. Its solvability equivalence is valid relative to the
explicitly inherited source/Pell/refutation theorems. This review does not
replace those inherited semantic proofs with a formal object-language proof.

I read the new `PROOF.md`, `verify.py`, and construction code, compared the
relevant arguments with the included proofs from packages 59, 65, and 71,
inspected the literal serialized DAG and coefficient metadata, and performed
the small independent counts and degree checks below. I did not repeat the
large sparse-polynomial expansion; the component contains its recorded PASS
and code for reconstructing that expansion exactly.

## Unbounded mathematical checks

1. **Universal majorant and its domain.** The proof uses complete polynomial
   expansions after `(A,C,i,t)=(x+3,y+1,z+1,u+3)`, with positive coefficients
   and positive constant terms. This proves strict positivity on the whole
   real cone, not merely sampled integer inputs. Since `D,F,I>0` there,
   `T0>0` and `T0^2-2^32 C^14 DFI>0` imply the required strict upper bound.
   The source formulas imply `R>=1`, `N>=8`, and hence `A>=3`; positive `j`
   gives `t=2R+1+(j-1)C>=3`. No source-zero condition is used here.

2. **Soundness has the correct dependency order.** `E0>0` follows from
   `E0=Jn+(J-2)W1^2+3W1C+2`. The case `m=0` is excluded first. For `m!=0`,
   real factorization gives signed roots and
   `E0/J=m(V0+T+u0+u1)`. Both strict majorants hold before any margin or
   integrality conclusion, so the parenthesis is positive and `m>0` follows.
   The inherited margin then yields `C>K` and `C>B1+W1`.

3. **Square-root separation and scaling are valid.** After recovering the
   margin, the source inequalities give
   `DFI>C^2 A^4>K^2 P^2>a0`. Thus `a1=S^2 DFI>a0`. The rational signed sum
   `u0+u1=Theta/Omega` cannot vanish, and the displayed linear identity makes
   both square roots rational, hence integral. Although `S=2^18 C^7` is
   variable, `u1/S` is rational and its square is the integer `DFI`; therefore
   it is integral. No additional divisibility assumption on `S` is needed.
   The factor equation consequently recovers `J|Q` and the unchanged ratio
   conditions. There is no circular reliance on the source zero.

4. **Completeness preserves strict positivity.** The old witnesses give
   integral roots, `J|Q`, and integer `m>=1`. Also
   `F-D=(D-1)(e^2D^2-1)>0`, so the new bound gives `T>S D>2D`.
   Together with the inherited bound `W1^2+Q/J<2D`, this proves that the
   proposed value of `n` is a positive integer. It makes one norm factor
   zero exactly. The new scale therefore creates no lift obstruction.

## Exact degree and literal-implementation checks

I independently parsed the coefficient tables. The unique highest weighted
monomial of `T0`, for weights `(16425,1,1,7963)`, is
`2^26 A^23 C^31 i^5 t`, of degree 385774. The unique highest weighted defect
monomial is `141664530202624 A^22 C^42 i^10 t^2`, of degree 377328. There are
654 majorant terms and 3781 defect terms; the defect has A-degree 22.

The two-defect identity is algebraically correct. With `deg Omega=82360`,
`deg V0=57239`, `deg K=28620`, and `deg T=385774`, its four term degrees are

```
1084096, 1149781, 1158228, 821246.
```

The third is uniquely largest. It is `4 Omega^4 (K^2-1) T^2`, whose diagonal
leading coefficient independently simplifies to
`2^166 a^578828 c0^276>0`. Hence the stated degree is attained for the actual
fixed constants, and is not merely a syntactic upper bound.

Independent reachability of the literal JSON finds **861/861 live nodes**,
including **430 multiplications, 265 additions, and 31 subtractions**. There
are precisely the nine declared variable names. The serialized definition
of `Laurent_t` is exactly `B1+(j-1)C`. The source coefficient recipes, base and
threshold scale exponents, bit-length metadata, coherent-tuple identifier,
source/layout hashes, and source calibration parameters equal those of the
pinned source71 DAG. I also inspected the cone tables: all 9216 majorant
coefficients and 32637 defect coefficients are positive, with positive
constant terms, consistent with the recorded exact-expansion verification.

## Small verifier hardening suggestion

The present artifact is correct, but `verify.py` treats `Laurent_t` as a cut
leaf without separately verifying its definition. Likewise, source-DAG
canonicalization identifies fixed coefficients by name; it should additionally
compare the new coefficient recipes and scale metadata with the pinned base.
Those facts were independently checked directly in this review. Adding the
checks would make later accidental changes fail automatically. They do not
require changing the polynomial, proof, counts, or degree.


## Release follow-up

Both suggested verifier checks were added before release. The final
`nine_full_radical/VERIFICATION.json` records
`guard_parameter_identity_checked: true` and lists the fixed metadata
fields compared with the pinned source. The final offline replay also
regenerated all four source31 coefficient integers byte for byte.
