# Independent review of the fixed-input arithmetic reduction

Reviewed files: `theory_notes/FIXED_INPUT73_PROOF.md`,
`fixed_input73.json`, `fixed_input63_system.json`, and the pinned upstream
raw75, asymmetric-scale, auxiliary-quotient, and strong-normalization notes.
This is an independent mathematical/source review within the present
collaboration, not an external human endorsement or proof-assistant check.

## Result

No blocking arithmetic or domain error was found in the 73-gate,
16-positive-variable polynomial or its seven-equation counterpart.
The result retains the imported generic Pell strong-rank/step-down lemmas
and the raw75 compiler theorem as explicit proof dependencies.

## Points checked

1. **Unit signs.** The discriminant factors as `(a+1)(a+3)>0`. The
   scaled strong factor cancels exactly. The marker factor is a positive
   integer unit, hence equals one. The main and strong norm signs are
   positive modulo four; the auxiliary factor is a square residue modulo
   four. The negative Pell equation for `V(V+1)`, V>1, is excluded by the
   stated strict descent. This leaves only the index/transport signs.

2. **Pretyping inequalities.** From the marker budget,
   `q=F+2Z+alpha+W0`, one gets F+Z<q and 0<C<q before any power recovery.
   With the actual native masks less than B-1 and the shifted source
   port MF=MF_native+B-1, the bounds
   `(2q-1)(q^2-1)<R<q^4-q^3` hold. The shifted MF convention is essential.

3. **Positive auxiliary reconstruction.** The strong norm gives
   `f^2=1+Delta*i^2*c^4`, so f>c^2>2c. The gap argument excludes negative
   V, and `V=-c mod f` excludes V=0,+1,-1. The reconstructed integers
   `o=cT-Rf` and `j=Tf-R*Delta*i^2*c^3-1` obey `of-c=V`, `jc=V+R`;
   therefore o,j are strictly positive. The note's wording of the
   congruence was clarified during review.

4. **Index sign.** The first Pell classification gives
   `k=2*psi_(2XY^2+1)(n)`, while the main norm gives `c=psi_(a+2)(p)`.
   The imported strong-rank and signed step-down lemmas use no omitted
   input norm. They yield p=R. The inequality E>R+2 excludes first-index
   wrap. The negative index sign would give p=2n+1, contradicting
   `kY<c<k(Y+1)` by Pell duplication. Thus both remaining signs are +1.

5. **Power recovery and the deleted raw-input bound.** The lower ratio
   estimate and projected recurrence give X=2^R with X=wq; hence q is
   dyadic. The fixed marker is W0=2^(2d+b)<q, so q>=2W0. The budget then
   gives `q-C=(q-W0+F+alpha)/2>W0/2>=2d`. Thus the correct restored slack
   is `alpha_raw=q-C-2d>0`. It is not necessary, and would be unsafe, to
   assume the supplied alpha itself exceeds 2d.

6. **All raw75 coordinates.** The restored input Pell coordinates are
   integral and positive since the input exponent u=2d+b is odd and
   u<R. The first Pell root is unchanged: raw75 itself uses tau^2-1,
   not the earlier tau(tau+1) normalization. The asymmetric scale
   restores `w_old=X/q^3>0`; the strong coefficient is `i_raw=Delta*i`.
   The transport quotient is exactly `z_raw=t-1+wC>0`, as follows by
   multiplying the sheared transport equation by q-1. These checks
   support direct reconstruction of the full raw75 system.

7. **Degree.** An independent leading-term calculation gives factor
   degrees 22,18,60,7,2,46,2. Their leader is

   `-8 Q^91 h gamma i^4 (eta+zeta)^13 w^13 s^26 T^2 f^2`
   `*(wZ-tQ)*(Q-F-2Z-alpha)^2`.

   The monomial `J^94 h gamma i^4 eta^13 w^13 s^26 t T^2 f^2` has
   coefficient `8(B-1)^94`, so degree157 is exact. The seven-equation
   system has a unique degree60 residual; its sum-of-squares polynomial
   has exact degree120.

8. **Literal source replay.** The standalone verifier was run afresh:
   41 multiplications and 32 additions/subtractions for the polynomial,
   34 and 29 for the seven-equation system, 16 positive unknowns,
   64 signed whole-source identity fixtures, and exact diagonal degree157
   all passed. Diagnostic numerals are not claimed to compile K215.

## Required semantic wording

The raw75 compiler's arithmetic input x is checked by the normalized
machine at raw input 2x. For x=1 this is raw input2, encoded by four
unary ones. Our normalized K215 machine erases and ignores its unary
input. It need not literally recognize an even-only language: the exact
pointwise compiler statement is solvability at x iff that machine
accepts at 2x. Its proof queries only these even inputs. The final
construction should distinguish arithmetic input1 from normalized
machine raw input2.

## Remaining boundaries

The review does not reprove all upstream Pell classification/rank lemmas,
rerun the historical Lean/Rocq K215 builds, materialize the astronomical
full fixed compiler numerals, or exhibit a complete accepting witness.
It verifies the new reduction conditional on those precisely identified
mathematical compiler/calibration results. The unconditional mathematical
claim is the equivalence with Con(ZFC), not a proof of either consistency
or nonhalting.
