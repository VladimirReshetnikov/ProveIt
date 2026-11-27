# Analysis of the ProveIt merged GRH article

## Snapshot and scope of inspection

Repository: <https://github.com/VladimirReshetnikov/ProveIt>.

Pinned `main` commit read through the GitHub connector:
`22e5c8b7dda558fd9a50b61465483cb4c0433694`.

Article directory:
<https://github.com/VladimirReshetnikov/ProveIt/tree/22e5c8b7dda558fd9a50b61465483cb4c0433694/Analysis/GeneralizedRiemannHypothesis/Article>.

The README and the source sections `src`, `spn`, `li`, `rec`, `ana`, `tors`,
`lub`, `cost`, introduction and abstract were fetched for inspection.
These external source snapshots are not bundled; the pinned links below
identify the source version.
The source theorem/mechanism and the matrix-statistics sections were read in
detail, together with several analytic sections and their open questions.
This is a targeted source review, not verification of all 760 statements.

## What the article claims about its own status

The README describes a 621-page merge of 103 delivered reports with 760
theorems/propositions/corollaries/lemmas. It explicitly calls the article a
merge rather than a review, says nothing was recomputed, and says claims
have not been independently checked or formalized. It marks statements as
unconditional, dependent on Dirichlet GRH, or reductions with the target
estimate open. It takes the upstream RH/Dirichlet-GRH result as input.

Source:
<https://github.com/VladimirReshetnikov/ProveIt/blob/22e5c8b7dda558fd9a50b61465483cb4c0433694/Analysis/GeneralizedRiemannHypothesis/Article/README.md>.

`sections/src.tex` pins the upstream development to
`72fead102f663d5c7a407964a13dc0cf9d977207`. Its stated input covers Riemann
zeta and Dirichlet L-functions over Q, including imprimitive characters in
the open strip. It does not extend those quantifiers to all Artin or
automorphic L-functions, and it does not claim simple zeros.

## Transferable mechanism

The arithmetic proof compares short integral theta-lift forms, nearly full
spanning by translates, and a product-formula lower bound on the same
corrected covolume. Near-full spanning arises from second moments and a
positive-type Fourier estimate. These finite representation-theoretic
parts motivate matrix compression statistics independently of GRH.

The article develops that connection in `spn:sec:positive-type` and
`spn:sec:symplectic`. An unconditional general symplectic compression bound
is

\[
d_{TV}(M(g),U)\le C q^{-(n+1-a-b)/2}
\]

when the ambient symplectic dimension is `n` and `a+b<=n`. It is useful
when the dimension slack grows, and does not force convergence in the
critical regime `a+b=n`.

Source:
<https://github.com/VladimirReshetnikov/ProveIt/blob/22e5c8b7dda558fd9a50b61465483cb4c0433694/Analysis/GeneralizedRiemannHypothesis/Article/sections/spn.tex>.

## Existing results that must not be relabelled as new

1. `spn:thm:symplectic-exact` computes a positive critical-limit TV distance
   for a Lagrangian source and an isotropic test space of fixed codimension.
   The limiting optimal event is a rank deficiency of one.
2. `spn:thm:lagrangian` gives an exact matrix likelihood for a Lagrangian
   output and an arbitrary source alternating form.
3. `spn:thm:growing-form` already shows exponential convergence of the rank
   law while the full-matrix law retains a positive discrepancy when the
   symplectic rank of the source grows. Its optimal obstruction is
   non-isotropy of the ordinary kernel.
4. The article already proves substantially more about binary principal
   nullity than older conversation summaries mention: two-point
   concentration near sqrt(n), sharp above-threshold rare tails,
   near-saturation asymptotics, and exact even saturation counts.
5. `rec.tex` contains robust quadratic-character decoding from low zeros,
   Li/moment recovery and prescribed-zero positive averaging; earlier
   work also extends character decoding to arbitrary order and edit errors.

## Precise boundary for the selected new theorem

The selected theorem takes **both** half-dimensional spaces nondegenerate,
so neither is Lagrangian. In the notation `N=2m`, the ambient dimension is
`2N=4m`. A block `A` of a uniform isometry for `diag(J,J)` has likelihood
depending on the nullity of its **alternating defect**

\[
D(A)=J-A^TJA.
\]

The new content relative to the merged article is the complete likelihood
sign comparison, the exactly optimal test `det D(A)!=0`, the positive
critical-limit discrepancy, and a sharp first-order universality theorem
for the ordinary rank distribution, with an `O_q(q^{-2N})` remainder.
The companion theorem gives the entire defect-nullity law relative to a
uniform alternating matrix, again with its leading signed correction and
an `O_q(q^{-2N})` remainder.

The article explicitly leaves a general two-subspace symplectic law open
in `spn:q:symplectic`. An earlier delivered general finite-frame law,
*Exact symplectic compression laws* (26 November 2026), already implies the
finite likelihood by specialization; therefore the correct research claim is the **critical
growing-dimension detector and universality extension**, not invention of
general Gram-fibre counting or an entirely new framework.

The new theorem is unconditional. Its connection to the GRH development is
through its finite spanning/Fourier/compression mechanism; it is not an
arithmetic consequence of accepting GRH. No further RH, BSD, Artin
holomorphy, or other named conjecture is claimed.

## Independent mathematical and computational checks

The mathematical proof received a separate review. The following points checked:

- The Gram equation automatically gives injective frames because the source
  form is nondegenerate.
- The normalized general embedding count is
  `q^(Dj-j(j-1)/2) prod_(i=D/2-j+s+1)^(D/2)(1-q^(-2i))`.
- The exact Gaussian-moment expressions follow from frame transitivity.
- Finite Lagrange interpolation at `1,q,...,q^N` gives a quantitative
  conversion from moment differences to mass differences; no abstract
  moment-determinacy theorem is needed.
- Defect nullities are even, and interpolation at `1,q^2,...,q^(2m)`
  supplies the stronger coefficient decay needed for the companion result.
- In that companion result, `K` being in the defect radical forces `U|K`
  injective: if `Ux=0`, then `J(x,y)=0` for every `y`, hence `x=0`.
- Swapping the two nondegenerate ambient summands proves the exact identity
  connecting the optimal defect event with invertibility of the block.

The independent checker is
`code/verify_exhaustive.py`; exact output is
`results/exhaustive.json`. It enumerates all matrices
and forms Gram-frequency tables rather than generating probabilities from
the proposed formula. Cases are `(q,N)=(2,2),(2,4),(3,2),(4,2),(5,2)`;
the extension field uses `F_4=F_2[x]/(x^2+x+1)`. Every exact fibre count,
frame total, likelihood sign and optimal-test identity passes.

For `(q,N)=(2,4)`, it obtains full-matrix TV `6767/52224` and rank-TV
`1087/52224`. The distinction already appears in a 4-by-4 binary block.

