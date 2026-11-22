# ProveIt source audit for the quantitative implicit function theorem

Inspected branch: `main`, pinned through the GitHub connector to commit
`d36b35eed5bd01af4ade66bf539622495813ccc8` (commit timestamp
2026-11-22 01:33:01 UTC; November 21 in the user's timezone).

No repository changes and no local rebuild of these modules were performed.
The source bundle contains only the listed relevant files, not their transitive
import closure. The saved `source_manifest.json` records exact blob hashes and
commit-pinned URLs. The repository's root README and per-project status distinguish
object-theory derivations from archived research packets.

## Most useful checked object-theory interfaces

All paths below start with
`Logic/PrimitiveRecursiveArithmetic/Derivations/Lean/IPRADerivations/`.
The namespace prefix is `LeanProofs.IPRA`.

| File | Declaration and exact scope | Use and remaining boundary |
| --- | --- | --- |
| `Foundations/ContractionTrace.lean` | `contraction_iter (D : PTm 2)`, object terms `a b x N : PTm n`, turns the premise `forall j < N, b D(j+1,x) <= a D(j,x)` into `b^N D(N,x) <= a^N D(0,x)` in `Prf PRAAx`; explicitly uses `PRA.qfInd`. `contraction_unique` derives `d=0` from `a<b` and `b*d<=a*d`. | Correct internal variable-iteration template. The new inexact recurrence needs the additive error term and rational coding, rather than a direct invocation of the exact homogeneous estimate. |
| `Analysis/HalfContractionTail.lean` | `halfPrem` is the object formula `forall i, 2 d(i+1,x) <= d(i,x)`. `halving` proves `2^i d(i,x) <= d(0,x)` for object index `i`. `tail` proves `2^m Sum(d,m+j) <= 2^m Sum(d,m) + 2 d(0,x)` for object terms `m,j`. | Internal finite geometric-tail argument, with the potential `U(k)=Sum(d,k)+2d(k)`. The displayed inequalities are over cleared natural-valued terms; general rational trajectories need the encoding adapter. |
| `Analysis/DyadicCauchy.lean` | For fixed PR symbols `p q : PR 2`, signed value `a(k,x)=p(k,x)-q(k,x)`, `motion` says `forall k, abs(2 a(k,x)-a(k+1,x))<=1`. `dyadic_cauchy` proves the closed universally quantified object formula `motion -> abs(2^r a(N,x)-a(N+r,x))+1<=2^r`. `dyadic_endpoints` uses internal `N<=M`. | Strong internal coherence provider if new approximants are converted to this exact adjacent integer format. Its special motion premise is not automatic for arbitrary fast rational names; proving it or using a direct pairwise Cauchy invariant remains necessary. |
| `Analysis/FiniteFTC.lean` | `ftc_upper` and `ftc_lower` sum local signed error inequalities, with internal finite mesh length. `UpInv` and `DnInv` are quantifier-free inequalities for the accumulated signed sums and `N*E`. | Direct model for the subdivision proof deriving a Lipschitz/segment bound from Taylor certificates. Does not supply C1 data or a general real FTC by itself. |
| `Foundations/ContractionIterates.lean` | `Contr F B d` supplies derivation-transforming rules for preservation and exact halving; `iter_contract` and `cauchy_iterates` use internal object indices and `PRA.qfInd`. | Useful exact fixed PR map iteration. The new fixed-precision evaluator is inexact, so contract hypotheses require an adapted error invariant. |

## Useful finite schemas, with an external/internal index distinction

| File | Actual Lean boundary | What must not be claimed |
| --- | --- | --- |
| `Analysis/FeedbackInexact.lean` | `inexact_budget` constructs `Prf PRAAx` proofs of `2^k abs(u_k-v_k) <= (E0 + Sum_{j<k} 2^(j+1)(eps_j+eta_j))*w_i`. Here `k : Nat` is a Lean metatheoretic index and `num (2^k)` is an object numeral. The family is recursively constructed outside the object theory. | It is not already one internally universally quantified proof for the runtime iteration bound. Its recurrence is reusable as the local proof pattern. |
| `Analysis/WeightedFeedback.lean` | A finite-dimensional certificate carries positivity, weighted row halving, domain preservation, and gain estimates. `contract_scaled`, `box_invariant` are derivation transforms; `orbit_inc`, `orbit_tail`, `name_bound`, and `residual_bound` are externally indexed families. | Do not infer a runtime-dimension/runtime-iteration theorem merely from Lean parameters `m` and `k`. |
| `Foundations/NeumannCorrection.lean` | `geometric_left` and `geometric_right` derive exact finite matrix identities in `Prf PRAAx`. Matrices have a fixed external dimension, and `N : Nat` is external: `(I-M) sum_{j<N} M^j = I-M^N` and the right identity. | The new numeric matrix-loop implementation still needs PR codes and object QF induction for runtime `N`. The source proves exact identities, not a convergence theorem or a completed inverse. |

## Why this distinction matters for the new theorem

The source read supports a precise reuse claim: the necessary elementary
arithmetic, signed-error summation, contraction arithmetic, and finite Neumann
identities already have object-proof implementations. It does not support a
claim that the complete general C1 implicit function theorem is already
formalized. The new work must supply rational/vector coding, the clipped
fixed-precision program, a variable-length inexact trace theorem, modulus-driven
subdivision, and the Taylor/Neumann derivative interface.

For a fixed precision the natural new quantifier-free invariant is the
denominator-cleared form of
`2^j E_j <= E0 + 2*eta*(2^j-1)` for the recurrence
`E_(j+1) <= E_j/2 + eta`. The coordinate conjunction is a PR Boolean fold.
The real-name error is handled at a fixed auxiliary rational observation
precision before induction; it is not a Pi1 real inequality used as an
induction formula.

## Archived packets actually read

`docs/proofs/analysis/ipra_certified_continuation_2026-11-19/paper/sections/03_feedback.tex`
contains a finite weighted contraction development, residual comparison,
inexact convolution bounds, a finite Neumann producer, and a discussion of
Boolean folds and the universal PR evaluator obstruction. It explicitly marks
its accompanying reference Lean file uncompiled and the object port incomplete.
Some components have since been implemented in the Derivations files above.

`docs/proofs/analysis/ipra_constructive_analysis_2026-11-20/roots.tex`
gives an important complementary pattern: fix the requested observation
precision before bracket induction, then remove the arbitrary positive slack
by a bounded choice based on a rational denominator. Its exact-root discussion
also explains why a continuity modulus alone does not yield a coherent root
name without further local structure. The implicit theorem's uniform
contraction is precisely such additional structure.

## Citation base

Commit-pinned base:
`https://github.com/VladimirReshetnikov/ProveIt/blob/d36b35eed5bd01af4ade66bf539622495813ccc8/`

The project-level status text read in full is
`Logic/PrimitiveRecursiveArithmetic/README.md`, copied as
`PrimitiveRecursiveArithmetic_README.md`. Its description of archived research
packets is explicitly weaker than the claimed kernel-checked status of
`Derivations/`; this audit preserves that distinction. No `AGENTS.md` exists at
the repository root, `Logic/`, or `Logic/PrimitiveRecursiveArithmetic/` at this
commit, and the inspected Derivations and docs subtree inventories contain no
such file. An unrelated FabiusFunction policy was not applied.
