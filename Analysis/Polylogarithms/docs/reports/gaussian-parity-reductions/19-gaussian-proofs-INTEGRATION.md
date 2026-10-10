# Proposed source corrections

## Pinned base and application

This reviewable patch targets ProveIt commit
`09812e81e578c3f13f54b2d0c46a95a0e0665b19` and changes only:

- `Analysis/Polylogarithms/docs/manuscript/chapters/04-depth.tex`
- `Analysis/Polylogarithms/docs/manuscript/chapters/06-cm.tex`

It was generated from temporary copies. The supplied source snapshot was
not modified. Run the following from the root of a checkout at the pinned
commit, using the actual location of the delivered patch:

```bash
git apply --check /path/to/proposed_corrections.diff
git apply /path/to/proposed_corrections.diff
```

The first command passed against the supplied snapshot. The patch has
120 insertions and 83 deletions across the two files; it does not rewrite
either chapter. If the checkout has advanced, reconcile these local changes
with intervening edits before applying them.

## Substantive changes

| Location | Change and justification |
|---|---|
| Chapter 4, Gaussian reduction table introduction | Marks the five weight-six doubles and three displayed weight-four triples as proved by the companion article. Their existing coefficients are unchanged. The other numerical equations retain their stated status; a spanning conclusion drawn from an unproved numerical relation is made conditional. |
| Chapter 4, single Gaussian and Eisenstein values | States the zeta formulas for integer orders `n >= 2` and gives the separate logarithmic values at `n = 1`. This prevents a formal substitution of the divergent `zeta(1)`. |
| Chapter 4, diagonal `Li_{3,3}(i,i)` | Replaces the incorrect software-vocabulary claim with the exact stuffle consequence `9 zeta(3)^2/2048 + 47 pi^6/1935360 - 3 i pi^3 zeta(3)/1024`. |
| Chapter 4, antisymmetric combinations | Uses `Li_{a,b}(x,y) - Li_{b,a}(y,x)`, exchanging both indices and colors. Equal indices alone do not imply vanishing at different colors. |
| Chapter 4, mixed Gaussian and Eisenstein coordinates | Supplies exact reductions of all four coordinates previously presented as new mixed directions. Replaces the associated dimension narrative with the distinction between a residual in a selected formal system and the existence of further parity relations. No replacement numerical dimension is claimed. |
| Chapter 6, differentiated line law | Corrects the sentence that calls the just-evaluated components opaque. The line law evaluates the real part at odd weight and imaginary part at even weight; it does not fix their complementary components. This limited statement does not assert non-reducibility by other methods. |

The two real weight-five mixed relations have small integer heights: 1024
in the Gaussian case and 843 in the Eisenstein case. Both use atoms already
named in the source basket. Missing them at the reported approximate
`10^4` scale cannot be explained solely by large coefficients. The patch
requests reproducibility of the actual values, basis, dependence handling,
and stopping rules, without guessing which implementation detail caused
the reported failure.

## Suggested report location

Copy the complete extracted package into
`Analysis/Polylogarithms/docs/reports/gaussian-polylogarithm-proofs-2026-10-09/`.
Its root TeX file, section inputs, figure, code, and results are all relative
to that directory. The existing main manuscript need not share these
macros until the proofs are explicitly integrated. Build the companion
with `make pdf`; the supplied PDF can be read directly.

## Companion proof pointers

The patch deliberately introduces **no bibliography key** into the main
manuscript. Plain prose identifies the companion article, and LaTeX
comments provide these integration pointers:

| Result in the source | Companion file and labels |
|---|---|
| Five weight-six Gaussian doubles, source labels `gauss:eq:g51` through `gauss:eq:g15` | `sections/parity.tex`; `sec:gaussian-six-proof`, `thm:gaussian-inversion`, `cor:gaussian-coefficient-rule` |
| Three displayed Gaussian weight-four triples | `sections/one_two.tex`; `one2:sec:triples`, `one2:thm:triples` |
| Four mixed-root reductions | `sections/mixed.tex`; `thm:inverse-color`, `eq:inverse-color-one` |

When the companion article is placed in the repository, replace the plain
companion reference with the repository's chosen bibliographic entry or
integrate the relevant proof into the chapter. The comments are pointers,
not cross-document `\ref` commands. The four new equation labels in the
patch are local to Chapter 4 and resolve within that chapter.

The general depth-two parity theorem is established prior work. The
companion attributes its functional equation to Panzer, *The parity
theorem for multiple polylogarithms*, arXiv:1512.04482v3, equation (3.2),
with the index order reversed to match the repository's convention. The
new proof status here is relative to the pinned snapshot. No priority
claim for the general theorem or all four mixed-root formulas is implied.

## Scope and checks

Exact symbolic generation reproduces the five original Gaussian rows and
the four displayed mixed corrections. The companion separately proves the
three weight-four triples. Independent numerical checks are described in
the companion, with exact rational enclosures provided for the supported
Gaussian cases. The patch does not upgrade unrelated historical precision
claims, certify absent source scripts, or assert numerical independence
of any remaining coordinates.

Other rank and numerical-dimension statements elsewhere in Chapter 4 need
their own reproducible relation systems. This patch removes the specific
mixed-candidate conclusions invalidated by the four exact formulas; it
does not silently certify every earlier dimension statement in the chapter.

Original file SHA-256 values were checked before and after patch generation:

```text
04-depth.tex  e11d9eadf7dea3ba71e43de97124c00aff9e7b346ddbd76005d91eea4170e4a2
06-cm.tex     d21653080fbf86e3ddf00c76fb947bdd7aadaf3b0c0fc391e92445742bb95a02
```

