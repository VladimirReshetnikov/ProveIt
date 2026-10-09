# Proposed corrections to the inspected ProveIt drafts

Prepared October 7, 2026. This is a targeted mathematical audit, not a complete
verification of the directory. The reviewed branch reference was
`c78c7c3dc2fc742a1af9492e47d578b3fb4e01e7`. Blob hashes and reviewed ranges appear
in `../provenance/source_manifest.json`. No upstream files have been changed.

## 1. Replace the unconditional parity “if and only if”

**File:** `gaussian-multiple-polylog-depth.tex`  
**Location:** `thm:alternation`, the “genuine depth” table, and the associated
weight-five and weight-seven claims.  
**Finding:** The positive identities are supported by the new analytic theorem.
The claimed converse does not follow from failed floating-point PSLQ/LLL
searches, even at high precision or high coefficient bounds.

**Proposed replacement:**

> For every integer m >= 0, the value S_(2m+1) belongs to the algebra generated
> over Q by pi, log 2, odd zeta values and even Dirichlet beta values. An explicit
> uniform formula is proved in the research continuation. For even outer
> exponents, the present numerical searches provide evidence concerning a
> specified finite candidate basis; they do not prove non-membership in the
> full depth-one algebra. The proposed irreducibility assertions remain
> conjectural in that stated algebra.

Use `replacement_parity_statement.tex` as an editorial starting point. It
contains the uniform formula and a proof, but it is not an automatic patch:
the abstract, narrative, table captions and later claims also need revision.

A search over one finite list is not a search over an algebra unless the list
is proved to span the relevant component. Adjoining the off-axis values
Im Li_n((1+i)/2) changes the question and should be explicitly stated.

## 2. Remove the canary-as-certificate claim

**File:** `gaussian-multiple-polylog-depth.tex`  
**Location:** numerical verification after `eq:S5` and `eq:S7`; generator
independence discussion.  
**Finding:** A zero coefficient on an unrelated numerical constant does not
prove exact equality of the other constants. Algebraic independence of the
Champernowne constant from the chosen atoms has not been established in the
argument. Transcendence of a single number would not imply that independence.

**Proposed replacement:**

> The canary is an empirical diagnostic against some spurious relations. Its
> zero coefficient is not an exactness certificate. Numerical identities are
> conjectural until justified symbolically or by another exact argument.
> Numerical non-detection, in turn, does not establish irreducibility.

Retain discovery precision, residuals, software versions and coefficient
heights as reproducibility data. Remove language such as “certifying a true
linear dependence” unless an actual symbolic proof is attached. The interval
certificates in this package certify *enclosures*, not equality from overlap.

## 3. Correct the iterated-integral simplex order

**File:** `gaussian-eisenstein-double-polylogs.tex`  
**Location:** `eq:G-def`.  
**Finding:** The displayed increasing simplex is incompatible with the
immediately following standard word formula Li_n(z) = -G(0^(n-1),z^(-1);1).
For the word (0,2), the displayed definition has an inner divergent integral
of dt_1/t_1, while Li_2(1/2) is finite.

Preserve the word formulas and replace

```tex
\int_{0<t_1<\dots<t_n<1}
```

by

```tex
\int_{0<t_n<\dots<t_1<1}
```

The alternative is to reverse every word-to-polylogarithm formula consistently;
changing the simplex is the more localized repair. Retain explicit path and
regularization conventions wherever genuinely necessary.

`apply_goncharov_fix.py` previews this one replacement and refuses any file
whose Git blob hash differs from the reviewed source:

```sh
python corrections/apply_goncharov_fix.py /path/to/ProveIt
# Only after reviewing the printed diff:
python corrections/apply_goncharov_fix.py /path/to/ProveIt --write
```

The script's transformation, refusal path and command-line behavior were tested
on synthetic fixtures. It was not run against a full local copy of the original
repository. No GitHub writes were made. This finding concerns the typeset
convention; it does not, by itself, diagnose the unseen implementation.

## 4. Separate relation-quotient, motivic and numerical dimensions

**File:** `gaussian-eisenstein-double-polylogs.tex`  
**Location:** abstract and introduction statements about exactly five new
doubles, a binomial depth dimension, and three selected irreducible triples.

A computation modulo a supplied list of exact relations identifies a quotient
by those relations. Unless completeness is proved, its dimension is an upper
bound on the space of numerical periods represented by the generators. A
positive ambient motivic depth dimension does not identify which selected
triples have nonzero images. Nor does a weight generating series automatically
identify the depth filtration with word length in another presentation.

**Proposed replacement:**

> The exact relation computation gives reductions and bounds in the explicitly
> defined quotient. Claims of minimal depth for named triples require
> element-specific calculations in the specified motivic depth quotient.
> Passing motivic independence to numerical-period independence requires the
> relevant additional injectivity hypothesis, which is not assumed here.

State the precise motivic object, coefficients, Tate convention, and filtration
before any dimension formula. Do not cite an ambient positive dimension as a
certificate for particular numerical constants. This correction does not
assert that every computed reduction is false; the invalid inference is the
lower-bound conclusion.

## 5. Avoid beta-value independence as an explanation of parity

**File:** `gaussian-multiple-polylog-depth.tex`  
**Location:** “The mechanism: beta(w) as the alternating irreducible.”

Availability of an even beta value in a formula does not establish its
independence from the other constants. Failure to recognize a decimal ratio as
a rational number does not prove irrationality. Replace this explanation by
the beta-integral reflection and its digamma coefficient extraction. This gives
an exact mechanism for the positive reductions without transcendence
assumptions, and makes no unsupported converse.

## 6. Repair convergence and p=0 conventions

**File:** `gaussian-multiple-polylog-depth.tex`  
**Location:** preliminary definitions of multiple polylogarithms and S_p.

For outermost-first nested sums, impose the appropriate conditions on *every
prefix product*, not just the total product. For example,
Li_(1,1)(2,1/4) diverges even though the total product has modulus 1/2: its
inner sum approaches log(4/3), and its outer summand grows like 2^m/m.
Strict prefix inequalities give a simple absolute-convergence region;
boundary cases need separate arguments or regularization.

The ordinary sum S_0 diverges because its terms do not tend to zero. Its Abel
sum is -log(2)/2, from the harmonic generating function. Restrict the ordinary
sum to p>0, and label any use at p=0 explicitly as Abel summation.

## 7. Qualify the sampled Stieltjes rank extrapolation

**File:** `stieltjes-parameter-derivative-tower.tex`  
**Location:** `thm:rank` and the immediately following computation description.

The harmonic-number master identity has a valid direct coefficient proof. No
correction to that identity is proposed here. The rank theorem explicitly
concerns the quotient generated by distribution rows; keep that qualification.
The displayed evidence k=1,2,3 and q=3,...,30 is not by itself a proof for all
k and q. Supply a general algebraic proof, or state the finite result as
verified computation and the universal statement as conjectural. In
particular, do not reinterpret the residual dimension as an unconditional
independence theorem for numerical Stieltjes values.

## Editorial order

Apply the localized convention correction first, incorporate the positive
uniform theorem, then revise abstracts, theorem names, captions and
irreducibility claims consistently. Preserve the historical computations and
provenance. Keep this continuation separate from the historical drafts until
the mathematical and editorial changes have been reviewed.
