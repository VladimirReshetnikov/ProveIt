# Independent review: dominated-pairing codec isomorphism

Date: 2026-10-20.

## Verdict

**PASS for the stated native proof-system isomorphism.** The Cantor-to-2-adic
case is an explicit arithmetizable bijection that transports the complete
native theorem relation and fixes F=1. Simultaneous translation of labels
and formula fields correctly preserves the seed's code-as-label coupling.

Reviewed file: `research217_codec_pairing/CODEC_ISOMORPHISM.md`.

Reviewed SHA-256:
`43b1d59adc16ce31044848f2aafd47ceea1f8633c9a345a2acf9feefe469bb64`.

No received code was executed and no proof-assistant build was performed.
No source-size, runtime, fairness, or machine-state claim is certified here.

## Recursive definition and inverse

Let beta and gamma be bijections N^2 -> N, each mapping (0,0) to 0 and
dominating both components. For a positive tagged number n, both decoded
components are <=floor(n/4)<n. Therefore the proposed f and g are legitimate
course-of-values definitions. The isolated definition f(0)=g(0)=0 handles
the only nondecreasing decoding case.

Positivity induction is valid: a positive code of nonzero tag stays
positive; a positive tag-0 code has a positive child, which remains positive
by induction, so gamma's zero-preimage property prevents the output being
0. The same proof holds for g.

For every a,b and tag t, the constructor homomorphism equation holds. The
only exceptional input is t=a=b=0, where both sides are explicitly 0.
Consequently strong induction on n proves g(f(n))=n by using g's constructor
equation and the induction hypotheses on the beta-decoded children of n.
It does not require f(n)<n, order preservation, or induction on f(n).
The symmetric argument proves f(g(n))=n. The recursion/inverse proof has no
hidden circularity.

For S(a,b)=2^a(2b+1)-1, factorization of n+1 into a power of 2 and an odd
part gives a unique inverse. The claimed component bounds follow from
2^a>=a+1 and S(a,b)>=2b. Thus P and S satisfy the hypotheses. The functions
in this concrete case are primitive recursive, including their inverses
and the finite course-of-values translation. For a general pairing interface,
effectivity and formalizability are relative to the pairing functions and
their proved properties; arbitrary effective functions should not silently
be assumed primitive recursive. This does not affect the concrete theorem.

## Raw constants and exact native templates

Both translations fix 0,1,2,3, since these decode to the zero pair with the
corresponding tag. In particular truth0 and F=1 are fixed, and negation
I(x,1) commutes with translation.

I rechecked the definitions in KCode230.v, Codes230.v, Codes222.v, and
Thm222.v at the source locations cited in the proof. The active native
axioms are constructor terms in their natural parameters and F. Their only
nonconstructor side conditions are c!=a and c!=b for the full bundle;
bijectivity preserves and reflects these.

The exact nks222 expression has repeated occurrences of c in both label
and opaque formula positions. Translating every numeric field sends each
one to the same f(c). Nothing requires formula substitution inside a fixed
theorem or replacement of the seed by a simplified version. The merged G
row's binder R(a,b) maps to R_gamma(f(a),f(b)), also exactly as required.
The raw-zero failed-gate branch is preserved because f(0)=0.

The downstream source Complete222.v confirms named seed roles 1 and 3 and
the elementary equality labels 0,1,2,3; all are fixed. Larger future raw
literal constants would need to be translated explicitly or proved fixed.
The theorem does not assert that arbitrary natural numerals are fixed.

Fresh-name arithmetic such as successor(x+y), or the implementation of an
equality interpretation using that choice, need not commute with f. The
argument translates completed numerical derivations rather than claiming
that all downstream proof-generating source functions commute with f.

## Exact theorem transport

Induction on a native derivation covers every rule: truth is fixed; each
axiom becomes the same constructor template at translated parameters; gates
are preserved; MP uses the I homomorphism; GEN translates its label as well
as its body. The inverse argument with g proves the converse. Thus

    T_beta(n) iff T_gamma(f(n)),

and, since f(1)=1, the two literal contradiction-derivability statements
are equivalent. Existing ZFC-provable calibration of the exact old native
theory consequently transfers to the new native theory. This conclusion
needs no semantic completeness or theorem-substitution assumption.

The general extension to another basis is valid when its schemas are also
constructor terms with appropriately fixed/translated constants and
preserved side conditions. No unrestricted transfer of arithmetic-coded
axiom predicates is implicit.

## Checked nontransfer boundaries

The stated numerical counterexamples are correct, including the final
explicit reversal of order:

    P(1,1)=4, f(4)=4, S(f(1),f(1))=5;
    f(8)=8, f(16)=20, so f(8+8) != f(8)+f(8).
    f(16)=20 and f(20)=16, so 16<20 but f(16)>f(20).

Therefore the theorem is not conjugacy of raw pairing, stack numbers,
cache additions, or source execution. Formula-by-formula proof translation
does not by itself produce a correct new proof-list parser or fair scheduler.
New stack, cache, enumerator, blank-start, and machine correctness proofs
remain necessary, exactly as the source document states.

The separate support observation is justified: component domination makes
every label in a positive formula smaller than that formula. The inspected
tau_fr and seed_code_gt3 proofs use component bounds; Sound222's merged-row
freshness bounds do as well. This is not permission to reuse the
Cantor-specific triangular-walk proofs or order comparisons through f.

## Artifact verification

An initial read encountered a transient proof/manifest hash mismatch while
the author was adding the explicit f(20)=16 example. I checked that example
and re-read the final hashes. The settled proof and its SHA256SUMS.txt now
both match the reviewed hash at the top of this report. No packaging issue
remains. The original proof and manifest were not modified by this reviewer.
