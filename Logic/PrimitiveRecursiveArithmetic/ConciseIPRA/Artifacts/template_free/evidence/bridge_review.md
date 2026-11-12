# Review of the inherited iPRA bridge

This is an additional assistant mathematical/source review, not an external
human review or a new proof-assistant certificate. The reviewed frozen source
files and their hashes are recorded in `sources.json`. The new G rule and its
oversized-marker equivalence proof are not part of those inherited Lean files.

## What “full first-order iPRA” means here

`reference/PR.lean` defines a numerical function symbol for every fixed finite
primitive-recursive description: zero, successor, projections, composition and
primitive recursion. The recursion argument is first, with equations

    prec(f,g)(0,p)   = f(p)
    prec(f,g)(Sn,p)  = g(n,prec(f,g)(n,p),p).

The logic is full intuitionistic first-order natural deduction with actual
equality and genuine falsity. The arithmetic axioms are the projection,
composition and recursion equations, successor injectivity, `Sx=0 -> false`,
and induction for every quantifier-free formula, with parameters. “Full” means
that formulas, hypotheses and conclusions may use all first-order logical
operations and quantifiers; it does **not** mean induction for arbitrary
quantified formulas. Quantifier-free formulas include implication and falsity.
Descriptions are external finite syntax, not numerical codes supplied to a
single internal universal evaluator.

## The exact native comparison and theorem statements

`reference/Native.lean` defines `NPrf` over all Eq/Q/D formulas, with the eight
rules Hyp, I0, IS, equational Tr, QE, DE, DI-case and atomic QI-progress. Its
ordinary readings are exactly

    Q_y B(y)       = B(0) -> forall y B(y)
    D_(x,y) B(x,y) = exists x (B(x,0) -> forall y B(x,y)).

The proposed seven-rule theory changes the equality inference to G and uses
the already established witness-sensitive introduction. Its required bridge
is exact equality of consequence relations with this unrestricted NPrf,
for every context and every native formula. Agreement only on equations,
closed goals, guarded formulas or standard numerical values would not suffice.
The marker proof in `global_rewrite_marker_proof.md` supplies the equality
part without induction or substitution into a new derivation. Its later
case/progress recovery supplies both missing introductions.

`reference/NativeBiInterpretation.lean` explicitly supplies the following
stronger inherited results, so no semantic strengthening is being inferred
from mere equiconsistency:

- `native_iff_pra`: native derivability of a sequent is equivalent to iPRA
  derivability of its translated sequent.
- `pra_iff_native`: the corresponding converse for arbitrary iPRA sequents.
- `native_roundTrip`: the iPRA round trip of every native formula is
  interderivable with that formula.
- `pra_native_roundTrip`: every iPRA formula is provably equivalent to its
  native round trip, in arbitrary retained contexts.
- `native_inconsistent_iff`: native derivability of `0=S0` from no assumptions
  is equivalent to iPRA derivability of falsity.

The definitions are `toPRA A = A.toFm.map ToPRA.tau` and
`ofPRA phi = NFm.ofFm (phi.map FromPRA.sigma)`. The scalar/iPRA component is
`biInterp : BiInterp TeqAx PRAAx` in `reference/BiInterpretation.lean`, with
term-composite proofs from `RoundTrip.sigma_tau` and `RoundTrip.tau_sigma`.
Both numerical domains are whole, interpreted equality is actual equality,
and both isomorphism graphs are `x=y`. There is no domain cut or quotient.
Once G and NPrf have the same sequents, these same translations and their
formula-composite derivations transfer unchanged to G.

## What the appendices establish and their presentation conventions

`inherited_ordinary_bridge.tex` states the ordinary scalar theory explicitly:
I0, IS, numerical coverage, `(0=S0)->false`, and contextual literal-equation
induction over intuitionistic equality logic. The explicit falsity bridge is
essential. The appendices give the arithmetic dependency order:

1. Scalar predecessor before successor injectivity or pairing.
2. Truncated subtraction and a term reflecting actual equality on the whole
   domain.
3. Characteristics for all quantifier-free formulas, hence their induction.
4. Pairing by a bounded square-root search and compilation of each finite
   primitive-recursive description.
5. Internal uniqueness of the recursively defined operations, hence both
   numerical composites at arbitrary internal counters.

The opening of `equality_reflection.tex` explicitly explains its scalar
application: the proof uses only predecessor, the scalar selector, addition,
monus and their finite compositions. Thus its PR-flavoured general statement
does not require the later general compiler in the scalar application.

`inherited_choice_basis.tex` uses an older Eq/D presentation with reusable
clauses and formula-template transport. Its macros and its round-trip proofs
explain the same logical interface, but its primitive rule table is not the
new G rule table. In the formal native language Q is explicit, and
`NativeEq.lean` supplies formula-template transport as a derived rule.
The main report should keep these presentation conventions distinct and
attribute the appendices as inherited material.

## Verification boundary

The inherited Lean sources were inspected, not rebuilt during this work. The
selected copied `.lean` files are reference excerpts with upstream imports,
not a self-contained Lake project. The repository reports successful builds
of its native bridge; this package does not claim a new Lean verification of
G, its Python codec, or the oversized-marker lemma. Finite executable tests
are evidence about the implementation, not substitutes for the universal
metatheorem.

## Final bounded comparison check

The final branch check was frozen at commit
`2a724ea8ec6665f91aa74c892414584b36ca698d`, dated
2026-11-12 01:58:39 UTC, with message “New research report(s)”. The comparison
from `521884df22e8f2dac0b7066095a42ae975ea4166` contains sixteen commits.
Within ConciseIPRA, it adds exactly these three archives and changes no
existing Lean source:

- `ipra_checked_refinement_2026-11-11.zip`: explicitly implementation-only
  checker reductions.
- `ipra_validated_core_2026-11-11.zip`: explicitly implementation-only shared
  validation.
- `ipra_one_sided_transport_2026-11-11.zip`: the previously encountered
  one-template crossed rule, with a nonliteral-zero source, and a pure-equality
  strengthening. It still supplies the template as part of the inference.

Their READMEs, main reports and relevant formalization text were inspected.
None states the present template-free global replacement rule or the
oversized computation-marker proof. The downloaded ZIPs match the Git blob
hashes returned by the repository API; details are in
`comparison_boundary.json`. This is a bounded comparison with the supplied
proposal, not a literature-wide novelty or absolute-minimality claim.
