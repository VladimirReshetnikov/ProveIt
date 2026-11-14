> Release note: this review was written before final integration of the physical/source proof. The completed written theorem is now in `proof/physical_ipra_audit.tex`. The source-to-command and PA-calibration obligations identified here remain open. See `claims.json` for the final status.

# Focused follow-up: weak-base PA-to-numerical calibration

Audit target: `VladimirReshetnikov/ProveIt`, commit
`1c9524d8bf2e0a27b9a16ff622359927f536e663`.
This is a separate mathematical audit; it does not change the AX11H/QAX11H
command-preservation proof.

## Outcome

There is a real reduction in the outstanding work. The full-PA induction in
`PA196/Arithmetic/CompilerInvariant.lean`, theorem `fuel_invariant`, can be
replaced by the bounded all-store argument in `ax11h_preservation.tex`.
The resulting theorem concerns a *given internal numerical derivation* and
the new abstract commands. Its proof is by quantifier-free induction after
Boolean encoding, so it does not merely assert correctness separately for
standard derivations.

I have **not completed the earlier PA-refutation-to-numerical-certificate
calibration in iPRA or IΣ1**. This conclusion is not inferred from missing
Lean code. The specific missing mathematical work is a uniform bounded
construction for the arbitrary-matrix induction-axiom supplier and its
formula-realization dependencies, together with complete finite request
coverage through the ordinary sequent compiler. Several inspected local
maps make such a construction plausible. They do not constitute its full
instantiation.

## What the existing calibration actually supplies

The inspected report is
`Computability/BusyBeaver/Research/PA/docs/pa194_conpa_2026-11-13/report/reference/original_pa195_calibration.tex`.
Its theorem explicitly has **PA** as metatheory. Its forward-calculus
equation imports the published PA196 compiler and replaces selected
equality-interface proof templates. It claims primitive-recursive proof
transformations with PA-provable correctness. A primitive-recursive map
with PA-provable correctness need not have iPRA-provable correctness;
the latter requires its own proof.

Conversely, the arbitrary induction instance in the report's finite-bit-
comprehension *generated PA proof* is not itself an obstacle to weak-base
verification. A weak metatheory can check that a generated line is an
instance of the full PA induction schema. One must distinguish induction
inside the output PA proof from induction used to establish the uniform
correctness of its producer. Therefore the report's phrase that full PA
induction is used must not be treated as an impossibility result for a
weak-base syntactic calibration.

## A precise bounded-demand lemma

Here is a sufficient replacement for the unbounded oracle-style
inductions. It is a theorem with explicit hypotheses, not a claim that
all hypotheses have now been checked for the repository.

Represent a request as `(r,x)`, where `r` is a numerical rank and `x` is
one code for its remaining parameters. Let `ValidReq(r,x)` and
`ValidCert(r,x,c)` be primitive-recursive Boolean predicates. Suppose:

1. Each valid request has a primitive-recursively computed finite list
   `Q(r,x)` of child requests, each having rank strictly smaller than `r`.
   The entire list is computed from `(r,x)`, independently of the
   certificate values returned by the children.
2. A primitive-recursive constructor `K(r,x,children)` combines the
   corresponding child certificates. In iPRA, validity of the parent
   request implies validity of every request in `Q(r,x)`, and validity
   of those child certificates implies validity of the constructed
   parent certificate. The empty-list case includes a uniform leaf
   supplier; its correctness is part of this hypothesis.
3. The encodings of finite lists, their indexing, the query function,
   and the constructor have their stated elementary correctness
   properties in iPRA.

Fix a root rank `D` and a bound `s` for its parameter code. Define the
total primitive-recursive majorant

    F_D(v) = 1 + max({v} ∪
                 { parameter(y) : r ≤ D, x ≤ v, y occurs in Q(r,x) }).

The maximum is over bounded inputs and finite primitive-recursively
computed lists. Define `B(r) = F_D^(D-r)(s)` for `r ≤ D`. If a parent
request of rank `r` has parameter code at most `B(r)`, then every child
of rank `j < r` has parameter code at most

    F_D(B(r)) ≤ B(j).

Construct, in ascending rank, a table of certificates for **all**
requests `(r,x)` with `r ≤ D` and `x ≤ B(r)`, using the previously
constructed rows for the child lookups. Invalid requests receive a
fixed default value. The whole table construction is primitive
recursive; no bound on certificate output values is needed to define
it. Induct on the number of completed rows with invariant

    for all r < current_rank and x ≤ B(r),
      ValidReq(r,x) implies ValidCert(r,x,table[r,x]).

Both displayed universals are bounded and are represented by a finite
Boolean fold. This is a quantifier-free induction invariant in the
language containing the displayed primitive-recursive functions. The
child-bound inequality and hypothesis 2 establish the successor step.
The root is in the final table. Universal generalization over `D,s`
gives a uniform iPRA certificate constructor.

This proves that unbounded universal *formulations* of these induction
invariants are not intrinsically necessary. It does not permit omission
of hypothesis 2's actual uniform axiom suppliers or the request list.
In particular, writing “take a bound large enough for the recursive
calls” without defining certificate-independent queries would leave
the essential point unproved.

## Exact request maps that were inspected

All paths in this section are relative to
`Computability/BusyBeaver/Research/PA/jamesyc-upstream/pa196/`.

The sequent endpoint is
`PA196/Arithmetic/Transport/NumericPAeqSequentDerivation.lean`,
`ordinary_derivation_requested`.
Its actual requested-certificate interface, defined in
`NumericPAeqSequentDerivationInvariant.lean`, is

    RequestedCertificate(f,s) :=
      ∀ native lo z,
        FormulaCovered 0 native lo z (guardedCode f s) →
        ∃ c, verifyValue c =
          translate (parameters 0 native lo z) (guardedCode f s) + 1.

The proof-budget invariant additionally quantifies all environments `f`
for all smaller derivation codes. Keeping this formula unchanged does
not make it a Σ1 invariant.

The following maps are explicit and do not depend on child certificate
values:

| Source theorem/file | Actual child request |
|---|---|
| `NumericPAeqSequentExsRule.lean` | With `r = max(guardedCode f (insert(substs1 u p) s), existentialRuleCode f p u)`, query `(padEnvironment native r, lo, z+lo+r)`. |
| `NumericPAeqSequentShiftRule.lean` | With `r = guardedCode f s`, query `(padEnvironment native r, lo, z+lo+r)` at the child environment `f` of parent `x∷f`. |
| `FoundationRelationalSequentRequestedUniversal.lean`, `requested_universal_certificate` | With `d = free p + 1`, query `(lo∷padEnvironment native d, lo+1, z+lo+d)` for the opened formula `free p`. |
| `NumericPAeqValueCertificateComposition.lean`, `source_implication_compose` | With `r = max(imp a b, max(imp b c, imp a c))`, both supplied implications are requested at `(padEnvironment native r, lo, z+lo+r)`. |
| `NumericPAeqSequentAllChild.lean` | Use `eigenEnvironment f`, shifted context, and `r = guardedCode (eigenEnvironment f) (insert (free p) (setShift s))`; request at the corresponding padded triple. |

These equations are useful concrete inputs to the bounded-demand lemma.
They are not a complete enumeration: the universal context construction,
for example, nests universal introduction, modus ponens, implication
composition, a free-domain prepend certificate, and a curry template.
Its induced demand list must include every nested query. Readback and
formula-coverage lemmas must also hold under the intended weak base.

## The exact outstanding axiom-supplier chain

The ordinary sequent axiom rule calls
`NumericPAeqOrdinaryAxiomCertificate.lean`,
`ordinary_axiom_requested_certificate`. It splits into fixed axioms and
an **arbitrary internally coded PA induction axiom**. The latter calls
`NumericPAeqInductionAxiomCertificate.lean`,
`induction_axiom_requested_certificate`. Its required interface is:

    targetInductionR(q) ∧ FormulaCovered(0,native,lo,z,
       formulaSyntax(parameters(0,f),q))
      → ∃c, verifyValue(c) =
         translate(parameters(0,native,lo,z),
                   formulaSyntax(parameters(0,f),q)) + 1.

This particular closed-induction theorem permits arbitrary `f`; the
closed-environment lemma removes its influence. Its quantifiers range
over all internal codes, not only standard PA induction formulas.
The source file presently assumes a model of full PA.

Unfolding this endpoint exposes at least these nontrivial uniformities:

* `NumericPAeqGuardedAlls.lean`, `matrixSupply_alls`, iterates universal
  closure. It explicitly uses `InductionScheme.succ_induction` with
  `C := Set.univ`. Its predicate universally quantifies `s,p` and then
  asserts an implication from `MatrixSupply(s+k,p)` to
  `MatrixSupply(s,qqAlls p k)`. `MatrixSupply`, defined in
  `NumericPAeqGuardedAllsSyntax.lean`, itself quantifies all bound and
  free term environments and all covered native label triples before
  asking for a certificate. This is another full-induction use below
  the advertised sequent endpoint.
* `NumericPAeqCanonicalMatrixCertificate.lean`, `matrix_certificate`,
  invokes `open_source_formula_realization_certificate` when relating
  the actual substituted matrix to its original formula.
* `NumericPAeqFormulaRealization.lean`, `open_source_formula`, proves
  that last supplier by another explicit `C := Set.univ` induction on
  formula codes. Its `FormulaSupply` quantifies the changing depths,
  substitution vectors, environments, and requested native labels.
  Its local formula cases are separately factored, but their complete
  finite request maps and weak-base correctness have not been supplied
  in this audit.
* The mathematical ordinal-induction template itself is a fixed
  derivation: `RelationalPredicateTemplateOrdinalRequested.lean`
  invokes `template_nd_requested_certificate inductionDerivation ...`
  with `induction_axiom_certificate` as its axiom callback. This is
  promising because the outer template is fixed. It does not by itself
  discharge the arbitrary-formula substitution, coverage, and callback
  correctness needed to use it uniformly.

Therefore replacing just `ordinary_derivation_requested` and
`fuel_invariant` would not by itself eliminate the full-PA assumptions
from the forward chain. The forward-audit README says “two explicit
uses”; it does not claim to enumerate every transitive use.

## What can and cannot be concluded now

The following two claims have different status:

1. **Established in the new written argument:** an internal finite
   derivation in the stated numerical calculus has an all-store
   AX11H/QAX11H refutation word, with uniform correctness provable by
   quantifier-free induction. Together with the separately stated
   scheduler equations, this removes the need to inherit the old
   full-PA command-fuel argument.
2. **Not established by this follow-up:** every internal PA refutation
   produces such a numerical derivation in iPRA/IΣ1. To establish this
   via the inspected upstream route, supply explicit demand lists and
   weak-base-correct leaf constructors for the chain above, prove
   their coverage conditions, and instantiate the bounded-demand lemma.
   Then port the numerical verifier and replacement-interface maps to
   the exact new calculus. No inference from standard-model executions
   or finite testing supplies these obligations.

Nothing found is a counterexample to weak-base calibration, and no
impossibility claim is justified. But an unconditional assertion of the
requested iPRA equivalence is not supported by a complete proof in hand.
The positive physical simulation remains a separate obligation even
after the mathematical calibration is completed.
