# Independent mathematical review of the inherited guarded-source presentation

## Scope and result

Reviewed the mathematical sections of
`incoming/ipra_guarded_source_2026-11-11/ipra_guarded_source_2026-11-11/report.tex`,
the complete inherited `guarded_core.tex` and
`zero_source_admissibility.tex`, and the ordinary interpretation bridge.
Also checked the computation-supply argument in
`inherited_arity_checker.tex` against the source restriction.

No critical mathematical gap was found in the reported equational
dependency theorem, mixed auxiliary reading, or public formula-composite
argument. This is an independent written review, not a Lean/Rocq
formalization or a universal executable proof-checker audit.

## Dependency order that must be preserved

1. In the auxiliary calculus, equation induction is derived directly from
   atomic DI, DE, and anchored QE, with an unused existential coordinate.
   This uses arbitrary, potentially unguarded equation matrices.
2. In the equation-only restricted-source fragment, equation cases follow
   from equation induction with an unused induction hypothesis.
3. Computation and permitted transport supply reflexivity, safe symmetry
   and congruence, and the represented-zero joining lemma.
4. The unconditional singleton test and zero filter are proved by equation
   cases. Their arbitrary targets are obtained from the derived case rule,
   not by indiscriminately substituting into restricted proofs.
5. Under a fixed assumption `0=t`, one induction on
   `n=I(n,t;u.Su)` proves `1=St`. The singleton test and filter yield `t=0`.
6. Full numerical equality follows. Only then is canonical formula transport
   recovered by structural induction on the public formula template.
7. The inherited unrestricted guarded calculus embeds in the restricted
   auxiliary calculus on public sequents. Auxiliary soundness and agreement
   of readings give the reverse public translation through iPRA.

This order avoids dependence on logical case introduction during the
restricted equality bootstrap.

## Restricted substitution: important distinction

The restriction is syntactic: the left side of a primitive transport major
must not be the literal one-node term `0`. A variable source is permitted
even when its interpreted value is zero.

Arbitrary substitution is not verified by a direct induction on restricted
derivations: replacing a variable source by literal zero changes a permitted
rule instance into a forbidden one. The inherited proof does not require
that invalid direct argument. It uses only:

- weakening, cut, and fresh renaming, which preserve the source condition;
- source-preserving substitution when all affected sources retain an `I`
  or `S` head;
- an induction or equation-case rule at the desired arbitrary target.

The variable source in the step proving `n=I(n,t;u.Su)` remains the fresh
induction variable. The proof does not subsequently substitute zero into
that primitive source. Induction is applied directly at target `1`.

The inherited guarded calculus G has unrestricted transport. Its own
equation-induction derivation legitimately specializes an arbitrary supplied
step proof at `0` and `Sw`. That derivation must not be copied directly into
the restricted calculus before equality has been repaired. The actual
composition avoids this issue by deriving equation induction in the larger
auxiliary calculus first.

## Mixed reading and the public language

For auxiliary formulas, the sound interpretation is:

- equality is actual equality;
- Q is the anchored closure `B(0) -> forall y B(y)`;
- D with an equation matrix E means
  `exists x forall y (E(x,y) -> E(x,Sy))`;
- D with a compound matrix means
  `exists x (B*(x,0) -> forall y B*(x,y))`.

The interpretation is syntax-sensitive, but numerical substitution preserves
the equation/compound distinction. Restricted equality transport is therefore
sound under it. At atomic DE, iPRA's equation induction converts the progressive
property to the anchored Q resource that the rule exports.

For a public guarded atomic matrix

    E(x,y) = [I(y,0;u.h) = I(y,0;u.k)],

the base E(x,0) is a theorem even when h,k depend on x,y,u. Thus progressive
and anchored readings are provably equivalent. Structural induction extends
agreement to every public formula.

There is no such equivalence for unrestricted auxiliary atomic D formulas.
For example, a predicate true at 1 but false at 0 and 2 has vacuously true
anchored closure and false progressive closure. The report must not claim
that the entire auxiliary syntax is complete or bi-interpretable under a
uniform anchored reading. The exact theorem concerns canonical public
contexts and conclusions, with broader intermediate proofs.

## Canonical transport and clause contexts

The structural transport proof is sound in both branches:

- With a guarded equation matrix, compute its true source base, use the
  opened source Q resource at the successor target, transport that equation,
  and introduce the target D while ignoring its induction hypothesis.
- With a compound matrix, transport the target's local base backwards,
  use the opened source Q resource, and transport the successor conclusion
  forwards. Both recursive calls concern the smaller canonical matrix.

The inherited guarded calculus uses clauses rather than first-class Q
formulas. On proofs beginning with public formula contexts, the relevant
clauses are constant clauses representing assumptions and anchored clauses
introduced by DE. Constant-clause uses translate to hypotheses; anchored
uses translate to Q elimination. The comparison does not identify arbitrary
external clause contexts with arbitrary Q contexts.

## Both composites, not just consistency

The guarded padding translation is the identity on equations and uses

    T(D B) = D P(TB),
    P(E) = D_{u,v} [C(v,0,s)=C(v,0,t)]  when E is s=t,

with P the identity on compound formulas. It sends every paired matrix to
a compound one. The old and new formula composites are established by
padding equivalence, compound binder congruence, and the guarded atomic
composite. The latter uses the true zero base essentially.

The exact public consequence theorem transfers these composite proofs to
the restricted auxiliary presentation. Terms, numerical domains and actual
equality are unchanged by the guarded/source stages. Composing with the
inherited scalar/iPRA bridge therefore retains the whole-domain identity
graph for both numerical composites.

## Computation-supply caveat

The inherited arity-codec lemma “supply with a known zero instance” is written
as a proof transformation using substitution in an unrestricted native
calculus. It cannot be imported verbatim as a restricted-proof transformation.
For soundness of the restricted implementation, first translate the
continuation to ordinary iPRA. Substitute zero for all newly admitted fresh
parameters there, where substitution is available, and cut the ordinary
computation zero-instance there. The guarded-source report explicitly makes
this repair. It should be retained in the new report.

Completeness of computation packets with syntactic zero restrictions uses
the represented zero

    c0 = I(2,1;u.0),   c0=0.

Replace the offending predecessor/initializer zeros by c0 to obtain an
admitted computation, then transport its equation template along c0=0.
The only repair source is the nonempty term c0, so there is no zero-source
bootstrap cycle.

## Claims to retain and claims to avoid

- Retain the canonical-public-goal contract, or include and count the strict
  public grammar validator. Compact checker bytes do not include that validator.
- Retain the role of unguarded auxiliary equation induction. The reviewed
  proof does not establish completeness if every intermediate formula must
  itself be canonical guarded syntax.
- Distinguish the inherited written mathematics from current Lean results.
  The current composition and guarded translation were not newly formalized.
- If the new modules change only implementation spelling and preserve the
  same calculus, describe the gain as a smaller complete checker under the
  repository's metric. Do not present it as a new mathematical axiom deletion.
- The measured coordinate envelope may use different programs. It is not
  one program achieving all coordinate minima and is not a proved lower
  bound on all possible proof checkers.
