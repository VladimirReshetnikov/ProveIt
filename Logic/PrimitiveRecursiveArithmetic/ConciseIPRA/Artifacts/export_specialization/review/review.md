# Independent mathematical audit

## Scope and verdict

This audit compares the proposed newest-parameter specialization systems with
the raw five-family clause calculus and the fully normalized four-family
deterministic-Export calculus of the pinned article at ProveIt commit
`2fa4637b3bf922beea0052a5210c22b14482950b`.

Both proposed equivalences are correct with the hypotheses below. They remove
the supplied numerical target from conditional clause Use; Use at the fixed
numeral1 is not primitive either. They keep arbitrary atomic reflexivity and
arbitrary witnesses of Intro. A matched implementation must count its name
selector and scope handling. This audit establishes no global size record and
does not constitute a machine-checked Lean proof.

## Common setting

Scopes are finite ordered lists of distinct numerical parameters. The newest
parameter is denoted nu; in an empty scope use0, or omit Use there. The proofs
below do not require empty-scope Use because their simulated Uses always open
a fresh name. Every term and every free variable in a goal or clause belongs
to the current scope. Fresh eigenparameters are appended at the end.

Clauses have exactly one antecedent: `[A;y.B(y)]`. Ordinary assumptions are
`[0=0;y.F]`, with unused y. Refl is an arbitrary equation `t=t`. The new rule
Use_nu derives B(nu) from a proof of A and an occurrence `[A;y.B(y)]` in the
current context. A clause need not be the newest clause.

All substitutions are capture avoiding. Normalized systems normalize their
term substitutions according to the source's established coherent normalizer;
raw systems use ordinary substitution only.

## Fully normalized four-family system

Keep Refl, Intro, and the original deterministic Export. Its selector at fresh
b returns r if the normalized rows B(b,0) and B(b,1) are literally `0=0` and
`b=r`, respectively, and returns b otherwise. Export opens the clause
`[B(b,0);y.B(b,y)]`, proves F, and concludes the normalized F[r/b], provided
b is absent from this exported formula. Replacing arbitrary Use by Use_nu
gives four families.

Every target inference is an inference of the unrestricted normalized source:
Use_nu is the old Use at one permitted term, and the other three rules are
unchanged. This proves soundness without any appeal to a target Use at1.

For completeness, given a term t choose fresh x,z,u and define

    N_t = D_{x,z}(C(z,0,x)=C(z,0,t)).

Intro at witness t has normalized premise conclusion t=t, so Refl proves it
without using the introduced assumption. This works also at t literally0,
when Intro selects progress. Its selected rows at b are `0=0` and `b=t`.
Thus its deterministic Export selects t exactly.

For an old Use at t, open N_t at fresh newest b, reconstruct its antecedent
proof under that extension, apply Use_nu to the original clause to obtain
B(b), and Export B(b)[t/b]=B(t). The reconstruction is justified by the
strong induction statement below, not by naive target weakening.

## Raw five-family system

Keep raw Refl, the original two-case Eval, and arbitrary-witness Intro. Replace
Elim by the following deterministic raw Export, and Use by Use_nu.

The selected term is t when the major matrix is *literally* the raw name
shape `C(y,0,x)=C(y,0,t)`, where t contains none of the displayed bound
variables x,y or either selector's internal state variable. Otherwise select
b. This is an exact syntactic test, using alpha-stable names or de Bruijn
indices. It is not a test of provable equality. Independence of t from the
displayed binders must be checked by a decidable free-variable traversal or
equivalent structural support test in an implementation.

Raw Export has the same clause-opening and result-substitution form as above.
In the name case, the ordinary/native source calculus proves B(b,0) by zero
computation, uses the opened clause at1, and computes B(b,1) to b=t.
Equality transport and ordinary D elimination therefore derive Export's
conclusion. The source is unrestricted, so this soundness proof may use
source Use at1; it does not import that operation into the restricted target.
In the fallback case Export is simply ordinary Elim with a fresh conclusion.

The same name N_t is available directly in the raw target: Intro at witness
t has the literal raw equation

    C(Sw,0,t)=C(Sw,0,t)

as its premise conclusion. Refl proves this equation without computation or
normalization. Its selector chooses t. Hence arbitrary Use is reconstructed
exactly as in the normalized case.

Conversely, a source raw Elim is one target Export with its original goal F.
That F does not contain fresh b, so F[r/b]=F for either selector outcome.
The source Eval and Refl are unchanged. This gives the raw equivalence.

## Required strengthened induction

For **every unrestricted source derivation** of a clause sequent, prove:

> Under every injective renaming of its numerical parameters into any larger
> ordered target scope, and in every target context containing the renamed
> source clause occurrences, its renamed conclusion has a target derivation.

The target context may contain arbitrary additional clauses. The statement
is proved by induction on the source derivation. It is stronger than merely
translating the original end sequent.

At a source Use, the induction hypothesis for the antecedent is invoked in
the still larger context opened at the new alias b. That permits reconstructing
the antecedent derivation with b now newest. Its source tree is smaller, so
there is no circularity even though the resulting target derivation may grow.

At Intro, choose a fresh target eigenparameter z, append it, and translate the
source premise there with the newly added assumption. Injective renamings
preserve the equation/compound test and whether a witness is literally0.

At raw Elim, choose a fresh target b and translate the branch with the added
opened clause. Use Export as described above.

At normalized source Export, the selector commutes with injective renaming:
normalization is equivariant, and injectivity preserves and reflects both
literal row tests. The translated selected term is the renaming of the source
selected term. Normalization/substitution coherence therefore identifies the
exported conclusion with the renamed source conclusion.

No arbitrary term substitution is applied to a target proof. No local target
proof is simply reused after appending a parameter. No target cut theorem is
assumed. These facts prevent the familiar newest-parameter weakening gap.

The source and target consequently derive exactly the same open clause
sequents. Their ordinary readings are the same, so the source's established
whole-domain, actual-equality bi-interpretation with iPRA transfers by identity
on the object language. Equiconsistency follows as well. The proof is
schematic and effective, with finite target proofs for each finite source
proof; it does not assume a truth predicate or an internal universal evaluator.

## Boundaries and unproved stronger claims

1. **Keep arbitrary Refl.** Restricting a fixed reflexivity clause to newest
   Use gives only nu=nu directly. The name proof needs reflexivity at a general
   t (normalized) or at C(Sw,0,t) (raw). Deriving that reflexivity by naming t
   would be circular. This audit does not show completeness without Refl.
2. **Keep arbitrary Intro witnesses.** N_t is introduced at t. If Intro too
   were newest-only, this name proof would fail. An independent naming theorem
   would be required. It is not supplied by this argument.
3. **Keep arbitrary exported formulas.** The Use being simulated may have a
   compound body B. Restricting Export to equations alone invalidates the
   immediate argument and would need a separate rank induction.
4. **Check the exported support.** F itself may contain b, but F[r/b] must
   not. A rule that omits that check can leak an existential eigenparameter.
5. **The raw exact-shape check is real trusted work.** It must detect the
   advertised iterator counters, zero seeds, witness variable, and binder
   independence of t. Looking only at a pretty-printed resemblance is not a
   valid implementation.
6. **No broader novelty claim.** Names, deterministic Export, and restricted
   specialization each appear in prior packages. In particular Chapter6,
   `Fresh aliases and backward substitution`, already proves newest-only
   Use via a *primitive* Alias rule and a strengthened translation with
   arbitrary scopes/contexts (`alias_back` and `equation_aliases`). Therefore
   neither newest-only specialization nor its hereditary proof technique is
   new. The distinct statement here is the composition: the existing
   deterministic Export, applied to an introduced exact name packet, supplies
   the export capability needed to remove arbitrary Use without adding
   primitive Alias to this four-family (normalized) or five-family (raw)
   calculus. It is a refinement/corollary of prior ideas, not a claimed
   breakthrough or an independently new theory of naming.

## Novelty search

The consolidated Chapter6 has separate sections for the four-family
normalized inferred-Export calculus (lines755--946 in the downloaded source),
deterministic specialization with a special newest-clause-at1 case
(lines2200--2574), and primitive Alias/Back with newest-only Use
(lines2575--3425). The specific combination of deterministic Export with
newest-only Use does not appear in the inspected article or in the extracted
incoming TeX files. This is a scoped source comparison, not a claim about
the entire mathematical literature. The report should cite these direct
predecessors together so the limited extent of the refinement is clear.

## Optional generalized raw selector

A possible future variation recognizes
`I(y,0;u.x)=I(y,0;u.h(x,y,u))` and selects h(b,1,0). Its row0 and row1
computations prove soundness without an occurs check on h, even if the
selected term contains b, provided the exported result omits b. This variant
is not part of the exact-name implementation unless explicitly implemented
and tested. Its size may be better or worse than the support-checked selector.

## Implementation review

Reviewed `math_work/newest_use/checkers/reference.py`, `newest.py`, and the
untrusted bidirectional compiler `translate.py`. The checked implementation
is the **normalized four-family** version; no raw-five checker was reviewed.

The sole inference change in the matched pair is that Use has no target
field or target syntax-validation call and specializes at the inferred newest
parameter `-len(context)`. Both matched programs have primitive Refl.
Export validates its major formula, opens the fresh witness, computes both
selector rows, validates the branch formula in the larger scope, and compares
the normalized substituted result to a previously validated old-scope goal.
That last comparison enforces the exported freshness condition.

The selected right-hand side is a validated term at root depth, so it has no
loose positive bound indices. Inserting it below binders while replacing a
negative free parameter therefore needs no additional index lift; its own
internal binders remain local. The compiler correctly regenerates antecedent
proofs under enlarged contexts and carries a renaming/context-occurrence map.

I reran `python3 -B verify.py` under Python3.12.14: all nine closed fixtures
passed source-to-target-to-source checks and standalone checker execution;
five open targets, a nontrivial scope renaming/context embedding, and thirteen
negative controls passed. I additionally ran a compound-body capture test
whose clause body is a D formula containing an iterator and whose target is
the neutral iterator `I(v,0;u.Su)` with an internal bound variable; the
candidate and reverse compiler accepted the properly scoped result.

Measured matched sizes are 669tokens/754ASTnodes/2117normalizedbytes for the
reference and 663/748/2093 for the candidate. This is a modest matched
reduction, not a new corpus-wide minimum.

The programs tie scope allocation to context extension (`fresh=-len(g)-1`),
with one fresh numerical parameter per added clause. The public entry point
checks closed theorems. The executable open-context tests use compatible
encodings; the scripts are not a general independent explicit-scope API.
The mathematical theorem is stated with general scopes, while the closed
compiler uses this more economical allocation convention.

The verifier imports the local untrusted compiler, so run it without Python's
`-I` option unless its import path is explicitly configured. Its subprocesses
run the standalone checkers with `-I -S -B`; these need no local imports.

These finite checks supplement the written equivalence theorem. They are not
a formal verification of the entire normalizer/checker or the inherited iPRA
bi-interpretation.

## Follow-up: retained-reflexivity encoding and final report

The later `newest_reflexive_clause.py` keeps the inherited fixed reflexivity
clause at index0. A Use of that distinguished clause infers its target from
the validated equation goal; ordinary clause Uses select the newest parameter.
The ordinary clause argument is removed, but general reflexivity remains.

An initial implementation accidentally removed `syntax(t,fresh)` from Intro
as well as from Use. The parent caught this. I independently confirmed the
resulting validation failure: the true goal `D_{x,y}(0=0)` with proof
`['i',bad,['u',0,[]]]` was accepted for each invalid erased witness
`null`, `{}`, `'bad'`, the unavailable free level-1, and loose bound index1.
This is an invalid-certificate acceptance defect; those examples do not
claim an arithmetically false conclusion. The witness check was restored.

I reviewed the corrected diff against `reference_clause.py`: apart from
whitespace it changes only the Use packet and its target-selection code.
The restored checker rejects all five invalid erased witnesses above. The
full verifier was rerun successfully. Corrected sizes are
654tokens/731ASTnodes/2049normalizedbytes, against653/729/2058. Thus this
encoding saves nine bytes while using one more token and two more AST nodes.
The earlier2020-byte count belongs to the defective version and must not be
reported as a result. The explicit-Refl matched pair is unaffected.

The final report's four-family inventory, raw Eval rules, all-open-sequent
translation, and inherited bridge were checked. Its exact proof-node bound
`n+3u` is valid in the explicit-Refl convention: each source Use is replaced
by Export, Intro, Refl, and one restricted Use, with its antecedent proof
translated exactly once. Other source nodes are copied once. This is a node
bound only, with no bound on normalized term size or verification time.

For the membership-only-major obstruction, the precise variant must omit a
separate cut/lemma-retention rule. With such an added primitive rule, a derived
major could first be retained and then used by membership, undoing the intended
deletion. The report limits the claim to the direct deletion; making the
absence of the extra rule explicit strengthens its presentation.
