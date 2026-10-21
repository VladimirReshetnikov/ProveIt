# Self-vacuity as a one-parameter classicality schema

## Result and scope

Let `C` be the exact native numerical calculus used by K218: the `C222`
rows, including unrestricted rho8, truth zero, MP, theorem-only GEN, merged
equality G, and the literal gated seed bundle. Replace only rho8 by

```
K(A,B)   = A → (B → A),
S(A,B,C) = (A → (B → C)) → ((A → B) → (A → C)),
SV(A)    = A → Q_A A.
```

The binder in SV is the natural number which is also the formula code A.
There is one numeric parameter, no substitution rule, no new freshness
test, and no separate choice of binder. Call the resulting calculus `CSV`.
Then the inherited numerical-calculus/ZFC calibration extends to give

```
ZFC proves:  Con(CSV) ↔ Con(ZFC).
```

The same result holds with `NN(SV(A))` in place of SV(A), where negation is
the exact native operation `N X = I(X,1)`. It also holds with the two-parameter
positive-introspection row `Q_i A → Q_i Q_i A` in place of SV; that variant
first recovers quantified double-negation elimination and then uses the
repository's existing `k218-quantifier-stability` proof.

The new finite certificate proves the **lower** syntactic direction:
K/S + SV recovers every unrestricted rho8 instance, so every C proof is
transformed into a CSV proof of the same native code. The reverse direction
uses the inherited decoded-theory interpretation and logical validity of
SV. It does **not** claim that the reduced native equality engine proves
every SV instance, or that C and CSV have identical sets of theorems.

This is a new calibrated formalism, not a smaller Turing machine. The direct
K218 source measurements below are larger than the current source.

## Exact native syntax and the zero alias

Put `P(x,y) = (x+y)(x+y+1)/2+y`, and use the exact operations

```
I(x,y) = 4 P(x,y),     R(x,y) = 4 P(x,y)+1,
Q(x,y) = 4 P(x,y)+2,   E(x,y) = 4 P(x,y)+3.
```

The falsity target is `F=1=R(0,0)`. Truth is the native code zero, and
`I(0,0)=0`. Use the exact Rocq decoder `D` imported by `Sound222.v`, not
an alternative decoder which reads every implication code literally.
Its zero value is the closed tautology

```
T0 = (forall 0 E(0,0)) → (forall 0 E(0,0)).
```

For positive n, unpair `floor(n/4)` to obtain x,y and use the tag
`n mod 4`. Tags 1,2,3 decode respectively as membership `R(x,y)`,
universal quantification `forall x D(y)`, and equality `E(x,y)`.
For tag 0, if y=1, the decoder produces primitive negation of D(x);
otherwise it produces `D(x)→D(y)`. The zero exception is taken before
this tag split. Thus native negation decodes literally as negation
(`D_wn`), while arbitrary native implication is related to ordinary
implication by `D_wim_E` in the comparison theory with irreflexivity.

Own-code freshness is inherited machinery: `Sound230.D_fr` proves that
every free label of D(n) is less than n, and `D_fr_self` proves
`fr n (D n) = false` for every n, including zero. `Sound222.V_bundle222`
already uses `D_fr_self` for the seed matrix. The contribution here is
the new classicality replacement using that freshness, not discovery of
the freshness property. The following slightly stronger bound also
follows directly from the exact decoder.

**Label-bound lemma.** If n>0, every label, including bound labels, occurring
in the resulting decoded formula is strictly less than n.

For any x,y, both x and y are at most P(x,y). If n>0 and
`(x,y)=unpair(floor(n/4))`, then

```
x,y ≤ floor(n/4) < n.
```

Proceed by strong induction on n. Membership and equality have only the
two labels x,y, so the displayed inequalities suffice. For a quantifier,
the binder is x<n and the body has code y<n. If y>0, use the induction
hypothesis; if y=0, T0 has only label 0<n, all its occurrences bound.
For an ordinary positive implication code, apply the same argument
separately to its two children. In the special negation case y=1, only
the child x<n is decoded, and the same argument applies. The impossible
circular case at zero is never recursed into: zero was handled explicitly.
In particular, label n does not occur in the decoding of any positive
code n.

Consequently, for n>0, decoded SV(n) is the logically valid formula
`D(n) → forall n D(n)`, with a binder absent even among bound labels.
At n=0, D(0)=T0 is closed, so the same vacuity argument applies. The
outer SV implication is positive even at n=0, and its right operand
Q(n,n) has tag 2 and therefore is neither 0 nor 1. Thus `D_wim` and
`D_wal` decode it literally as the displayed implication, with neither
exceptional branch. Equivalently, `D_fr_self` directly supplies the
freshness hypothesis for ordinary logical vacuity. By `D_wn`, weak SV
decodes literally as the double negation of this valid formula and is
also logically valid.

This argument concerns native codes, not a new syntactic substitution
convention. It remains valid for every natural number, including all
degenerate parameter coincidences and codes which other syntax conventions
would regard as junk.

## Recovering classicality from self-vacuity

The proof uses only K/S and three retained logical rows:

```
rho1(i,b):  Ex_i E(i,b),
rho2(i,X,Y): Q_i(X→Y) → (Q_i X → Q_i Y),
rho6(i,X): Ex_i(Q_i X) → X,
```

where `Ex_i X = N(Q_i(N X))`. In particular it does not inspect or alter
the seed core, its gates, G, membership transport, or quantifier commutation.
The following persistence lemma was already proved in the repository's
`k218-quantifier-stability/proof.md`; the new observation is its
code-dependent use with i=A.

**Persistence lemma.** If `NN(A→Q_i A)` is a closed theorem, then
`NN A→A` is a closed theorem.

First, K and rho6 prove explosion. K gives
`F→N(Q_i(N(Q_i A)))`, and rho6 finishes `F→A`. For any i, rho1(i,0),
theorem-only GEN, rho2, and explosion prove seriality `Q_i F→F`:
necessitate the closed theorem `F→N E(i,0)`, use normality, and combine
with `N(Q_i(N E(i,0)))`.

From the assumed closed double negation of persistence, intuitionistic
implicational reasoning gives the closed theorem

```
h': A → NN(Q_i A).
```

Indeed, A and `N(Q_i A)` would refute any implication `A→Q_i A`.
Necessitate this closed h' and use rho2 to obtain
`Q_i A→Q_i NN(Q_i A)`. Put `Z=Q_i N(Q_i A)`. Under Z and Q_i A, this
last implication and rho2 give Q_i F, hence F by seriality. Therefore
`Z→N(Q_i A)`. Combining this with h' gives `Z→NA`. It follows
intuitionistically that `NNA→NZ`. The exact rho6(i,A) instance is `NZ→A`.
This proves the lemma. Every temporary assumption is discharged using K/S;
GEN is applied only to already closed theorems.

Now instantiate the lemma at the natural binder i=A. An SV axiom gives its
double negation by intuitionistic double-negation introduction, hence
`NN A→A` for every A. If weak self-vacuity is the new row, its axiom is
already the lemma's premise. No induction on A is needed in this lower
direction; numerical aliases can only identify expressions in a valid
finite schematic proof.

To recover rho8 for arbitrary A,B,C,U, suppose
`h:(C→U)→A` and `k:A→C`. Under an additional NC, an assumed C yields F
and hence U, so C→U. Applying h and k yields C, contradicting NC.
Thus NNC and therefore C by the stability just proved. Weaken by B and
discharge k,h. The resulting closed formula is exactly

```
((C→U)→A) → ((A→C)→(B→C)).
```

This retains all four unrestricted parameters. It is not one of the
fourth-parameter restrictions excluded by the repository's HC countermodel.

## The two consistency implications, formalized inside ZFC

All inherited references in this section are pinned to ProveIt commit
`9adcaff0a72486ecc81242e0eca86e428c74879e`. Paths are relative to
`Computability/BusyBeaver/Research/ZFC/`.

The exact imported decoder and upper logical lemmas are also available
as pinned vendor sources elsewhere in the same repository:

- `SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/data/117-k226dp-vendor-k230-rocq-coq-settheory-KDecoder230.v`
  defines T0 and D, with `D_0`, `D_wim`, `D_wal`, and `D_wn`.
- `SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/data/117-k226dp-vendor-k230-rocq-coq-logic-Sound230.v`
  contains `D_wim_E`, `E_F`, `V_nF`, `D_fr`, and `D_fr_self`.

These two paths are relative to the repository root. Their statements
are inherited; no proof-assistant rebuild is claimed here.

For the direction from an inconsistent ZFC to an inconsistent CSV, use
`k225-formal/rocq224/src/Complete222.v`, theorem `thm222_complete`:

```
StandardZFC proves falsity  ⇒  C proves native code 1.
```

Replace each rho8 node in this native proof by the finite K/S/SV derivation
above, leave every retained axiom node unchanged, and preserve MP and GEN.
This gives a CSV proof of code 1. The construction acts on finite proof
objects and is recursive; its correctness is established by induction on
the original proof. Contraposition gives `Con(CSV)⇒Con(ZFC)` in ZFC.

For the other direction, the relevant inherited statement is stronger
than equiconsistency alone. In `k225-formal/rocq224/src/Sound222.v`,
`thm222_V` interprets each native derivation in the decoded K230 theory;
`V_bundle222` proves the **literal** seed bundles in that decoded theory,
including the original gates. The final argument passes through
`thm222_to_DecodedK230IR`, `decodedIR_to_KPrimeOrdIR`, and
`KPrimeOrdIR_standardZFC_inconsistent`. The latter two are imported
dependencies of Sound222; the numerical interpretation of native 1 is
membership of a variable in itself, contradicted by the retained IR axiom.

Repeat the induction defining `thm222_V` for CSV. Retained rows and the
literal bundle use the existing cases. Transport ordinary K and S
theorems through `D_wim_E` and its implication congruence. This equivalence
is established in the comparison theory **with IR**, not in pure logic:
the consequent-code-1 branch uses `E_F` and `V_nF`. For example, native
K(1,1) decodes to `FF→not FF`, where `FF=R(0,0)`, and IR supplies
`not FF`. The zero-alias branch is also handled by `D_wim_E`.
In contrast, decoded SV is itself a pure logical theorem by `D_fr_self`
and ordinary vacuity, or by the label-bound argument above. `D_wn`
also validates NN(SV) if that variant is chosen. These steps supply
the new interpretation cases. MP and GEN use exactly the old steps.
At target 1, repeat the existing IR argument and the same final two
refutation translations. Thus

```
CSV proves native code 1  ⇒  StandardZFC proves falsity.
```

This is an ordinary finite-proof interpretation, not an assertion of
external soundness. All new syntactic computations, label bounds, and
proof transformations are elementary recursive or obtained by induction
over finite codes/proofs, and their correctness is formalizable in ZFC.
The inherited translations provide the set-theoretic part. Taking the
contrapositive yields `Con(ZFC)⇒Con(CSV)`.

There is an equivalent model presentation if desired. The inherited upper
refutation translations imply, inside ZFC, that Con(ZFC) entails consistency
of the decoded K230+IR comparison theory. The ordinary completeness theorem,
formalizable in ZFC for this countable first-order theory, gives a nonempty
set-coded model of that comparison theory. Logical validity makes SV true
in that model, `D_wim_E` validates decoded K and S there, the old soundness
proof validates every retained native row, and IR makes target 1 false.
Induction on CSV proofs therefore establishes
Con(CSV). This does not require an externally well-founded model, a
transitive model, or an unconditional proof in ZFC that ZFC has a model.
The model-existence implication is conditional on Con(ZFC).

No new Rocq or Lean kernel check of these extended interpretation cases is
claimed. The finite lower derivations are executable and checked as follows.

## Finite proof artifact

Run `python3 check_self_vacuity.py` beside
`upstream_quantifier_checker.py`. The latter is an attributed, unchanged
copy of the repository's `k218-quantifier-stability/check_derivation.py`;
the former supplies the new schema constructors and endpoint derivations.
The run creates a 1,110-node proof DAG and a receipt. A separate serialized
rule reader checks every MP/GEN/axiom step, every dependency index, and the
open-assumption sets. It shares the axiom-formula definitions with the
builder; it is not an independent reimplementation of the axiom semantics.

There are five closed endpoints: positive and weak SV imply arbitrary
DNE; positive introspection implies quantified DNE; positive and weak SV
recover unrestricted rho8. The first, second, fourth and fifth endpoint
ancestries use only K, S, rho1, rho2, rho6, and their named SV schema. The
third uses introspection instead. Generalization never has an open
assumption. Numeric parameter A is allowed to occur both as a formula code
and a binder label; the proof syntax explicitly represents both uses.

The emitted proof file is `self_vacuity_proof_dag.json` (475,755 bytes),
SHA-256
`bc5dc3b13b2dcea285ee5865dd7be11ec69e8b660c78e7dd6daf7233c505cd9f`.
The finite checker does not establish the inherited set-theoretic bridge,
the mathematical strong-induction lemma, compiler coverage, or runtime
correctness. The ordinary arguments above cover the new logical obligations;
machine obligations have not been attempted for this alternative.

## Literal source measurements

The baseline is `candidate-k218/sites218.json`, SHA-256
`b0169f2d477d0584ac70f9bdb79c3a78ef2bc700d080b3cd80976210235b80d9`.
The measurement scripts replace the closed primitive interval [135,486),
which contains rho8 and its extra fourth-field reader, by K/S and the new
row. They try independent parameter permutations, six output orders, and
three fixed association shapes, deduplicating to 1,944 source layouts per
SV variant. Existing arithmetic and interval CFG resolvers agree on each
saved best source. There is no claim that this finite set exhausts possible
shared grammars.

| Source | Distinct source subtrees | Primitive occurrences | Maximum zero run |
|---|---:|---:|---:|
| Existing K218 | 205 | 4,744 | 6 |
| K + SV + S | 212 | 5,003 | 6 |
| K + NN(SV) + S | 214 | 5,097 | 6 |

The best positive source emits K, SV, S in that order; its SV postfix word
is `a a a Q I`. Saved sources are `sites_KSSV.json` and
`sites_KSNNSV.json`, with the full receipt in
`self_vacuity_measurements.json`. They emit two more axiom rows than the
old source. Source subtree counts are not working-state counts. Neither
alternative has a compiled, runtime-certified binary table or a startup
certificate, and neither improves the current source by this measurement.

The conceptual benefit is that a single formula's own numeric code gives a
fresh binder for free: one-parameter persistence suffices for all classical
reasoning in the presence of the retained existential and quantifier rows.
Any practical size benefit will require a different emitter or stronger
global source sharing than the direct replacement measured here.
