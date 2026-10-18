# Double-negation normalization of the exact SIR bundle

## Result and scope

For every one of the 64 masks in `original_layout_dne_variants.json`, the numerical calculus obtained by replacing the original fixed bundle with the indicated normalized bundle has **exactly the same derivable numerical codes** as the original calculus. This is a syntactic interderivability theorem, uniform in all natural-number parameters. It includes the cases in which a quantifier binds variable 0, the designated falsity code is also a relation code, parameters collide, or the implication constructor has the numerical alias `Imp(0,0)=0`.

The machine source must implement the corresponding new bundle constructor. Its AX input reads, GEN row, eight logical rows, output positions, gate and cleanup remain unchanged. The proof below supplies the new logical/enumerator bridge. Combining it with a complete compiler simulation and the exact blank-start frame for a resulting literal binary table gives the same ZFC consistency equivalence as the original source. An old/new source bisimulation that demands identical numerical registers is neither needed nor generally true.

No Lean build of this new transfer theorem is supplied here. The mathematical proof is explicit, and `check_dne_variants.py` independently checks the finite template/emission facts for all 64 masks. Complete binary coverage and bootstrap verification belong to each actual compiled candidate and must be reported separately.

ProveIt source basis: commit `6446ff5668307a2ac6aee1896037f0b792090389`. The exact formula specification is the attributed upstream `ZF/m254/tools/logic/spec.py` at commit `297ab8df7e5de329605c3875b4934643b371a5e3`, SHA-256 `7d96deff6994315b714579c74d10efeb65374694d476c802c727356e258578e9`.

## 1. Work with the actual numerical calculus

Put

\[
P(x,y)=\frac{(x+y)(x+y+1)}2+y,
\quad I(x,y)=4P(x,y),\quad R(x,y)=4P(x,y)+1,
\]
\[
Q_i A=4P(i,A)+2,\qquad E(x,y)=4P(x,y)+3,\qquad F=1.
\]

Use the abbreviations

\[
NA=I(A,F),\quad A\mathbin{\wedge_F}B=N I(A,NB),
\quad D_iA=NQ_iNA.
\]

These are functions on natural numbers. We do not assume they freely generate a syntax tree. In particular, `I(0,0)=0` and `R(0,0)=F` are genuine identities. Symbolic trees in the artifact describe expressions formed from these functions; every identity of derivability below survives arbitrary evaluation of their leaves.

Write `T ⊢ A` for a theorem predicate closed under the following common rules and rows:

* Modus ponens: from `A` and `I(A,B)`, infer `B`.
* Generalization: from `A`, infer `Q_i A`, for every natural `i`.
* The Łukasiewicz row
  \[
  \rho_8(a,b,c,u)=((c\to u)\to a)\to((a\to c)\to(b\to c)).
  \]
* The original falsity/quantifier row
  \[
  \rho_6(i,A)=(D_iQ_iA)\to A.
  \]
* Quantifier distribution
  \[
  \rho_2(i,A,B)=Q_i(A\to B)\to(Q_iA\to Q_iB).
  \]

Both the original and every normalized calculus contain this common core, without using either bundle as a premise.

### Lemma 1: full classical implication in the common core

The checked Łukasiewicz derivation supplies, uniformly in its arguments,

\[
K(A,B)=A\to(B\to A),
\]
\[
S(A,B,C)=(A\to(B\to C))\to((A\to B)\to(A\to C)),
\]
\[
\operatorname{Peirce}(A,B)=((A\to B)\to A)\to A.
\]

Only MP and instances of `rho8` occur in those derivations. The repository states this polymorphically for an arbitrary binary operation; injectivity of implication is not an assumption. See `Lukasiewicz.lean`, the theorems `k`, `s`, and `peirce`, and `Code254.lean`, `implicational` and `c254_classical`.

The common core also proves `F → A` for every natural `A`. To see this directly, fix `i=0` and abbreviate

\[
H=Q_0NQ_0A,\qquad X=D_0Q_0A=H\to F.
\]

An instance of K gives `F → (H → F)`, hence `F → X`. The row `rho6(0,A)` gives `X → A`. Transitivity of implication, derived from K and S, gives `F → A`. This is exactly the `Code254.c254_efq` proof; it uses neither IR, atomic vacuity, the CP/GIC bundle, nor a freshness condition.

### Lemma 2: both double-negation directions

For every natural `A`, the common core proves

\[
A\to NNA\qquad\hbox{and}\qquad NNA\to A.
\]

For the first direction, under assumptions `A` and `A→F`, MP yields `F`. Apply the propositional deduction theorem twice.

For the second, assume `NNA`. Under a further assumption `A→F`, MP yields `F`, and `F→A` yields `A`. Discharging the latter assumption gives `(A→F)→A`; Peirce gives `A`. Discharge `NNA`. These uses of the deduction theorem involve only MP and common-core theorems. Generalization is never applied to an undischarged assumption.

### Lemma 3: replacement in formula contexts

Let `A ≃ B` mean that both `A→B` and `B→A` are common-core theorems. Then `≃` is an equivalence relation and is preserved by the following context constructors:

\[
C[\,]\ ::=\ [\,]\mid I(C[\,],U)\mid I(U,C[\,])\mid Q_i C[\,].
\]

Implication congruence is propositional. For example, from `A'→A` and `B→B'`, assumptions `A→B` and `A'` produce `B'`; discharging gives `(A→B)→(A'→B')`. Reverse the two equivalences for the other direction.

For quantifier congruence, generalize the theorem `A→B` to obtain `Q_i(A→B)` and apply `rho2(i,A,B)`. This gives `Q_iA→Q_iB`. Repeat for the converse. There is no condition on `i`: this generalizes a theorem, including when `i=0` and the literal number `F=1` decodes as `R(0,0)`.

No selected rewrite occurs in a variable-label argument of `Q`, `R`, or `E`. Thus these context constructors cover every path used by the finite transformation.

### Why a purely semantic shortcut needs care

For an arbitrary propositional atom `f`, `((A→f)→f)` is equivalent to `A∨f`, rather than to `A`. Five selected redexes have an inner formula `A=Y→(Z→F)`; there `F→A` is a tautology even when F is arbitrary, so local semantic cancellation works. The remaining redex has a quantified inner formula. Moving from a free assumption `¬R(0,0)` through a binder of variable 0 would be invalid without further argument. Lemmas 1–3 avoid that issue completely: they derive the required equivalences in a bundle-independent numerical calculus and then apply GEN to proved implications. The full six-redex theorem is consequently stronger and cleaner than a claim restricted to the five locally absorbing redexes.

## 2. The exact source transformation

Let `beta(a,b,c)` denote the original expression

\[
\bigl(C(a,b,c)\wedge_F G(a,b,c)\bigr)
\wedge_F
\bigl((R(a,b)\to Q_cR(a,b))\wedge_F(E(a,b)\to Q_cE(a,b))\bigr).
\]

The exact C and G expressions are taken directly from the pinned `spec.py`, not reconstructed from an informal set-theory description. Here `c` remains both the supplied GIC matrix code and a variable-label parameter; its occurrences are not renamed or reinterpreted.

An address is a list of child numbers in the fully expanded constructor expression: child 1 is the first argument and child 2 is the second. The six original addresses are:

| Redex ID | Original address |
| --- | --- |
| 0 | `1,1,1,1,1,2` |
| 1 | `1,1,1,1,1,2,1,1,1,2,2,1,1,1,2` |
| 2 | `1,1,1,2` |
| 3 | `1,1,1,2,1,1,2` |
| 4 | `1,1,1,2,1,1,2,1,1,1,2,2,2,2,1,2` |
| 5 | `1,2` |

At a selected address replace `I(I(X,F),F)` by `X`. Addresses refer to the original expression throughout, so deleting an enclosing selected node does not accidentally select a different descendant. Mask `m` selects ID `j` when bit `j` of `m` is one. The recursive implementation transports the original addresses through a deletion.

Write `beta_m` for the result. Lemmas 2–3, by recursion on the fixed expression, give

\[
\vdash_{\rm core}\beta(a,b,c)\to\beta_m(a,b,c),
\quad
\vdash_{\rm core}\beta_m(a,b,c)\to\beta(a,b,c)
\tag{1}
\]

for every mask and every `a,b,c`. All parameter equalities are allowed in (1). The actual bundle-axiom gate remains `c≠a ∧ c≠b`.

Define `C_m` to have exactly the original truth rule, MP, GEN and eight rows, and the sole changed axiom rule

\[
c\ne a\ \land\ c\ne b\quad\Longrightarrow\quad C_m(\beta_m(a,b,c)).
\]

### Theorem 4: equality of the numerical theorem sets

For every natural `n` and every mask `m`,

\[
C_m(n)\ \longleftrightarrow\ C_{254}(n).
\tag{2}
\]

Induct on an original derivation to obtain the forward translation into the modified calculus. The truth, MP, GEN and eight-row cases are unchanged. In a bundle case, use the new bundle axiom with the same parameters and unchanged gate, followed by the common-core implication `beta_m→beta` from (1). The reverse translation is identical with the implication reversed. This replaces each changed axiom leaf by a finite derivation and preserves the conclusion code exactly.

This proves more than equiconsistency. In particular, every original CP/GIC/vacuity projection, every original native-formula adapter, and every original derivation of IR remains available in the new calculus, with the same numerical conclusion. There is no need to reprove set-theoretic calibration for a weakened schema or a changed variable convention: (2) returns directly to the original literal calculus.

## 3. Exact AX interface and source implementation

Use the original six boundary registers `(pl,np,t,S,d,h)`, where the scratch registers and axiom selector have been cleared. Every command begins with the unchanged fetch/read prefix. If `pl=0`, it selects candidate `np` and increments `np`; otherwise it decrements `pl` before unpairing. It decodes the selector and an additive field `x`, giving `d'=d+x`.

The three non-AX commands are unchanged:

* MP checks `I(t,d')=h`. Success sets `t=d'` and pushes zero onto `S`; failure sets `t=0`. Either branch clears `h`.
* DROP pushes the old `t` and sets `t=h`, retaining `h`.
* NIP halts exactly when the incoming `h=1`; otherwise it pops `(h,S)=unP(S)`.

For AX, the selector supplies `c`; put `a=d'`. Read the next field `y`, put `b=h+y`, and read the same fourth field `u` as before. Above the protected old stack tail, AX pushes, from bottom to top,

\[
t,\ Q_a h,\ \rho_8(a,b,c,u),\ \rho_7(a,b,c),\ \rho_6(a,b),\ \rho_5(a,b,c),
\]
\[
\rho_4(a,b,c),\ \rho_3(a,b,c),\ \rho_2(a,b,c),\ \rho_1(a,b).
\]

The new current formula is `beta_m(a,b,c)` if `c≠a,b`, and zero otherwise. Clear `d,h` and all scratch/selector registers. **Only the displayed current bundle value changes.**

The unchanged AX word prefix is `[166,121,180,176]`: push `a`, push the old cache, build its GEN row, then read the new `b`. The eight original rows follow in original push order. The only destructive `u` read remains inside the unchanged rho8 constructor. After the changed bundle, the original tail `[192,131,211,197,131]` applies the same gate and cleanup.

The independent symbolic checker establishes these facts for every mask:

1. The GEN prefix, eight complete row expressions and their order are literal matches to the pinned source.
2. The input reads are identical and occur at the same stack depths.
3. RPN execution never consumes the protected old current formula or the old stack tail.
4. The new constructor word leaves exactly one current formula above the same ten pushed outputs.
5. The bundle has outer constructor `I`, so its numerical code is divisible by four and is never `F=1`. Every pushed logical row also has outer `I`, except GEN, which has tag two; no pushed row is 1.
6. The gate and cleanup macros are byte-for-byte unchanged.

To lift this symbolic identity to a changed structured register program, apply the already proved scalar-push and binary-constructor contracts by induction on the emitted RPN word, followed by the unchanged gate/cleanup contracts. Each complete formula constructor is balanced: it leaves its value as current, restores its scratch and parameter registers, and pushes the previously current formula onto the protected tail. A binary constructor combines exactly the two fresh arguments; no new register operation is introduced. This is a compositional source lemma for the new program, not a comparison asserting that it emits the old numerical bundle.

The routed baseline's fine-token AST is not literally the old `Dag254.v` AST: previous optimizations commute independent increments and reassociate control nodes with corresponding continuation adjustments. A separate all-register macro bridge now checks **all 19 entries** of `macro_to_fine.json`. It independently builds finite control-flow graphs for the old macro and the composed fine word, compares the nine-register increment vectors between matching decrement guards, explores both branches, and verifies the resulting path equations again with the upstream path decoder. The certificate has **192 state pairs and 346 checked edges**. It preserves exact output registers and return/divergence behavior. See the neighboring machine-reduction artifacts `audit_macro_fine_bridge.py`, `macro-fine-bridge.json`, and `macro-fine-bridge-certificates.json`. Composing that bridge with the original macro contracts is the required justification for assigning original constructor meanings to the new fine words; the aggregate original AX word hash alone would not establish it.

The finite fine-token representation has these exact sizes:

| Mask | Deleted redexes | Constructor-expression nodes | Wade macro calls | Fine AX terminals |
| --- | ---: | ---: | ---: | ---: |
| 0 | 0 | 145 | 186 | 1,270 |
| 59 | 5, omitting ID 2 | 125 | 196 | 1,180 |
| 63 | 6 | 121 | 196 | 1,162 |

Every deleted redex removes 18 fine terminals and four constructor-expression nodes. It can increase the count of coarser Wade macro calls because an `And` or `Ex` pattern ceases to be recognizable as a single derived constructor. Consequently source size alone does not predict compressed state count.

## 4. Soundness and completeness of the changed enumerator

### Soundness from a safe start

Let `Good_m(S)` mean that every element obtained by repeatedly unpairing the logical stack is a theorem of `C_m`; the zero tail contributes the truth code 0. Preserve

\[
C_m(t)\ \land\ C_m(h)\ \land\ Good_m(S).
\tag{3}
\]

The ordinary command proof is unchanged. Successful MP follows by MP in `C_m`; failed MP and pushed dummy zeros use truth. DROP and NIP move previously proved codes. AX pushes GEN of the proved cache and eight unchanged logical axiom instances, and its current formula is either the gated new axiom or truth. Thus a halt, which is precisely an incoming cache value `F`, implies `C_m(F)`.

By (2), the sets of safe formula/stack contents for the original and new calculi are equal. At the actual baseline seed `(N,T,W,A,D,H,X,Y,L)=(3,0,0,0,3,0,0,0,0)`, all three formula-bearing fields are zero, so (3) holds. The nonzero candidate counter and additive parameter are not soundness assumptions about formulas.

### Completeness by explicit proof blocks

Use the original contract: a command list `Build(A)` started from `(t,S,d,h)=(T,S,0,0)` either halts, or ends at `(A,S,0,0)`, for arbitrary `T,S`. Earlier halting is an allowed successful outcome of this contract.

The unchanged stack row count and the tag facts above permit precisely the original proof-block construction. In the following notation AX `(c;x,y,u)` denotes selector `c+3` followed by the three data fields; every unprinted command field is zero.

| Derivation case | Command block |
| --- | --- |
| Discard / truth | `MP(1); AX(1;0,0,0); NIP^10` |
| Gated new bundle | `Discard; AX(c;a,b,0); NIP^10` |
| Logical row `rho_j`, `1≤j≤8` | `Discard; AX(c;a,b,u); NIP^j; DROP; NIP^(11-j)` |
| GEN `i` from `A` | `Build(A); DROP; NIP; AX(i;i,0,0); NIP^9; DROP; NIP; NIP` |
| MP to `B` from `A` and `A→B` | `Build(A); DROP; Build(A→B); NIP; DROP; NIP; MP(B); AX(B;0,0,0); NIP^10; DROP; NIP; NIP` |

The cleanup AX calls have `c=a`, so their bundle gate fails exactly as before. In the row selector the new current bundle may be pushed temporarily by DROP, but it is never 1, so the same NIP sequence restores the protected tail. The bundle-leaf case uses the new expression directly. Induction on a `C_m` derivation therefore gives the required block for every theorem code, including `F`.

### No refutation is lost by beginning with nextproof 3

The precise original safe-start proof is in `EnumSafeStart254.lean`, theorems `pad_code_ge`, `padded_program_halts`, `reach_ge`, and `complete_from`. It adapts without altering any command schedule.

Let `p` be a contradiction block. For every natural `u`, prepend

\[
\operatorname{AX}(0;1,1,u)
\]

and append `DROP;NIP;NIP`. The leading AX resets `d=h=0` from arbitrary working values. Its current output and its newly pushed stack may depend on those old values and on `u`, but the contract for `p` quantifies over both. Thus this padded program halts from every working state.

Its candidate code is at least `u`. Explicitly, if the encoded remaining command list is `r`, the leading code is

\[
P(3,P(1,P(1,P(u,r)))),
\]

with the usual successor convention included in `r`; every Cantor pairing is at least either argument. Pick `u` at least the initial next-candidate counter. Unchanged decrement-before-unpairing drains each current proof list, and every completed candidate increments that counter. Hence the padded refutation is eventually selected unless an earlier genuine halt occurs.

Consequently, from every start satisfying (3), and in particular the actual seed with nextproof 3,

\[
\operatorname{Halt}(\operatorname{Enum}_m)\quad\longleftrightarrow\quad C_m(F)
\quad\longleftrightarrow\quad C_{254}(F).
\tag{4}
\]

This argument does not assume that the earlier candidates 0, 1, or 2 are harmless, or that the current proof-list pointer is initially zero. It supplies the needed cofinality directly.

## 5. The exact CP/GIC and ZFC comparison

The inherited native theory has literal sealed sentences for the raw container axiom CP, global-image collection GIC for **every actual finite native formula with all parameters**, and raw irreflexivity IR. The upstream source names these compact axioms C and G; the source bundle also supplies atomic vacuity for the numerical calculus.

In ordinary set-theoretic notation their content is

\[
\forall p\,\exists V\Bigl(p\in V\ \land\
 \forall x\in V\,[x\subseteq V\ \land\ \exists W\in V\,\forall z\,(z\subseteq x\to z\in W)]\Bigr),
\]

and, for every formula `phi(x,y,parameters)`,

\[
\forall B\,\exists C\Bigl[
 \forall x\in B\,\forall y\,(\phi(x,y)\to\exists y'\,(\phi(x,y')\land y'\in C))
 \ \land\ \forall y\in C\,\exists x\,\phi(x,y)\Bigr].
\]

IR is `∀x ¬(x∈x)`. These expressions describe the already calibrated theory; the precise finite syntax and closures remain those of `NativeTheory254.NativeAx`.

The proved numerical/native interface is

\[
C_{254}(F)\quad\longleftrightarrow\quad
\operatorname{BProv}(\operatorname{NativeAx},[\,],\bot).
\tag{5}
\]

Equation (2) gives exactly the same interface for `C_m`, not just a semantic soundness implication. All formula families, gate conventions, equality transport, and falsity aliases are inherited through the equality of theorem sets.

The ordinary ZFC calibration may be composed as in the baseline proof: finite syntax and first-order completeness produce nonempty set-coded models; the native CP/GIC model has the relevant bisimulation quotient and internally well-founded interpretation; ZF including Foundation is compared with ZFC by the internal constructible interpretation. Internal Foundation must not be replaced by external well-foundedness of an arbitrary countable model. The native theory is also not obtained merely by deleting Choice from a displayed axiom list. Those are substantive inherited interpretation arguments, referenced below, and are unchanged by this transfer.

Within ZFC these are assertions about sets of finite proofs, satisfaction for set structures, and finite machine runs. Equations (1)–(4) are uniform finite derivation transformations and elementary inductions and can be carried out there. Combined with the established ordinary baseline interpretation, they yield

\[
\mathrm{ZFC}\vdash
\bigl(C_m(F)\leftrightarrow\neg\operatorname{Con}(\mathrm{ZFC})\bigr).
\tag{6}
\]

This is not an assertion that the new theorem has already been checked in Lean, nor that every universe-polymorphic Lean result automatically becomes a ZFC proof. The particular set constructions and inductions in the ordinary baseline calibration, followed by the explicit finite transformations here, are the mathematical reason for (6).

## 6. What is needed for an actual binary machine

For a literal compiled candidate `M_m`, the remaining implementation theorem has the following concrete premises:

1. The exact table has a complete positive-time simulation of every instruction of the **new** structured source, for arbitrary natural register values, all legal continuations, and the full tape frame. Both directions preserve genuine halting; neither a decode failure nor internal divergence is a halt.
2. The constructor/source lemma in Section 3 identifies that source with `Enum_m`, and unchanged control fragments preserve the original fetch, selector, reads and command semantics.
3. The exact blank trace reaches the documented root frame, with the actual head, header, logical register values, pointer stack, exterior tape, and physical spare suffix. In particular the formula-bearing logical fields satisfy (3).

These premises imply by simulation, (4), and (6)

\[
\mathrm{ZFC}\vdash
\bigl(\neg\operatorname{Halt}_{\rm blank}(M_m)
\leftrightarrow\operatorname{Con}(\mathrm{ZFC})\bigr).
\]

A complete instruction/compiler certificate plus bootstrap is sufficient **when it is a certificate for the new source and is composed with the new AX/enumerator lemma**. An audit of the old source alone does not identify changed AX outputs. No equality-of-registers bisimulation between the old and new source is required; equations (2) and (4) replace that unnecessary demand.

## 7. Provenance and novelty

The original compact calculus and set theory are due to Mira-Cult, the upstream verification to Jeff Ketchersid, and the machine compiler to Andrew James Wade. ProveIt's pinned numerical calculus, enumeration, safe-start and model adapters are inherited work.

Prior incoming material already uses rho6-derived ex falso and quantified double-negation transport in `verification/double_b6_review.md` to compare a changed quantifier row. The present contribution applies that method to the **six exact fixed-bundle redexes**, enumerates all 64 original-layout masks, supplies their exact fine-token emission, and explains the complete source/enumerator transfer needed to combine them with a new binary optimization. It does not claim the underlying double-negation principle as new.

Primary reference paths in the pinned ProveIt tree:

* `Computability/BusyBeaver/Research/ZFC/candidate-routing245/README.md` — literal baseline, count, seed, ordinary theorem and formal status.
* `Computability/BusyBeaver/Research/ZFC/native_theory254.md` — exact numerical/native refutation comparison and full native formula schema.
* `Computability/BusyBeaver/Research/ZFC/dirty_program254.md` — safe arbitrary control fields and structured source composition.
* `SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/code/35-dirty-formal-src-BusyBeaver-ZFC-Code254.lean` — numerical constructors, eight rows, exact bundle, `c254_efq`.
* The same source-35 prefix with `Lukasiewicz.lean` and `Kalmar.lean` — implication derivations and deduction/completeness, without injectivity assumptions.
* The same source-35 prefix with `Enum254.lean` and `EnumSafeStart254.lean` — complete command contracts and cofinal padding.
* `docs/incoming/sub246-audit-and-alternatives-20261018.zip`, `research_sub246/verification/double_b6_review.md` and `acceptance_checklist_and_transfer.md` — prior quantified DNE argument and ordinary ZFC model interpretation audit.

The `foundation_choice_route.md` note contains older intermediate Lean status and must not by itself be read as the final 245-state ordinary calibration status. The baseline README and complete incoming ordinary proof distinguish that status from the remaining exact Lean endpoint.
