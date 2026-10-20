# Formalism and arithmetic-code investigation below K220

## Verified starting point and attribution

The seed-K calculus is described in ProveIt's `Codes222.v`, `Thm222.v`, and `Complete222.v`, at repository commit `9288593a769fa85adeebd2b505edf5c16728ce8f`. The final ordinary-formula theorem in the latter is `thm222_iff_standardZFC`. The K221 and delivered K220 layouts preserve the underlying seed-K primitive program. The existing K220 package already contains the general fresh-binder theorem and detailed countermodels against several axiom deletions. Those inherited results are not claimed as new here.

Primary references:

- [Complete222.v](https://github.com/VladimirReshetnikov/ProveIt/blob/9288593a769fa85adeebd2b505edf5c16728ce8f/Computability/BusyBeaver/Research/ZFC/k225-formal/rocq224/src/Complete222.v)
- [Codes222.v](https://github.com/VladimirReshetnikov/ProveIt/blob/9288593a769fa85adeebd2b505edf5c16728ce8f/Computability/BusyBeaver/Research/ZFC/k225-formal/rocq224/src/Codes222.v)
- [KPrimeCore.v](https://github.com/elliotglazer/k230-rocq/blob/main/coq/settheory/KPrimeCore.v)
- [KCode230.v](https://github.com/elliotglazer/k230-rocq/blob/main/coq/settheory/KCode230.v)

## 1. A wider family of arithmetically shorter fresh labels

Let `P(a,b)=(a+b)(a+b+1)/2+b`. The equality row is

`G_k(a,b,c) = E(c,a) -> (E(c,b) -> All_{k(a,b)} E(a,b))`.

The inherited general-binder calibration permits any total arithmetic builder k with `k(a,b)` different from both endpoint labels whenever `a!=b`. The diagonal case need not be fresh. The reason is precise: the merged row first recovers reflexivity and the canonical equality helper, and the equality-as-membership-indiscernibility interpretation uses this helper only off the diagonal; diagonal interpreted equality is a logical theorem. The code/private-label freshness for K must still be handled after translating its matrix, as in the inherited calibration.

For the scaled-pair family `k(a,b)=m P(a,b)+d`, with integer `m>=1,d>=0`, the exact criterion for uniform off-diagonal freshness is

`m>=2 or d>=1`.

Proof: `P(a,b)>=a,b`. If `d>=1`, freshness follows strictly. If `m>=2`, an off-diagonal pair has positive P, so `mP>P>=max(a,b)`. Conversely at `(a,b)=(1,0)`, `P(1,0)=1`, so `m=1,d=0` collides with endpoint a. For freshness also on the diagonal, the only additional excluded case in this family is `d=0,a=b=0`.

An even smaller numerical builder is

`k_sum(a,b)=a+b+1`.

It is strictly larger than both endpoints for every natural pair. Its arithmetic program can be built entirely from pre-existing closed source fragments: push parameter a onto the formula stack, add parameter b into the top register using the existing copy-preserving loop, and increment once. Thus it avoids the intermediate pairing operation. This is a valid logical alternative, not an assumption that smaller code values imply fewer machine states.

## 2. Measured decoder cost

The current G binder is the 80-primitive source block at ordinals 650 through 729, path `1110100100111000010`. Its literal arithmetic function is `4P(a,b)+1`.

Replacing it by `a+b+1` uses 34 primitives and cuts the complete program from 4,744 to 4,698 primitive occurrences. Nevertheless each of four tested argument-order/association variants has 210 distinct source DAG nodes rather than 208. The original exploratory incremental compiler reported 223 states for all four variants, but that compiler can overwrite rows also used by arithmetic helpers. Those numbers were therefore not validated machine constructions. The corrected, protected-helper hardware objective independently gives a lower bound of 223 for all four sum variants; see `binder_hardware_receipt.json`. A lower bound is a search rejection criterion, not an accepted table or an unbounded runtime theorem. The released baseline evaluates to 220 under the same objective.

`binder_search.py` also considered scaled-pair constructors by changing the final accumulation loop of the existing implication constructor, with m from 1 through 8 and d from 0 through 4, and both argument orders. Invalid m=1,d=0 was excluded. The bounded sharing screen retained 46 layouts with at most 211 distinct nodes and zero-run length at most seven. The corrected protected-helper objective rechecked all 46 retained layouts and gives minimum lower bound 220, achieved by the unchanged original binder. Historical literal tables under `binders/*/candidate.tm` are unvalidated exploratory outputs and must not be presented as candidate consistency machines. This is not an exhaustive lower bound over arithmetic label builders or source layouts. In particular layouts excluded by the node-count screen were not compiled.

The source shortening is real; the finite-control saving is absent in these layouts. Existing subtree reuse and contextual aliases dominate the cost of these already-small arithmetic expressions.

## 3. A larger sound contradiction target

The usual enumerator stops on theorem code 1, the atom `R(0,0)`. A mathematically equivalent target property is

`the produced theorem code is congruent to 1 modulo 4`.

Every such code has the form `R(a,b)`. In ordinary first-order logic, a theorem asserting membership between two free variable labels yields a diagonal membership theorem by universal generalization and specialization (if a=b it is already diagonal). This contradicts irreflexivity. More directly, the numerical soundness interpretation of `thm222` maps a proof of any such atom to a universally valid membership assertion in the calibrated K+IR theory, which cannot coexist with its irreflexivity axiom. Therefore existence of a proved membership atom implies inconsistency of StandardZFC. Conversely inconsistency produces a proof of code 1 by completeness, and 1 belongs to this residue class. These two proof transformations are finitary and formalizable in ZFC.

The analogous replacement by code 0 or code 3 is invalid: 0 is native truth and 3 is the reflexive equality atom `E(0,0)`. Both are derivable in the intended calculus. Code 2 is `All_0 Truth`, also a theorem.

A seven-leaf register program recognizes the valid residue-class target. With D decrementing register 5, put

```
A3=(D,Continue4)
A2=(D,A3)
A1=(D,(A2,Break1))
A0=(D,(A1,Halt)).
```

A0 halts exactly on inputs x=1 modulo 4, and otherwise returns with register 5 zero; its positive loop subtracts four. This is one leaf longer than the root's specialized exact-one comparison. Substitution in the current source produced 213 distinct DAG nodes and 4,739 primitive occurrences. The current incremental compiler did not have a direct leaf action for the newly introduced `Continue4` on its required edge, so it rejected the literal decoder allocation. No binary machine or state saving is claimed for this variant. The sound target family remains useful for a direct tape-level scanner or another compiler architecture.

## 4. Concrete new route used in this investigation

The seeded-program specialization is one concrete semantic route explored here. The new full countermodel below also settles a tempting but invalid formalism reduction, and the two-row implication basis supplies a genuinely equivalent alternative presentation. The independent certificate and all-natural halting-test proof are in `seed_specialization_proof.md`. They justify removing the general register-to-register equality comparison in favor of an exact-one test when its scratch register is certified zero. This changes the primitive source while preserving the seeded search semantics. It therefore offers a different source layout to the table optimizer without requiring a new consistency interpretation of K.

## 5. Further questions

1. Can the sum-binder block be scheduled jointly with the neighboring equality constructors so that its 46-instruction saving also reduces distinct decoder roles or increases aliases?
2. Can a direct tape-level residue test for a proved membership atom reuse existing engine states more effectively than the structured register implementation above?
3. Can relational abstract invariants identify further semantically dead comparisons or fixed scratch values that independent per-register value sets miss?
4. Can the seeded source-specialization theorem be reflected in Rocq so that future invariant-directed rewrites transport the compiled theorem mechanically?
5. Can the arithmetic emitter synthesize kappa and its source decomposition together, optimizing decoder-role count rather than numerical code size or primitive length?

## 6. A full countermodel rules out literal T and dual-B replacements

The separately supplied `t_replacement_countermodel.md` proves the following stronger result than the inherited relative modal countermodel:

**Theorem.** ZFC proves consistency of each of the two calculi obtained by literally replacing the seed-K row

\[
\rho_6:\qquad (\operatorname{Ex}_i\operatorname{All}_i A)\to A
\]

by either \(\operatorname{All}_iA\to A\) or
\(A\to\operatorname{All}_i\operatorname{Ex}_iA\), leaving the other native rows, the seed-K schema, native truth, MP, GEN, and irreflexivity unchanged.

The proof uses the set of hereditarily countable sets, \(D=H_{\omega_1}\), and two ordered times \(0\le1\). At time 0 membership is actual membership. At time 1 membership is actual membership enlarged by equality. Equality is actual identity at both times. Quantification ranges over both assignments and later times:

\[
(\operatorname{All}_i A)(t,v)
\quad\Longleftrightarrow\quad
\forall s\ge t\;\forall d\in D\; A(s,v[i:=d]).
\]

The distinguished native formula \(F=R(0,0)\) is false at time 0 and true at time 1. Implication is Boolean at each time. Consequently native negation \(A\to F\) becomes constantly true at time 1, and native existential quantification does too. This makes both proposed replacement rows valid while the original \(\rho_6\) and explosion \(F\to A\) can fail at time 1.

The substantial part is verifying the **literal seed-K schema**, including its variable-capture case \(a=b\), rather than only a normal modal fragment. At time 0 the schema reduces to a countable witness-closure requirement. An ambient choice function selects a witness for every supported matrix parameter. Starting with the required initial witness, close under the selected witnesses associated with countably many predecessors \(p\in z\cup\{z\}\). A countable union of countable subsets of \(H_{\omega_1}\) belongs to \(H_{\omega_1}\). The resulting set satisfies the literal seed condition. The complete reduction and the coincident-variable case are proved in the separate note.

Irreflexivity is also checked explicitly: \(R(a,a)\to F\) is true at both times. If irreflexivity is phrased as a rule from \(R(a,a)\) to \(F\), its premise is never globally valid, so it preserves global validity. Failed numerical gates emit native truth, code 0, which is valid. MP and GEN preserve validity at both times. Since \(F\) is not globally valid, it cannot be derived.

This theorem blocks an internal ZFC equivalence between either literal replacement's consistency and \(\operatorname{Con}(\mathrm{ZFC})\), provided ZFC is consistent. It does not say that a replacement supplemented by an independently calibrated explosion principle is invalid. That distinction motivates the next experiment.

The executable two-element reduction audit in `check_t_countermodel_reduction.py` checks 32,768 starting assignments across 2,048 configurations. It covers the four irreflexive relations on a two-element domain, all matrix truth tables at both times, and both \(a=b\) and \(a\ne b\). This finite audit checks algebraic expansion of the native code expression; it is supplementary evidence, not the infinite consistency proof.

## 7. Restoring explosion with a different propositional basis

A basis for classical implication and falsum can make the dual-B replacement legitimate. Once \(F\) has its classical falsum laws, Boolean contraposition turns

\[
\operatorname{Ex}_i\operatorname{All}_i A\to A
\]

into the corresponding dual-B schema, using renaming of the formula parameter. In the original nonexplosive Hilbert presentation, that conversion cannot be assumed; the countermodel above is the obstruction.

We tested the four-parameter single axiom A10 catalogued by Walsh and Fitelson,

\[
((p\to q)\to(r\to s))
\to
((s\to(r\to(r\to F)))\to(r\to p)).
\]

Its single occurrence of \(q\) can use the existing fourth-parameter stream reader. The screen tested six assignments of the other three formula parameters, the original \(\rho_6\) or six parameter assignments of dual B, and both first/last chunk insertion choices. The 168 layouts had best protected hardware lower bound **234**, with 218 source DAG nodes and 4,897 primitive occurrences. Thus this bounded screen supplies no smaller machine. The paper's assertion of completeness was adequate for rejecting these expensive layouts; no A10 proof transport into the repository's Rocq development was completed or claimed.

Primary source: Matthew Walsh and Branden Fitelson, [*Answers to Some Open Questions of Ulrich & Meredith*](https://fitelson.org/walsh.pdf), 26 June 2021. The exact Polish word used by the script is `CCCpqCrsCCsCrCrfCrp`; `a10_source_search.py` parses it independently before emission.

## 8. Eliminating the fourth formula parameter: a calibrated two-row basis

The native propositional row is

\[
L(a,b,c,u)=((c\to u)\to a)
\to((a\to c)\to(b\to c)).
\]

The code stream reader for \(u\) occupies 33 primitive occurrences at ordinals \([161,194)\). The whole native \(L\) emitter occupies \([135,486)\), or 351 occurrences. Replacing \(L\) with a classical basis using only \(a,b,c\) removes this reader and its fourth register role from that emitter.

### 8.1 A finite, explicit calibration

Let

\[
\begin{aligned}
G(p,q,r)&=((p\to q)\to p)\to(r\to p),\\
H(p,q,r)&=(p\to q)\to((q\to r)\to(p\to r)).
\end{aligned}
\]

**Theorem.** Under unrestricted schematic substitution and modus ponens, the two schemas \(G,H\) generate exactly the same implicational theorems as native \(L\).

For the direction \(G,H\vdash L\), the accompanying file `gh_to_l_explicit_certificate.json` is a 28-node derivation: two axiom nodes and 26 condensed-detachment nodes. The final node is exactly the native \(L\) schema up to a bijective renaming of its four variables. Every detachment carries explicit substitutions for both premises. The small checker `certify_gh.py` verifies homomorphic substitution, literal equality of the instantiated minor premise with the instantiated major antecedent, and equality of the consequent after canonical variable renaming. Its checker does not run unification or trust a search subsumption heuristic. `gh_to_l_audit.json` records PASS.

The first twelve nodes already recover identity, Peirce's law, and weakening \(p\to(q\to p)\), in addition to the axiom \(H\). They are also supplied in `small_basis_GH_certificate.json`. The full 28-node certificate avoids relying on an external completeness theorem for the converse direction.

For \(L\vdash G,H\), the repository's existing `CD222.v` derives weakening, Peirce, and \(H\) from \(L\). If \(X=((p\to q)\to p)\), Peirce supplies \(X\to p\), weakening supplies \(p\to(r\to p)\), and an instance of \(H\), followed by two applications of MP, supplies \(X\to(r\to p)\), which is \(G\). These are finite uniform proof transformations. Substituting numerical formula codes for schematic variables gives the native numerical derivations. Replacing the \(L\) axiom emitter by complete enumeration of \(G,H\) therefore preserves the consistency statement; no new set-theoretic interpretation is needed.

A related calibrated family uses

\[
G'(p,q,r)=r\to(((p\to q)\to p)\to p)
\]

together with \(H\). Its 15-node certificate `small_basis_GPxH_certificate.json` recovers the same three classical basis schemas. This is a proved alternative, not an unsupported assumption that permuting antecedents preserves completeness after removing \(L\).

### 8.2 Emitter result and exact scope

The \(G,H\) emitter uses nine implication constructors and eleven parameter pushes, versus six implication constructors, six existing parameter pushes, and the special reader in native \(L\). Although it removes an input field, it increases the complete program from 4,744 to 4,922 primitive occurrences. An AX operation emits one extra theorem code and consumes two stream fields instead of three. No additional dispatcher case is necessary: each formula push preserves the previously emitted theorem on the formula stack.

The enumeration argument must be updated for this changed AX format. The existing additive parameter choices still range independently over the three required formula codes. Each emitted result is an axiom instance and all instances are eventually covered. The stack invariant must count one additional theorem. These changes are conceptually routine but are not a completed Rocq or binary-runtime certificate for the exploratory layouts.

The completed first screen tested 432 layouts: 36 independent assignments of parameters to the two rows, both row orders, three token-boundary source parses, and both first/last insertion positions. Its best protected hardware lower bound is **226**, with 210 source DAG nodes and 4,922 primitive occurrences. The receipt and source are in `two_basis_variants/best_226/`. A separate chunk-preserving screen keeps the five original outer splice positions. It completed three prescribed parameter/order recipes, each with all 3,876 choices of four cuts in the 20-token macro word: **11,628 source layouts in total**. Their best protected lower bounds were respectively 226, 227, and 226. The receipt is `basis_chunk_variants/results.json`. Each segment uses one locally selected source parse; the cut search is exhaustive only within those three recipes and that parsing policy.

A final local screen retained the old fourth-parameter reader as the single occurrence of \(q\) in \(G(p,q,r)\) or \(G^{\prime}(p,q,r)\), while \(H\) retained its three register parameters. This is logically valid and restores the original AX stream format. Two reader decompositions were tested in 288 proposals each, for 576 proposals total. Both had best protected lower bound **225**, with 212 source DAG nodes and 4,929 primitive occurrences. Only one unmatched protected helper skeleton remained at that minimum. Retaining the reader therefore recovered some hardware sharing but did not produce a smaller machine. The receipts are in `retained_reader_variants/results.json` and `retained_reader_split_variants/results.json`.

For comparison, the established three-row basis consisting of weakening, Peirce, and \(H\) was screened over 216 layouts. Its best protected lower bound was **228**, with 212 DAG nodes and 5,001 primitive occurrences. The exact basis is also stated in F. Pfenning, [*Single Axioms in the Implicational Propositional Calculus*](https://www.cs.cmu.edu/~fp/papers/cade88.pdf), 1988.

### 8.3 Restricted native axioms and the modal possibility

Replacing \(u\) in native \(L\) by \(a,b,c,F\), or by \(a\to a,b\to b,c\to c\), does not come with a completeness proof. The bounded, proof-producing searches in `restricted_lukasiewicz.py` found no weakening/Peirce/syllogism calibration for these restrictions. Conditional runs with an additional explosion schema did not change that outcome. All six terms \(a\to b,a\to c,b\to a,b\to c,c\to a,c\to b\) were also tested as substitutes for \(u\); pure condensed detachment saturated at one or two schematic formulas under the stated size bound. These observations are search results, not impossibility theorems about the full seed-K calculus.

In particular, the retained quantifier rows may supply strength absent from a purely implicational search. `modal_g_detachment.py` therefore tests \(G\) together with a fixed binder's distribution row, native \(\rho_6\), native truth, and necessitation/GEN. Its formulas have a genuine unary \(Q\) constructor; they are not encoded as implications that could accidentally be detached. It validates every detachment and generalization step. At maximum formula size 101 and modal depth eight it reaches 172 schemas with no calibration of weakening, Peirce, or \(H\). The bound matters: this does not show that \(G\) alone is insufficient in the full retained theory. A positive finite derivation would remove the fourth reader while also shortening the propositional emitter from six implications to four, and remains a concrete open lead.

## 9. Exact logical symmetries and alternative numeric constructors

The companion `encoding_family_research.md` states the coding proofs and all measured bounds. The principal screens were:

| Family | Tested layouts | Best changed lower bound |
|:--|--:|--:|
| Pure antecedent exchange / parameter assignment / source parse in four retained rows | 480 | 225 |
| Global equality/membership converse and selected local equality reversals | 128, including baseline | 223 |
| Six permutations of fixed-length constructor tags, keeping membership tag 1 | 22 distinct edited layouts | 229 |
| Independent reversal of the Cantor-pair arguments for the four constructors | 16, including baseline | 239 |
| All ordered four-leaf binary suffix-code shapes and tag assignments, with membership code 1 | 163 distinct edited layouts from 30 code families | 256 among nonuniform-length families |

The unmodified baseline is 220 under the same protected-helper objective. These counts measure literal source-layout proposals while preserving required arithmetic helper rows. They are **not universal lower bounds** on the mathematical theories, coding families, or Turing machines. The local edit and parsing choices remain restricted. In particular, a whole-row closed splice can lose existing source-subtree sharing even when the emitted formula is unchanged; this is why the later five-chunk screen was added.

The experiments establish decodability and freshness for a broader family of constructor codes, and provide valid logical proof transports for several source changes. None of the completed theory-side screens in this note establishes a machine with 219 states or fewer.

## 10. Exact finite certificate for the two-row basis

The table below is the complete 28-node proof. `C` is prefix implication: `Cxy` means \(x\to y\). Letters are schematic formula variables, renamed independently on each line. A pair `(j,k)` denotes condensed detachment with line j as the major premise and line k as the minor premise. The supplied explicit-substitution JSON makes every instance concrete; the checker validates only substitution and syntactic modus ponens.

| Node | Formula in prefix notation | Justification |
|--:|:--|:--|
| 0 | `CCCpqpCrp` | G axiom |
| 1 | `CCpqCCqrCpr` | H axiom |
| 2 | `CpCqq` | (0,0) |
| 3 | `Cpp` | (2,0) |
| 4 | `CCCpqrCCCqsqr` | (1,0) |
| 5 | `CCCppqCrq` | (1,2) |
| 6 | `CCCCpqCrqsCCrps` | (1,1) |
| 7 | `CpCCCqrqq` | (0,4) |
| 8 | `CCCpqpp` | (7,0) |
| 9 | `CCpqCrCpq` | (6,5) |
| 10 | `CCCpqpCrCsp` | (4,9) |
| 11 | `CpCqp` | (8,10) |
| 12 | `CpCCCqrqq` | (11,8) |
| 13 | `CCCpqrCqr` | (1,11) |
| 14 | `CCCCCpqpprCsr` | (1,12) |
| 15 | `CCCCpqCrqsCCrps` | (1,1) |
| 16 | `CpCCpqCrq` | (13,1) |
| 17 | `CCCCpqCrqsCps` | (1,16) |
| 18 | `CCpCpqCpq` | (15,8) |
| 19 | `CCpCqrCqCpCsr` | (15,17) |
| 20 | `CCCCCpqpprr` | (18,14) |
| 21 | `CpCCpqq` | (17,18) |
| 22 | `CCCCpqqrCpr` | (1,21) |
| 23 | `CCpCCqrqCpq` | (15,20) |
| 24 | `CCpCqrCqCpr` | (15,22) |
| 25 | `CCCpqrCCrpp` | (15,23) |
| 26 | `CCpqCCCqrpq` | (24,25) |
| 27 | `CCCpqrCCrpCsp` | (19,26) |

Line 27 is \(((p\to q)\to r)\to((r\to p)\to(s\to p))\), the native four-parameter Łukasiewicz schema after renaming. The certificate therefore establishes the required direction without an appeal to semantic completeness.

## 11. Precisely open: T together with explicit explosion

A remaining proposal replaces the single native \(\rho_6\) row by the two schemas

\[
\operatorname{All}_iA\to A,
\qquad
F\to A.
\]

This is a different proposal from either literal replacement refuted by the hereditarily-countable countermodel. That model has \(F\) true at time 1 while some equality formulas are false there, so it fails the new explosion schema. It therefore does **not** settle the consistency strength of T plus explicit explosion.

At the schema level the proposed pair uses one fewer implication constructor and one fewer universal-quantifier constructor than the original row, at the cost of emitting an extra theorem. With the existing closed macros its straightforward word has 207 primitive occurrences versus the original row's 283. These are emitter-word lengths, not machine-state counts. No protected hardware allocation or consistency calibration was established for this proposal.

There is still a simple obstruction to recovering the original row from the other **logical** rows alone. Take times \(0<1\), domain \(D=\{0,1\}\), identity equality, and

\[
R_0=\varnothing,
\qquad R_1=\{(0,1)\}.
\]

Interpret implication classically at each time and interpret quantification by

\[
(\operatorname{All}_iA)(t,v)
\quad\Longleftrightarrow\quad
\forall s\ge t\;\forall d\in D\;A(s,v[i:=d]).
\]

Here \(F=R(0,0)\) is false at both times. Thus explosion is valid. T follows from reflexivity of the time order. Normal distribution, commuting quantifiers, the identity-based equality and congruence rows, existential equality, MP, and GEN are valid. Membership grows with time, so the positive fresh-variable membership-vacuity schema is valid as well. Both relations are irreflexive, so IR is valid.

Let \(A=R(0,1)\), fix an assignment with \(v(0)=0,v(1)=1\), and choose a fresh binder label \(i\). At time 0 the formula \(A\) is false. At time 1, \(\operatorname{All}_iA\) is true. Since \(F\) is false everywhere, the native existential is ordinary modal existence over a later time and an assignment value. Consequently \(\operatorname{Ex}_i\operatorname{All}_iA\) is true at time 0, and the original \(\rho_6\) implication fails there.

This finite structure is **not** a model of the seed-K schema. At the terminal time, choose the matrix \(\chi(y,p)\equiv E(y,p)\) and seed value 1. The schema's witness condition would require an object having 1 as a member, but no such object exists under \(R_1\). The relative countermodel therefore rules out a proof using only the other logical rows; it says nothing decisive about the extra strength of seed-K.

The complete T-plus-explosion calculus remains explicitly **uncalibrated** in this investigation. Its rows retain their intended first-order soundness. The missing direction is a proof that its full seed-K schema supplies enough strength to simulate contradiction proofs from the original calculus, or an interpretation establishing the same consistency strength. An equally decisive negative result would be a ZFC-constructible model of all its rows including seed-K. Neither has been supplied here. No positive equiconsistency or state-saving claim rests on this open proposal.
