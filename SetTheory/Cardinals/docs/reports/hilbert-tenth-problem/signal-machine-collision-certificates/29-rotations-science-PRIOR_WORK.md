# Bounded source comparison for the rational-rotation five-signal family

Checked 2026-10-04. This is a primary-source and connected-repository overlap check, not a proof audit, exhaustive novelty search, or priority certification. No repository program was executed, and no external state was written.

## Bottom line

No matching theorem was located in the inspected sources: for each fixed rational infinite-order planar rotation, an explicit finite, complete, rational-speed, number-preserving macro with exactly five live signals, together with the exact strict-guard infinite-return set and the positive-integer polynomial-sign obstruction.

The ingredients have substantial prior art. In particular, the dense-rotation obstruction to semialgebraic separation is already explicit in Fijalkow et al. (2017), beyond the sources named in the earlier audit. Conservative rational signal arithmetic and conservative shrinking are already explicit in Durand-Lose's AGC6 (2012). The potentially distinctive object is their exact five-live-signal physical realization with a complete collision word and exact return-domain analysis. Do not describe general rotation geometry, shrinking, bounded population, nonsemialgebraic linear-loop sets, or the dense-circle separation argument as new.

Interpret “fixed” per chosen rotation: the machine, finite rule table, and complete macro are fixed after the rational rotation is supplied. The check does not support a claim that one unchanged machine/table realizes every rational rotation.

## Primary sources

### 1. Becker et al., AGC8

Florent Becker, Mathieu Chapelle, Jérôme Durand-Lose, Vincent Levorato, and Maxime Senot, *Abstract Geometrical Computation 8: Small Machines, Accumulations & Rationality*, arXiv:1307.6468; journal publication J. Comput. System Sci. 97 (2018), 182–198.

- [Primary PDF](https://arxiv.org/pdf/1307.6468)
- [Author publication listing](https://www.univ-orleans.fr/lifo/membres/Jerome.Durand-Lose/Recherche/publications.html)

Checked Definition 1 and the definitions of n-speed machines and outgoing collision configurations (§2.1), introductory arithmetic (§2.2), and the accumulation/rationality scope. A meta-signal is a type, a signal is an instance, and speed count is a third quantity. Collision input and output sets have distinct speeds internally. Multiple outgoing strands can share a collision position. The paper's two/three/four-speed accumulation results do not certify a four-versus-five live-population boundary or the proposed rotation family. A text search for “five” in this PDF returned no hit; that is only a search observation.

### 2. Durand-Lose, AGC5: the apparent five-signal match is not a population match

Jérôme Durand-Lose, *Abstract Geometrical Computation 5: Embedding Computable Analysis*, Natural Computing 10(4) (2011), 1261–1273.

- [Primary author manuscript](https://www.univ-orleans.fr/lifo/membres/Jerome.Durand-Lose/Recherche/Publications/2011_NC_UC.pdf)

Checked §3.1, Figure 1, §4.2–4.3, and the concluding theorem. The signed-bit decoder uses five reference markers, plus the value marker e and an incoming get signal. Figure 1's basic rules include population changes 2→1, 2→3, 2→4, and 2→0. Its five-marker return pattern is therefore not an exactly-five-total-live number-preserving macro. Separately, the inner shrinking structure is described with five meta-signals and an additional start type; this is a type count, not the theorem's live-population claim. The paper establishes finite-signal real encodings, repeated halving, translations, and acceleration, but the inspected constructions do not present the proposed rational planar-rotation family or its strict-guard invariant set.

### 3. Durand-Lose, AGC6: closer conservative primitive precedent

Jérôme Durand-Lose, *Abstract Geometrical Computation 6: A Reversible, Conservative and Rational-Based Model for Black Hole Computation*, Int. J. Unconventional Computing 8(1) (2012), 33–46.

- [Primary author manuscript](https://www.univ-orleans.fr/lifo/membres/Jerome.Durand-Lose/Recherche/Publications/2012_IJUC_UC_HC.pdf)

Checked §§1–3 and 5–6, Figures 1–4. Here the conservative requirement explicitly equates incoming and outgoing signal counts. Rational stack push/pop is implemented through translation and scaling with two-to-two rules. Figure 4 already gives a rational conservative accumulator with two boundary strands and one alternating zigzag strand, using four meta-signals and two rules. The embedding construction scales a bounded computation by one half while preserving rational speeds and conservation. Thus neither conservative rational arithmetic nor conservative shrinking/Zeno acceleration is novel. No arbitrary rotation or exact strict-polyhedral return-domain theorem was located in these passages. The paper also explicitly separates ordinary evolution from semantics at accumulation points.

### 4. Dai–Xia: nonsemialgebraicity already occurs in three loop variables

Liyun Dai and Bican Xia, *Non-Termination Sets of Simple Linear Loops*, ICTAC 2012, LNCS 7521, 61–73; arXiv:1206.0232v1.

- [Versioned primary article](https://arxiv.org/html/1206.0232v1)
- DOI: 10.1007/978-3-642-32943-2_5

Checked §2, §3, and §4 Theorem 4.1 / Proposition 3. The nonsemialgebraic example is the three-variable homogeneous loop with update diag(2,3,5) and guard x1+2x2+x3≥0. It is a non-strict guard, despite the strict homogeneous convention used earlier for the two-variable algorithm. This precedes abstract three-dimensional linear-loop nonsemialgebraicity. It is not an irrational rotation example or a signal-machine realization. The claimed positive-integer agreement obstruction of the proposed family needs its separate rational-ray/eventual-sign argument; it does not follow merely by citing this real-set theorem.

### 5. Ouaknine–Worrell: rotation and the closed cone

Joël Ouaknine and James Worrell, *On Linear Recurrence Sequences and Loop Termination*, ACM SIGLOG News 2(2), April 2015.

- [Primary PDF](https://www.cs.ox.ac.uk/james.worrell/lrs5.pdf)

Checked §3, especially Example 3.1 on printed p. 7. The loop fixes z, rotates (x,y) by an angle irrational relative to π, and uses z−y≥0. Its nontermination set is the closed upper cone z≥sqrt(x²+y²). The displayed squared-cone formula in the paper must retain the nonnegative axial condition implied by the guard. Replacing ≥ with > changes the critical-circle behavior, so the closed-cone example does not settle the proposed exact boundary exclusions. This is a direct predecessor of the rotation/linear-guard setup, and an elementary strict-guard modification yields the single-tangency backward-orbit phenomenon. That last sentence is our mathematical comparison, not a claim that the source states the strict version.

### 6. Fijalkow et al.: dense-circle semialgebraic obstruction

Nathanaël Fijalkow, Pierre Ohlmann, Joël Ouaknine, Amaury Pouly, and James Worrell, *Semialgebraic Invariant Synthesis for the Kannan–Lipton Orbit Problem*, STACS 2017, Article 29, pp. 29:1–29:13.

- [Publisher record / DOI](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.STACS.2017.29)
- [Primary PDF](https://people.mpi-sws.org/~joel/publications/semialgebraic-invariants17.pdf)
- [Expanded author manuscript](https://people.mpi-sws.org/~joel/publications/complete-semialgebraic-invariants19.pdf)

Checked Example 1 and §3.3, Lemmas 10–11 / Corollary 12. Example 1 uses the rational rotation (1/5)[[4,−3],[3,4]]. An unreachable target on the closure circle may have no semialgebraic separating invariant. The general unit-modulus diagonalizable argument uses forward/backward orbit density and semialgebraic dimension/interior properties to force an invariant to include the orbit closure. This is a close precedent for the proposed separation mechanism. Their object is an inductive nonreachability invariant, not an arbitrary exact classifier of integer input gaps. No physical signal compilation is supplied. The matrix fixes the intended angle; the manuscript's printed arctan(3/5) description is inconsistent with it (the tangent is 3/4), without affecting the infinite-order rotation argument.

### 7. Recent bounded terminology check

Amir M. Ben-Amram, Samir Genaim, Joël Ouaknine, and James Worrell, *Termination Analysis of Linear-Constraint Programs*, arXiv:2509.06752v1 (2025).

- [Versioned primary PDF](https://arxiv.org/pdf/2509.06752v1)

Only a targeted check, not a full 126-page review: Remark 2.1, relevant nontermination-state discussion, and searches for rotation and Dai. Remark 2.1 uses non-strict inequalities by default and warns that strictness matters over real/rational state domains. The abstract semialgebraic potentially-nonterminating set used for existence decisions is not an exact classifier of all nonterminating starts. No match to the full proposed theorem was found by this limited check.

## Connected repository check

Repository discovery identified `VladimirReshetnikov/ProveIt`. Live connector search results were all pinned to commit `b64f24e591e7502ccc8b6dfa99c6dee1188e1155`; a separate read of the commit confirmed timestamp 2026-10-04T07:37:48Z.

- [Pinned commit](https://github.com/VladimirReshetnikov/ProveIt/commit/b64f24e591e7502ccc8b6dfa99c6dee1188e1155)
- [Collision geometry volume README](https://github.com/VladimirReshetnikov/ProveIt/blob/b64f24e591e7502ccc8b6dfa99c6dee1188e1155/SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/signal-machine-collision-certificates/README.md), fetched blob SHA `572efe05c7fb6c5d2c6da8009c0fa97d9f7060b1`
- [Finite-schema review](https://github.com/VladimirReshetnikov/ProveIt/blob/b64f24e591e7502ccc8b6dfa99c6dee1188e1155/Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/incoming_signal_review_808b.md), blob SHA `99dd820f2b1cec3d3bb7815a353b50f1ada72e0d`
- [Conservative frontend review](https://github.com/VladimirReshetnikov/ProveIt/blob/b64f24e591e7502ccc8b6dfa99c6dee1188e1155/Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/review_conservative_signal_2a8a39599.md), blob SHA `3f680635b6e80346eb43ddf96cf43dc4511d01b0`

These three files were fetched as inert text. The volume separates complete finite collision-schema certificates from an 18-live-signal conservative universal frontend. The review likewise confines its guarantees to fixed schemas, exact guards, and finite horizons; it explicitly disclaims chronology compression and post-accumulation semantics. These overlap with prerequisites, not the proposed fixed-five-live rotation family.

Queries: `signal rotation`, `non-semialgebraic`, `periodic collision`, `conservative stacks`, `five signals`, `rational rotation`, `nonsemialgebraic`, `complete macro`, `tangent orbit`, `five-live`, and `rotation` (top 100). Relevant matches led to the files above; other results concerned different rotation and macro topics. `non-semialgebraic` and `five-live` returned no hits. A general rotation search returned 100 ranked hits with no signal/collision path; this result is truncated and cannot establish absence. Search is default-branch and index-dependent, not an exhaustive tree/history/branch/attachment audit. Unindexed repositories were not searched exhaustively.

## Recommended claim boundary

Use: “We give an explicit five-live-signal realization, for each rational infinite-order planar rotation, with a fully specified complete macro and exact strict-guard return-domain analysis.” Say only that no matching realization was found in this bounded check.

Avoid: first nonsemialgebraic linear loop; first rational dense rotation obstruction; first conservative shrinking; first five-signal arithmetic structure; universal unchanged five-signal rotation table; general undecidability; any unrestricted lower bound or minimality claim; exclusion of integer-quantified Diophantine representations.

The integer-only result should explicitly concern finite Boolean polynomial-sign formulas with no quantified integer witnesses. Boundary-orbit distinctions, finite union of tangency orbits, multiple contacts, and the homogeneous-to-integer bridge still need the independent mathematical proof. The literature comparison does not supply that proof.
