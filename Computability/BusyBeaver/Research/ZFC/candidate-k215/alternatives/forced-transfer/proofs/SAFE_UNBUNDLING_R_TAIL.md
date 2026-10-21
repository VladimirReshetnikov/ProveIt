# Safe unbundling with cutoff R(a,b)=4P(a,b)+1

Date: 2026-10-21. Status: ordinary finite-refutation theorem, using the
accepted full-V logical comparison and seed-to-ZFC calibration. No new
machine/runtime claim or proof-assistant build.

## Exact emitted pair

Let K(a,b,k)=N(nks(a,b,k,k)), the positive complete support-bearing seed
core whose ACTUAL matrix code and private label are BOTH k. Let
V(a,b,c)=R(a,b)->Q_c R(a,b), and R(a,b)=4P(a,b)+1.

For every natural a,b,c, emit two independently usable heads:

    first: V(a,b,c) if c!=a,b, and truth0 otherwise;
    top:   K(a,b,k), where k=R(a,b)+c, UNCONDITIONALLY.

The old gate applies ONLY to the first V head. It must not reject,
replace, or accidentally test the transformed parameter for that head.
The original c is used in V; every matrix/private slot in K uses k.

THEOREM. This emitted theory, with the unchanged accepted logical
rows/rules, has effective finite-refutation transformations in both
directions with ZFC. The parameter coupling between the two heads does
not weaken their union, PROVIDED both heads are independently extractable
by the command compiler/proof enumerator. This theorem does not prove
that machine-side extraction/stack contract.

## Upper transformation: every emitted head is sound

Cantor pairing satisfies P(a,b)>=a,b, hence R(a,b)>max(a,b).
Therefore k=R(a,b)+c>max(a,b) for every natural c, including zero.
Every K head is an old enabled core with literal matrix/private code k.
The first head is either an old valid V instance or truth.

The accepted ordinary upper comparison validates the old bundle and its
V and positive-K components. Ordinary projection of a sound bundle is a
finite proof step in that comparison. Thus every emitted head has a
uniform finite ordinary/ZFC derivation. Numerical MP and GEN translate as
before, giving the upper finite-refutation transformation.

## Exact family coverage

Every original enabled V(a,b,d) is supplied by the call(a,b,c=d).
Every tail core K(a,b,k), k>=R(a,b), is supplied by the call
(a,b,c=k-R(a,b)). These may be DIFFERENT calls when the same binder k is
needed for V and K. No same-call identification of c with k is assumed.

In particular the first head's gate may fail in the call supplying a
particular K, but the K head remains emitted and sound. This is why the
stated unconditional top-head contract matters.

## Lower transformation at pinned roles1,3: no new padding is needed

The accepted Complete222 proof uses the ordinary named matrix

    q_phi = tr(source_names,phi),
    seed_matrix(phi) = Wn(Wn(q_phi)),
    seed_code(phi) = tau(th(seed_matrix(phi))).

Here th is the equality interpretation and tau is final native coding.
No public-role renaming is needed: retain the pinned roles(1,3).
Negation commutes with th and is encoded by N(x)=I(x,1), so, putting
m=tau(th(q_phi)), the ACTUAL seed code is

    k=N(N(m)).

For all natural x,

    N(x)=4P(x,1)=2(x+1)(x+2)+4 >= 8.

N is monotone on naturals, therefore

    k=N(N(m)) >= N(8)=184.

Meanwhile P(1,3)=13 and R(1,3)=53. Thus k>=184>53, and

    c_K=k-53 >=131

is a natural emitter parameter supplying exactly K(1,3,k).
A second call with c_V=k supplies exactly V(1,3,k), since k>3.

Let J=nks(1,3,k,k). From V and K=N(J)=J->F one derives the original
bundle N(V->J) by the implicational composition theorem

    V -> ((J->F) -> ((V->J)->F)).

This theorem is valid for an arbitrary F and requires no assumption that
native F is already an object-language falsum. It is derived from the
accepted propositional rows (or the inherited dominated-rho8 certificate).
Hence the split presentation derives exactly the named native bundle
that Complete222.Q_seed previously obtained as a single bundle axiom.

The rest of the pinned lower proof is unchanged:

1. Full original V remains available directly, so the accepted logical
   interpretation lprov_thm222, ordinary naming/equality interface, and
   finite natural-deduction translation remain available.
2. The original seed_code_fresh proof applies verbatim: k is computed
   after equality interpretation and double-negation padding; every
   matrix name required to be fresh is below k.
3. The original L_seed equivalence is applied INSIDE the ordinary
   interpreted comparison, normalizing the padded named matrix. We do
   NOT infer arbitrary native NN(m)<->m merely from positive rho8 or
   semantic model validity, and do not assume code-level alpha-conversion.
4. named_seed_to_seeded, seeded_core_to_kp0, and the accepted lower ZFC
   chain then apply to this reconstructed named bundle.

Thus each Q_seed use in a finite translated proof is replaced by two
head-extractions plus a fixed implicational derivation. Every other
proof replacement is inherited. The process is effective and formalizable
in the same metatheory as the accepted calibration.

Precisely, this is a mathematical replay with a NEW predicate thm_split
and Q_split(a):=thm_split(tau(th(a))). The existing Rocq lemmas are
hard-coded to thm222; this note does not claim they can be applied to
thm_split without transport or re-proving their counterparts. The
logical-interpretation proof is replayed using the directly supplied
full V, and Q_seed's former axiom invocation is replaced as above.
Pure formula identities and the arithmetic/freshness lemmas concern the
same unchanged codes. No proof-assistant compilation is claimed.

The theorem is equiconsistency/finite-refutation calibration, not identity
of native theorem sets. In particular it does not assert that every old
low-code K instance follows by a native alpha-conversion rule.

## General finite-cutoff form

More generally, retain every old fresh V and supply every enabled K at
fixed public roles(1,3) above any fixed natural cutoff B. Iterating the
ordinary double-negation padding before final coding makes the actual
code exceed max(B,3): each native NN step strictly increases its input.
A fixed number depending on B, for example B+4 rounds, gives a primitive-
recursive proof transformation. If a cutoff B(a,b) is specified by a
computable metatheory-provably total function, only B(1,3) is needed for
the lower argument. Upper validity requires every emitted private label
to differ from the public roles.

The present exact R-tail case is stronger and simpler: the EXISTING one
pair of negations already gives184, so the existing Complete222 matrix
and private code can be retained unchanged. No new padding theorem or
renaming lemma is required beyond the displayed arithmetic inequality.

## Machine-side obligations not discharged by this theorem

- Every original natural a,b,c tuple remains reachable by AX coverage.
- Both stack heads are independently extractable as axioms.
- The V head uses its original c and original freshness gate.
- The K head is unconditional and uses k=R(a,b)+c in all matrix/private
  occurrences, including nested shadowing positions.
- The two-output AX/reset/pop/index contracts are explicitly updated.
- Extra output is never treated as an unsafe, conditionally present head.

These are exact source/compiler conditions. If they are met, no logical
calibration gap remains for the stated unbundling.

## Independent review

The worker audit_r_tail_unbundling reviewed the completed argument and
reported PASS at the stated ordinary finite-refutation level on
2026-10-21. It checked the exact Q_seed coding, cutoff53 versus minimum184,
two-call coverage, pure implicational reconstruction, freshness,
noncircular full-V dependency, and all-natural upper soundness. Its note
SAFE_UNBUNDLING_R_TAIL_REVIEW.md preserves the explicit thm_split/Q_split
replay qualification. Compiler extraction and the two-output contracts
remain unverified by this theorem or review.
