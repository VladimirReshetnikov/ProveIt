# Actual C222 uniform alpha: atomic checkpoint first

Read-only proposal by `controller_certificate`, 26 October 2026, after root accepted the finite `ValidatorEindContext222` checkpoint. No proposed Lean source has been written or compiled. This note refines the earlier context-first outline and proposes two independently reviewable leaves.

## A. Smallest next leaf: ValidatorAtomicTransport222

Import only `ZFCinPA.ValidatorEindContext222`. Work over arbitrary internal `ORingStructure V` satisfying IΣ1. Reuse the actual CProv222 finite Kalmar interface, Eq_Eind, Eind_euclid, Eind_el_l/r, represented contexts, and unchanged syntax-only term-label interpreter. No old EqualityCore254, EqualityContext254, Alpha254 or semantic CProv254 result is imported.

Expose finite actual C222 certificates with no freshness, positivity or distinctness premises:

```
eind_refl a : CProv (Eind a a)
eind_symm a b : CProv (Eind a b → Eind b a)
eind_trans a b c : CProv (Eind a b → Eind b c → Eind a c)
eind_congr a a' b b' :
  CProv (Eind a a' → Eind b b' → Eind a b → Eind a' b')
rel_congr a a' b b' :
  CProv (Eind a a' → Eind b b' → wel a b → wel a' b')
```

Here and below arrows in displayed formulas abbreviate literal `wim`, and every CProv is the actual numeric-history predicate. Reflexivity is Eq_Eind applied to actual primitive reflexivity. Symmetry uses Eind_euclid with pivot a and the diagonal Eind(a,a); transitivity then follows with pivot b. Equality-atom congruence composes those three relations. Membership congruence first uses Eind_el_l to change the member and then Eind_el_r to change the container. These are finite deductions, not semantic equality identification; the numerical auxiliary binder need not be fresh relative to a third or fourth endpoint.

Define `EqUnder h p q := CProv(h → p → q) ∧ CProv(h → q → p)`. Its two directions deliberately share the same h. Add reflexive EqUnder and these typed interfaces:

```
term_eind_under {n u} (hu : IsSemiterm set n u)
    F B B' (hB : len B = n) :
  CProv (EC(B,B') → Eind (TermLabels.term F B u) (TermLabels.term F B' u))

atom_eq_under {n arity R terms} (hr : set.IsRel arity R)
    (ht : IsSemitermVec set arity n terms) F B B' s t
    (hB : len B = n) :
  EqUnder EC(B,B') (atom ?[F,B,s] arity R terms)
                    (atom ?[F,B',t] arity R terms)
```

`EC` abbreviates the accepted `eindContext`. The typed bound-variable case uses `i<n=len B` and the actual context projection. Free variables use the same free environment on both sides, including exact fallback1, followed by Eind reflexivity. The set language has no function symbols; the typed function case contradicts its literal false function predicate. No untyped claim about function fallback0 is made. The relation typing forces arity2 and R=0 or1, so vector lookups are justified. The atomic theorem does not itself need `len B'=n` because EC uses total right nth; the full uniform theorem below retains both lengths for the cross-body vacuity proof.

Finally expose the finite reverse-premise adapter, for arbitrary h and r:

```
CProv(h → Eind s t → r) → CProv(h → weq t s → r).
```

Its proof is the explicit chain `weq t s → Eind t s → Eind s t`, followed by the supplied body certificate. It never changes h to EC(B',B), assumes context symmetry, or derives Eind→weq. This adapter is the key reverse-quantifier dependency missing from a mere namespace substitution of the old alpha source.

Expected size: roughly 160–210 main lines and 45–55 focused checks. Checks should retain zero/repeated endpoints, actual auxiliary collision, typed free fallback1, both atom branches, fixed-context reverse direction and actual numeric C222 witness extraction. Freeze this leaf before implementing the uniform induction.

## B. Subsequent ValidatorEnvironmentAlpha222 interface

Import the newly accepted AtomicTransport222 only. Define literal stream predicates, over all internal indices:

```
StreamEnv s B  := ∀ k, Avoid (s + 2*k) B
StreamFree s F := ∀ k, FreeAvoid (s + 2*k) F
Apart s t     := ∀ i j, s + 2*i ≠ t + 2*j
FreshPair F B B' s t :=
  StreamFree s F ∧ StreamFree t F ∧
  StreamEnv s B ∧ StreamEnv s B' ∧
  StreamEnv t B ∧ StreamEnv t B' ∧ Apart s t
```

`Avoid z B` is bounded avoidance of all stored entries. `FreeAvoid z F` additionally includes z≠1. No positive or pairwise-distinct stored-label premise is added. Apart explicitly excludes coincident streams; neither parity nor disjointness follows silently from the numeric stream names. Same-stream identity, if wanted, is the separate reflexive theorem, not an application whose Apart premise is impossible.

The uniform target is exactly:

```
encode_eq_under [V satisfies IΣ2] {n p : V}
    (hp : IsSemiformula set n p) (F B B' s t : V)
    (hB : len B = n) (hB' : len B' = n)
    (hf : FreshPair F B B' s t) :
  EqUnder (EC(B,B')) (encode F B s p) (encode F B' t p).
```

Every parameter, source code and stack length is internal, not a standard natural or externally finite list. Source0 is malformed and is not assigned IsSemiformula; a separate malformed-source client can rewrite both encoder outputs to truth0. Valid source truth also outputs0 but has a different source code. Typed source falsum outputs1. No unbounded source-formula induction is asserted at IΣ1.

### Quantifier step under the same old context

For a body u typed at n+1 put

```
h = EC(B,B')
P = encode F (s∷B) (s+2) u
Q = encode F (t∷B') (t+2) u.
```

The induction hypothesis has both implications under exactly EC(s∷B,t∷B'). The accepted context discharge gives
`h → Eind s t → (P → Q)` and `h → Eind s t → (Q → P)`.

For forward ALL, precompose the first with weq(s,t)→Eind(s,t), then invoke actual all_relational at labels(s,t). Its four resources are:

1. Vac s h, from context vacuity using both s-stream stack guards at index0;
2. Vac s Q, from accepted encode_vac with right bound stack t∷B', its exact length n+1, s free avoidance, s≠t from Apart(0,0), and avoidance of all t+2+2k;
3. Vac t h, from the two t-stream stack guards;
4. Vac t(∀s P), from Vac t P and actual vac_all s.

For reverse ALL, keep h and the reverse body IH exactly unchanged. Precompose **weq(t,s)→Eind(t,s)→Eind(s,t)**, then invoke all_relational at labels(t,s), body(Q,P). Its four resources are Vac t h, Vac t P, Vac s h, and Vac s(∀t Q), the last from Vac s Q. There is no exchange of old stacks and no self-vacuity of either body.

Existentials use the exact encoded form `¬∀s¬P`, finite negation transport, the corresponding ALL result on negated bodies, and vac_neg of the same two cross-body resources. No informal bound-variable substitution is performed.

### Stream preservation and induction hierarchy

To push s,t and advance both streams by2, rewrite `(s+2)+2k = s+2(k+1)`. Avoidance of the same stream's old head follows from `2*(k+1)>0` in the internal arithmetic model. Avoidance of the other old head follows from Apart at (k+1,0) or (0,k+1); advancing Apart uses (i+1,j+1). The old finite stacks and free-vector fallback1 remain avoided by the original stream predicates. No inherited parity, order between s and t, or stored-label distinctness is required.

Use the explicit uniform invariant

```
P(p) := ∀ n F B B' s t,
  IsSemiformula set n p → len B=n → len B'=n →
  FreshPair F B B' s t →
  EqUnder EC(B,B') (encode F B s p) (encode F B' t p).
```

`len`, nth, the actual encoder and EC have fixed Δ1 function graphs; typed syntax is Δ1. Avoid/FreeAvoid are Δ1, so StreamEnv/StreamFree/Apart and FreshPair are Π1. Actual CProv is Σ1 and the conjunction of two proof-existence claims in EqUnder is Σ1. The six outer unbounded environment quantifiers give the advertised Π2 invariant; no Π1 or arbitrary-predicate induction claim is made. To use existing hierarchy closure APIs, lift CProv to Π2 and FreshPair to Σ2, then explicitly construct the Π2 graph of each implication and universal binder. Use `InductionOnHierarchy.order_induction_sigma Π 2` with this proved definability instance and explicit IΣ2. Each recursive call is to a source subformula with its checked strict numeric-code bound, exactly as exposed by IsSemiformula.case_iff.

Atomic cases use leaf A. Nrel uses finite negation transport. Truth/falsity use EqUnder reflexivity; and/or use literal encoder conjunction/implication formulas. Binder cases use the preceding resource accounting and the pushed FreshPair. At empty stacks, EC is actual truth0, so two modus-ponens steps discharge it and give unconditional alpha implications. Stream selection, source substitution/opening, arbitrary R2 proof translation, tagged-domain CP/GIC calibration, and HA provability remain later clients.

Expected second-leaf size after atomic factoring: roughly 280–320 main lines and 50–70 checks. This source-only outline is not authorization to implement it before review of A.

## Exact next cache plan

The fully read old `ValidatorEnvironmentAlpha254.lean` (346 lines, SHA `fc7d9701f11172b7c35160eb436d0e6ef6dd89c3037ef7081e6661d18799876c`) is a proof-structure guide only. Its primitive-weq atom congruence and context vacuity cannot be reused as semantic theorems. The actual new atomic proofs above replace that boundary.

The first leaf imports accepted Context222, so its closure is exactly **154 cached current sources, 117 Foundation modules, 505 recorded prerequisite artifacts, and 40 explicit external primary boundaries**. No added Foundation source/object is needed. A read-only fresh inventory of all these source/artifact pins is `research/c222-alpha222-cache-plan-20261026.json`, SHA `a9073746ac0cef236f51dd128a08ce7d6f15deeeb02adcfa27ba8f25c5f02b49`; it records 699 successful prerequisite hash observations and the repeated-modifier import graph. It has not created an overlay or run any compiler.

Context source is `828fdba014446b0094ac9ce130f71b5d16205e9ea0814ed752940a46eccb1de5`; its accepted root fresh primary is `/tmp/validator-eind-context222-root-peer-ml7gi848/lib/ZFCinPA/ValidatorEindContext222.olean`, SHA `5d3a5a6643d1f39df3f9e3f7032da780c95fd56821bfa528a2d8f3427bdad7a7`. The root record is `reviews/validator-eind-context222-root-replay/ROOT.json`, SHA `b3edf1c7915e66d33e4cc9eb973afe4c284d7f6b60d42d3d976d1188a0b84061`; the author replay is `a26fc0465cbeda971ffa8fcdda19fbb1b61168ee3681e406815b15416f78fa19`. Relevant actual dependencies remain Encoder222 `805d1028574b0cc6ab1466f34d82011a5a3a7ba54c047a9a3001fc2bcd1c97ed`, Vacuity222 `cd02e19ae31785ab5460b8af4e850687ef93c68feb84a1a29a0434872e2244e9`, Eind222 `09ee7d8f43c4bf35486043beb4cfa191ad29ca5891797f0b2919476c825025f3`, and RelationalCore222 `3246a40dae816446a560652ff334ad44026752e176e577328622b236855a47a9`.

After A is independently accepted, B would add only A's one source/primary object to this closure, giving 155 cached sources, unchanged117 Foundation and40 boundaries; that future A pin is intentionally not invented here. Before either authorized compilation, reauthenticate exact pins and use a new private overlay, `-M6000 -j1 -DElab.async=false`, no shared cache writes or Foundation build, and the512MiB reserve. Historical-vs-trace Foundation provenance and the explicit Aesop boundary retain the accepted distinctions.
