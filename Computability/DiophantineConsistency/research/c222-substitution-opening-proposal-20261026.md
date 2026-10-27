# Next actual C222 checkpoint: substitution and opening

Read-only proposal by `controller_certificate`, 26 October 2026, after root's independent acceptance of EnvironmentAlpha222. No Lean source was implemented or compiled for this audit. The accompanying cache plan rehashes current sources and candidate objects; it does not claim a new replay.

**Recommended first checkpoint:** `ValidatorEnvironmentSubstitution222` and focused checks, approximately 130–170 main lines plus 45–60 check lines. Prove exact simultaneous source substitution for the actual Eind encoder, then derive both source opening and existential instantiation as short clients. A separate stream-selection leaf can follow. This avoids importing the much larger `ModelCodedSpecialization` dependency solely to obtain repeated qVec opening vectors.

## Existing sources read and reusable boundary

I read all of Streams254 (138 lines), Substitution254 (156), Opening254 (203), Instantiation254 (190), the actual Encoder222 (186), and R2Quant (the full quantifier proofs). I read the relevant R2Main rule cases and the actual Foundation definitions of `subst`, `substs1`, `free`, and typed Π1 structural induction. Exact source pins are in the cache-plan JSON.

The entire Substitution254 leaf is syntax-only: its sole import is EnvironmentLabels254, and it contains no CProv theorem. Its reusable `Matches`, `term_labels_bShift`, `matches_qVec`, `term_labels_subst` and `vec_labels_subst` concern the unchanged term-label interpreter. These remain valid for the Eind encoder. Its theorem about the old formula encoder is **not** the new result and will not be used to infer it. The new proof must apply actual Encoder222 constructor equations at every formula case; equality atoms are numeric Eind expressions of the equal argument labels, not primitive-weq atoms.

Opening254's repeated-vector construction is unnecessary for the immediate source-rule endpoints. Foundation literally defines `substs1 L t p = subst L (t∷0) p` and `free L p = substs1 L (^&0) (shift L p)`. Accepted Encoder222 already proves `encode_shift` with the same bound stack and stream. General substitution plus that theorem gives depth-zero opening directly.

## First exact theorem and quantifier invariant

For an arbitrary internal model of IΣ1, use the existing syntax-only relation:

```text
Matches F B B' n w := ∀ i<n, TermLabels.term F B w.[i] = B'.[i].

encode_subst
  (hp : IsSemiformula set n p)
  (hw : IsSemitermVec set n m w)
  (he : Matches F B B' n w) :
  encode222 F B s (subst set w p) = encode222 F B' s p.
```

All n, m, p, w, F, B, B', s are internal. The vector has exactly n source slots containing terms typed at target depth m. Neither `len B=m` nor `len B'=n` is needed for this exact identity: bound lookup is total and `Matches` explicitly supplies every used source slot. This fact must not be confused with the length guards required by the later vacuity/alpha theorem. There is no FreshPair, label positivity, label distinctness, or CProv premise.

The invariant at typed source `(n,p)` universally quantifies `m,F,B,B',w,s`, assumes typed w and Matches, and asserts the numeric encoder equality. Its fixed represented functions have Δ1 graphs and the conclusion is equality, so the invariant is Π1. Use the existing `IsSemiformula.pi1_structural_induction` under **IΣ1**, with explicit definability. A new Π2/IΣ2 induction is unnecessary for this syntax checkpoint.

At either source binder, both depths increase: `(n,m)` becomes `(n+1,m+1)`. The replacement vector becomes `qVec set w`; both stacks receive the identical literal head s; the stream becomes s+2. The existing `matches_qVec hw he s` proves precisely this next relation, using typed term-bound-shift and the no-function property of the set language. Atom and negated-atom cases use the existing vector-label equality and the actual `Encoder222.atom`. No unfolding of a large closed term vector is needed.

Proposed short clients:

```text
encode_substs1
  (hp : IsSemiformula set 1 p) (ht : IsTerm set t) :
  encode222 F 0 s (substs1 set t p)
    = encode222 F (TermLabels.term F 0 t ∷ 0) s p.

encode_free (hp : IsSemiformula set 1 p) :
  encode222 (x∷F) 0 s (free set p)
    = encode222 F (x∷0) s p.

encode_all_opened (hp : IsSemiformula set 1 p) :
  encode222 F 0 x (^∀ p)
    = wal x (encode222 (x∷F) 0 (x+2) (free set p)).
```

The first is the singleton Matches relation, with arbitrary typed t, and does not require a separate proof that a depth-zero term is a free variable. The second applies substitution to `shift p`, obtains the label `freeLabel (x∷F) 0=x`, then uses `encode_shift` and `tail_cons`. An existential-opened identity follows from the literal `neg (wal x (neg body))` constructor; it is not a CProv existential-introduction theorem. Pair substitution, swapped bound slots and free-variable fallback1 can be included as small checks/clients if the main remains within the stated size.

Typed source0 is impossible; valid source truth and malformed0 both encode to0 but remain separate cases. No all-malformed substitution claim is proposed. Empty or short label stacks, repeated labels, x=0, and free fallback1 are legal for the numeric identity. Under a binder the exact same stream label is pushed on both sides, so auxiliary-label collisions in Eind cause no freshness problem for this equality of codes.

## Separate stream selection checkpoint

`ValidatorEnvironmentStreams222` would import accepted Alpha222 only, about 140 main lines plus checks. A fixed Σ0 graph defines the actual internal selector

```text
alternateStart bound seed :=
  if seed % 2 = 0 then 2*(bound+2)+1 else 2*(bound+2).
```

Using `nth_le`, prove it exceeds bound and1, avoids all labels in any stack/environment whose numeric code is ≤bound, and has the opposite parity from seed. The sum bound `F+B+B'` therefore supplies the new stream's free/stack resources. The original stream must still supply its own required avoidance; the selector cannot retroactively make an unsafe original stream safe.

The first actual-CProv client is `encode_formula_relabel`: for a typed depth-zero formula, `StreamFree s F` and `StreamFree t F` suffice to prove both implications between `encode222 F 0 s p` and `encode222 F 0 t p`. Opposite parity gives accepted Alpha directly. Equal parity uses the explicit opposite-parity intermediate stream and finite composition of the two actual CProv certificates. The useful overlapping case t=s+2 then follows; it must not be passed directly to Alpha's impossible `Apart s (s+2)` premise. This composition uses accepted **IΣ2** alpha but requires no new uniform induction. Do not silently generalize the empty-stack result to arbitrary contexts by assuming context symmetry/transitivity.

## Later interpreted transport and rule boundary

After the exact syntax leaf and Alpha are accepted, a small actual transport theorem is immediate:

```text
hp : IsSemiformula set n p; hw : IsSemitermVec set n m w;
he : Matches F B B' n w;
len B'=n; len B''=n; FreshPair F B' B'' s t
  ⇒ EqUnder (eindContext B' B'')
       (encode222 F B s (subst set w p)) (encode222 F B'' t p).
```

Rewrite by the new exact identity and apply accepted Alpha. This endpoint uses the existing **IΣ2** theorem; it does not identify Eind with primitive equality or change the outer context. Replacing exact Matches by arbitrary relational Matches would be a separate, larger statement and is not needed for this first leaf.

For the eventual actual source ALL/EXS rules, R2Quant is only a guide. Its parity-resolved layout is explicit: odd stored free labels (fallback1 odd), even binder stream, and fresh odd labels `x=2*(F+1)+1`, `w=x+2`, `u=w+2`. All old CProv254 and primitive-equality-context certificates must be replaced. The accepted same-context ALL adapter and actual `Eind_vac` provide the cross-body vacuity route. For EXS, singleton context introduction can start from `Eind w z`, and accepted `Eind_ex w z` supplies its existential witness. There is no need to assume primitive `vac_eq` or an implication Eind→weq. Numeric syntax identities above do not alone prove either quantified rule under an arbitrary sequent context. That next finite-rule checkpoint should be proposed and reviewed separately before the Π2/IΣ2 proof-derivation translation.

No CP/GIC, theory-axiom calibration, proof translation, or HA derivation is asserted here. The HA goal remains the endpoint; these are internal arithmetic prerequisites.

## Authenticated cache and bounded execution proposal

Audit record: `research/c222-substitution-opening-cache-plan-20261026.json`, SHA `16d3cbc7ac69f4386b9dd02cba242c98de51e79a6d0fc6cff4d029e7b9bb0c19` (relative to `Computability/DiophantineConsistency`). Its current-source import traversal includes repeated public/private/meta modifiers and implicit Init. Every selected source, artifact and external primary was rehashed without executing Lean or any incoming driver.

| Proposed import set | Cached sources | Foundation | Artifact records | External names |
|---|---:|---:|---:|---:|
| Alpha222 only, for stream client | 156 | 117 | 507 | 40 |
| Encoder222 plus syntax-only Substitution254 | 153 | 117 | 504 | 40 |
| Alpha222 plus syntax-only Substitution254, later composition | 157 | 117 | 508 | 40 |

No new Foundation source or object is needed. The accepted Alpha provider is `/tmp/validator-environment-alpha222-root-peer-sduorx47/lib/ZFCinPA/ValidatorEnvironmentAlpha222.olean`, SHA `0e905fe0fb08c3052ecfa8c46ccfc4d881e7590b677b36b5eebd8777823280e1`; root record SHA `5f2bdbc02ef0c245670402c50c0c5035ad910fccb884c02f7aa7f353c301d50b`.

The one added syntax-only client has current source SHA `13bc509376d444d9ad71de08468151637a8ec8aa943968aa61f57152c0ae9d9c` and historical primary `/tmp/zfc-validator-substitution-bridge/run1/cache/ZFCinPA/ValidatorEnvironmentSubstitution254.olean`, SHA `95d444289b2efdf8cde2c13483d8ddba7967060711939e6ca0b3402303f4c87f`. Its captured successful 4.32 source command and source snapshot are pinned in the recorded historical provenance; this exact pair was also reused in root's accepted fixed-consistency73 plan. Its private/server/IR companions are absent, not invented. No fresh replay of that old client is claimed. If root prefers refreshing that single unchanged source before the new pair, it requires no additional dependency and must remain a separately recorded execution.

Any subsequently approved execution would reauthenticate this narrowed closure, use private symlink providers and private outputs, retain `-M6000 -j1 -DElab.async=false`, preserve every attempt, and check the 512MiB reserve before compiling. At audit time free disk was 561,049,600 bytes. No cache tree, Foundation source, accepted source, shared object or Git state was changed for this proposal.
