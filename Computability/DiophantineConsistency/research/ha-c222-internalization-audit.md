# C222 internal arithmetic calibration: critical-path audit

Date: 2026-10-26. Read-only source audit by `complemented47_review`.
Repository HEAD observed: `b51f2073a17521d06b86f0b760cd0cf8f89ea783`.
No compiler, packet program, proof generator, or incoming script was run for this audit.
The source hashes below identify the inspected contracts independently of later commits.

## Finding and smallest next proof

The reusable internal endpoint is **C254 validator consistency**, not C222 and not the
215-state machine. The missing bridge is an equivalence of *internal refutation
witnesses*, in every model of the proposed arithmetic base theory. Standard-Nat
halting equivalence and represented-run totality do not supply it.

A concrete small next checkpoint is `ArithmeticTemplates222` plus
`ValidatorGrowG222`: represent the literal `growG` constructor circuit, then prove
`ValidatorProvability254.CProv (growG a b c)` for arbitrary internal `a,b,c`.
This discharges the changed equality leaf without changing the decoder or assuming
an internal C222 calibration. It leaves the seed bundle and actual runtime bridge open.

## Exact difference being calibrated

`KCode222.C222` keeps truth, MP, GEN, rho1--rho6 and rho8. It replaces rho7 by

```
growG a b c = (c=a) -> ((c=b) -> forall_(wel a b) (a=b)).
```

Its other changed axiom is `bundle222 a b c`, gated only by `c != a` and `c != b`:

```
req b k m  = forall_b (m -> not(forall_b (m -> not(b in k))))
clos a b k m = forall_b (b in k ->
  not(forall_a (m -> not(forall_a (
    (forall_k (k in a -> k in b)) -> req b k m)))))
nks a b c = forall_c (clos a b c c -> not(req b c c))
vrel a b c = (a in b -> forall_c (a in b))
bundle222 a b c = not(vrel a b c -> nks a b c).
```

Here `not p` is the live implication to numerical false code **1**. The matrix
code and its private binder are both `c`. This is not the old C254 conjunction
of container, GIC, membership vacuity and equality vacuity. The cases `a=b` and
`c=0` are legal when the stated gate holds; they must not disappear in a port.

The literal 215 machine uses `EnumPerm`, not a base12 proof-tree interpreter.
Its commands are NIP=0, DROP=1, MP=2, AX=3+c; AX reads `y` before `x` and emits
only dominated rho8 instances (`u <= a`). `EnumPerm.build_c222` uses
`DomRho8.rho8_all_of_restricted` to recover the unrestricted calculus.
`SeedPerm.seed` is `(pl,np,tw,ws,d,h)=(0,4,0,0,0,0)`.
The external compiler prefixes `START_Y = AX(0;1,Y)` and proves its candidate
number is at least `Y`; setting `Y=4` is why skipping candidates 0--3 is safe.
Neither this witness compiler nor the stack invariant has an all-internal
arithmetic counterpart in the searched active modules.

## Existing contracts that really are reusable

| Source/API | Established scope and reuse boundary |
|---|---|
| `ArithmeticTemplates254.Circuit.graph`, `.defined` | A fixed finite constructor circuit has a parameter-free Sigma0 graph at arbitrary internal inputs, already under IOpen. New growG and seed circuits require no new coding machinery. |
| `ModelCodedDecoder254.decode`, `decode_isFormula`, `decode_succ` | The same base4 formula decoder, represented by internal course-of-values recursion in every IΣ1 model. Its name does not restrict its inputs to C254 theorems. |
| `ModelCodedDecoderCircuits254.decoded_circuit_equiv`, `zf_decoded_circuit_equiv` | Interprets any fixed circuit at arbitrary internal inputs. Numerical binder labels are preserved. Does not prove new axiom validity. |
| `ModelCodedDecoderFreshness254.positive_code_fresh` and `decode_binder_fresh` | Internal capture/freshness facts, useful for the seed's self-labelled matrix. Positive-code premise matters: handle `c=0` separately. |
| `ModelCodedDecoderAtomicVacuity254.namedFormula_eq_vacuous`, `decoded_weq_vacuity` | Equality vacuity at any binder distinct from the two names, with no distinctness of those two names. Useful for growG. |
| `ArithmeticHistory254` / `ArithmeticProofConstructors254` | Actual base12 course-of-values checker, total unique graph in all IΣ1 models, with explicit numeric proof constructors. A C222 sibling can reuse this architecture but cannot reuse its unchanged row theorem. |
| `ValidatorProvability254.CProv`, `cProv_classical`, twelve closures | Sigma1 theorem predicate `exists d, value d = conclusion+1`; closures are all-internal, not Nat adapters. |
| `ModelCodedDecoderAccepted254.rowKernel_sound`, `rejected_or_decoded_provable` | Internal accepted-proof induction for old leaves. A C222 variant needs new tag9 and tag11 soundness; the target may need L-relativization for the latter. |
| `R2Native.cProv_falsum_of_ZF` | In IΣ2, an internal Foundation-ZF refutation gives **CProv254 1**, via native-theory equality/container/GIC axiom translations. It does not quantify over an arbitrary replacement validator. |
| `LSchema.provable_falsum_ZF_of_ZFC` | Internal ZFC-to-ZF refutation translation using the L interpretation. Its schema theorem handles Foundation separation/replacement codes, not arbitrary C222 seed bundles. |
| `ValidatorConsistencyEquivalence.iSigma2_proves_con_ZFC_iff_validator` | Actual IΣ2 theorem `Con(ZFC) <-> not exists d, ArithmeticHistory254.value d=2`; PA weakening also exists. |
| `ArithmeticMachineRun215.run_total`, `run_defined_delta`, `haltingSentence` | Exact decimal215 represented run is total unique at every internal time. `run_nat`, `run_represents`, `run_halt_iff` and `haltingSentence_nat` compare to the actual Core machine **only at ordinary Nat inputs**. |

The source search for `C222|growG|bundle222` returned no matches in active
`ZFCinPA/Lean`, `BusyBeaver/ZFC/Arithmetic*.lean`, or the new
`DiophantineConsistency/Arithmetic*.lean` modules. This is a scoped search,
not a claim about every inert manuscript or historical verification packet.

## Minimal final bridge, and a practical decomposition

The following are **proposed missing signatures**, not existing theorems. The
`V` assumptions mean `ORingStructure V` and `V` models IΣ2 (with its IΣ1 instance).
No assumption should say that the desired consistency equivalence already holds.

```
theorem internal_215_accepted_falsity_iff :
  (exists time : V,
    ArithmeticCantor.first (ArithmeticMachineRun215.run time) = 0) <->
  (exists d : V, ArithmeticHistory254.value d = 2)
```

This is the smallest logical connection to reuse the existing IΣ2/PA endpoint;
an all-conclusions C222-to-C254 identity is stronger than needed. A proof should
be decomposed into inspectable witness-producing interfaces, for example:

1. **Actual C222 checker.** Define `rowKernel222` by changing old tags 9/11 only;
   prove a represented `value222`, totality, recurrence and numeric constructors.
   Its standard specialization must recognize the actual `KCode222.C222`, not
   an assumed new calculus. `CProv222 p := exists d : V, value222 d=p+1`.
2. **Internal logical calibration.** Prove both
   `(exists d, value222 d=2) -> (exists e, value254 e=2)` and the reverse,
   or use internal Foundation-ZF refutations as the intermediate witness.
   Each direction requires actual internal proof construction/induction.
3. **Actual runtime connection.** Prove
   `(exists time, first(run215 time)=0) <-> (exists d, value222 d=2)`.
   This must internalize the command-permuted enumerator, dominated rho8
   compiler, counter4 reachability, register program and the exact table's
   operational simulation. An unrelated generic represented machine is insufficient.

The new checker is a useful isolation layer, not logically compulsory. A direct
represented `EnumPerm` invariant could avoid it, but would couple the set-theory
translation to stacks and runtime witnesses. Reusing existing decoder recursion
and adding a small C222 checker seems the more reviewable route; the checker
alone does not solve either substantive calibration obligation.

## Why the seed is the substantive logical obstacle

`KUpper222.seed_in_VL` proves the seed property for each external `Form` by
choosing a constructible stage containing the finitely many parameters,
reflecting the matrix and its existential closure, arranging subset closure,
and separating a container. `bundles_in_L` applies this to the decoded standard
matrix; `zf_refutation_of_c222` then invokes external `completeness_inf_context`.
`KSeedDirect222.seed_direct` and the equality interpretation give the external
lower-bound route. These are valid external results, but do not give a uniform
internal proof code for a possibly nonstandard matrix/derivation.

In particular, `ModelCodedDecoderBundle254.zf_decoded_bundle_provable` proves
the **old** bundle. Substituting `bundle222` there is invalid. Nor does the
existing source establish unrelativized `Provable ZF (decode(bundle222 a b c))`
for arbitrary internal inputs. A plausible upper-bound port needs a coded
L-relativized seed/reflection theorem and preservation of MP/GEN under that
interpretation. This audit does not prove that unrelativized translation is
impossible; it identifies what the current sources actually provide.

For the reverse logical direction, recovering rho7 from growG is finite
(`KEqCodes222.rho7_222` gives the external symbolic argument). Recovering the
old container/GIC axiom interface from seed-K, including nonstandard matrices,
is not furnished by `R2Native`: its `axOK_native` is hard-coded to CProv254.
The external equality/seed interpretation must be turned into represented
syntactic translations or replaced by another explicitly proved internal route.

## Proposed small implementation after review

Define the following fixed circuit using existing `Circuit.im/eq/al/el`:

```
growGCircuit = im (eq input2 input0)
  (im (eq input2 input1) (al (el input0 input1) (eq input0 input1)))
growG a b c = growGCircuit.eval a b c 0
```

Prove its Sigma0 graph and Nat specialization to `KCode222.growG`. Then in every
IΣ1 model prove `CProv254 (growG a b c)`: put `v=wel a b=4*cantor a b+1`;
`ArithmeticCantor.components_le` gives `a<v` and `b<v`. From
`cProv_bundle a b v`, extract `(a=b)->forall_v(a=b)` using the existing
polymorphic classical propositional certificate; compose it with
`cProv_rho7 a b c`. The source equality row needs **no** `c!=a,b` premise.
The accepted-row theorem then also gives internal ZF-provability of its decoded
formula. This is a bounded, substantive proof task and removes one changed leaf;
it is not advertised as solving the seed, enumerator, or consistency bridge.

## Theory and provenance boundary

Even completing the displayed all-model bridge would first yield the specified
**classical IΣ2/PA** theorem. It would not by itself be an HA derivation:
the existing endpoint uses classical arithmetic completeness and PA weakening.
HA proof objects, a suitable constructive syntactic translation, and the
equation-to-arithmetic-sentence connection require their own stated results.
Likewise the external proposition `DiophantineConsistency.ConZFC` and
Foundation's represented arithmetic consistency sentence must not be silently
identified inside an arithmetic theory.

This audit relies on source contracts, not a new dependency-closure replay.
The author previously wrote the exact215 represented-run packet and several
native Diophantine modules; that authorship is disclosed rather than counted as
independent validation here. No source or object was changed apart from this note.

## Source pins

Paths in the following table are repository-relative. SHA-256 values were read
from the actual source files at completion of the audit.

- `BB` = `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/`
- `ZP` = `Logic/Interpretability/ZFCinPA/Lean/ZFCinPA/`
- `DC` = `Computability/DiophantineConsistency/Lean/DiophantineConsistency/`

| Source | SHA-256 |
|---|---|
| `BB/KCode222.lean` | `fbc4fef6e479b6bc5bc83bcfafa73fb1befdc1b1d02b605da68ecf691f641eb3` |
| `BB/KSeed222.lean` | `f1edf98f4bcd6f548f8e7b8ca59afdf4f01fc8307c1fdab19b21d95afb9543e8` |
| `BB/KSeedDirect222.lean` | `671c413d14ec8b75d2c80f51ca8acb35acaf408fb8d0f4581df42e6fdc9f92af` |
| `BB/KSeedInterface222.lean` | `0ac1d3e3a2071fe04865502dcf0decb22fa9a32dfcceb7fa2e9c33c72cfc188e` |
| `BB/KEqCodes222.lean` | `1e2e768af99cbf3fe1cae0f4f41e93c229e77f8ea4937ceab9884a93ff8071cb` |
| `BB/KEind222.lean` | `cc863d4b209b505c3240d683812d86c4cd4f1a599abce050c5e558e09592a508` |
| `BB/KUpper222.lean` | `e9ad034a48cfef16d9d2aa388b1ab8536a68168e04497ca4c198d519bb84a511` |
| `BB/EnumPerm.lean` | `0c2a214ef68b37cb4df92c9a208d069bd2b4fca04f062483dfd11dc2b2a9e30e` |
| `BB/SeedPerm.lean` | `ed038b38122aca4ebd1f31a48f2ea9e99d2bb6f33a406cab4039ba62163b80ec` |
| `BB/KEndpoint215.lean` | `77b71164cf3cac4303ab786852e58969bc5c7332c5261aecfc22a63d3a39dfc9` |
| `BB/DomRho8.lean` | `8fdbec0db9134070bee2dfa0a433aff66ab83c00007ea7b9aabd9192c506d378` |
| `BB/ArithmeticCantor.lean` | `aadfdeb41e75c1652b555ed996fea5d15d7f1b9f65c7c553823a99773ee24c84` |
| `BB/ArithmeticCode254.lean` | `2edf178b0061838b13299f1332d65c4fc3194207cbd0e761f129a7bcc36bdff0` |
| `BB/ArithmeticTemplates254.lean` | `2031511caadb7bf794d190cea99bedfa32022197f64612cb270daceee986f65f` |
| `BB/ArithmeticRow254.lean` | `90c29554d76400618777a6139be5089220093a5effb2b0587f0d3ab497d0ca7c` |
| `BB/ArithmeticHistory254.lean` | `4cf3d35c0c8d156bfb14ceacf87a799e9d4a35108a17c70bb63c4f93278a9e2e` |
| `BB/ArithmeticProofConstructors254.lean` | `34d33aeb05b4b37a29659aa3d6e86281783fab70574a8352eded4560b6dfb875` |
| `BB/Code254Proof.lean` | `7bb8daf0f1c0965d22f2f16bbb1898d60cfb79f9a6feabe8ab38b3f69b3bc6d1` |
| `ZP/ModelCodedDecoder254.lean` | `1f471e17aa569a342e6e98b0985a86a7837a34b434bfedf35019e7e4014ba6e0` |
| `ZP/ModelCodedDecoderCircuits254.lean` | `746b0e0d1f0b8960c5c76c5a0a57833a794c49da01620798ff29eefa962dbe67` |
| `ZP/ModelCodedDecoderFreshness254.lean` | `62d50a4c46bbd83a32452b650ddecc311555eb024fbe7aa30f11df0057b45b83` |
| `ZP/ModelCodedDecoderAtomicVacuity254.lean` | `e3cdebe04cb8e85bb115105c41dc2c764e52c91914cdfd3cd98a391bca947e14` |
| `ZP/ModelCodedDecoderEquality254.lean` | `727f6fd2aa5740ab9e91d84b161cc89a1b0862d997af97ba71feee8c75bb61fd` |
| `ZP/ModelCodedDecoderBundle254.lean` | `a7a1ee775ffcc0753b4d10a0214229441a7f3c4a1ebd81b27cdf98cc245c01a2` |
| `ZP/ModelCodedDecoderAccepted254.lean` | `7459498d7e2243cb254178d08d28954ca740b626c6d2865642bd9e1c3fb892dc` |
| `ZP/ValidatorProvability254.lean` | `372a7fbd58fb5d018951e3e23dc308062ad02546279620e1d67fb3d06e7845b6` |
| `ZP/R2Native.lean` | `5dede1cf75df4ae1d9309cd24f6febe3573557fadbd037aeada97988260f68c4` |
| `ZP/LSchema.lean` | `c68dbfb6e9b152ab71654de3a2b2cf3559ebe1f8e616edabd12e24209ea568f2` |
| `ZP/ValidatorConsistencyForward254.lean` | `ed61e36f97d574bc0a381c849f7f89008d9b5e5545f99fc7bf520838b60a49f9` |
| `ZP/ValidatorConsistencyEquivalence.lean` | `e0502e78a7c1a4a8c6d3f242279ae557ce91678dfd9cb52aa628bf38c0fbd242` |
| `DC/ArithmeticMachineGraph215.lean` | `bd2bef54c8ba0c1b59dec84d1797edb68d122467e73fc743ef71e5c4ab2acaad` |
| `DC/ArithmeticMachineStep215.lean` | `c04419c271a006d9e1526b75e86fb08de176be5589867abf6f7f2b1093ba7c37` |
| `DC/ArithmeticMachineRun215.lean` | `98f0c7004ac5796616bd3d7967a5bed443e7add149456813a0fd2d152a3751cd` |
