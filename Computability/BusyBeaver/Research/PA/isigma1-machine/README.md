# Turing machines inside models of IΣ₁

This directory states, for an arbitrary two-symbol transition table, the one obligation that
is left for the iPRA equivalence with the consistency of PA, and derives the equivalence from
it. No table is shown to meet the obligation.

## `ConPAMachine.lean`

Imports Foundation only. For `T : Table`, a list of rows `q b w d q'`, and any model `V` of
`𝗜𝚺₁`:

- A configuration is the number `⟪q, l, r⟫`: the state, the tape to the left of the head as a
  binary number whose lowest bit is the cell next to the head, and the tape from the head
  rightwards as a binary number whose lowest bit is the cell under the head. The blank initial
  configuration in state 0 is the number 0.
- `step T : V → V` is one step. A configuration to which no row applies is its own successor.
- `run T : V → V` is the configuration after `t` steps, for `t` in `V`, so `t` may be
  nonstandard. It is built with Foundation's `PR.Construction` and satisfies
  `run T 0 = 0` and `run T (t + 1) = step T (run T t)`.
- `haltDef T h` is a `Σ₁` sentence of arithmetic, and
  `haltDef_iff : (haltDef T h).val.Evalb ![] ↔ ∃ t : V, π₁ (run T t) = h` in every model.
- `haltDef_standard`: over the natural numbers the sentence is true exactly when the iterated
  step function reaches the state `h`.

## `ConPAMachineEndpoint.lean`

```lean
def Calibrated (T : Table) (h : ℕ) : Prop :=
  ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁],
    Provable (𝗣𝗔 : ArithmeticTheory) (⌜(⊥ : ArithmeticSentence)⌝ : V) ↔
      ∃ t : V, π₁ (run T t) = (h : V)

theorem endpoint (T : Table) (h : ℕ) (hc : Calibrated T h) (hb : BoundCertificate) :
    standardTheory ⊢ nativePAConsistency 🡘 ∼machineHaltSentence T h
```

`Provable` is Foundation's internal provability predicate, so the proof of `⊥` may be a
nonstandard element of `V`, and so may the halting time. `machineHaltSentence T h` is the
strict form of `haltDef T h` mapped into the language of iPRA
(`ConPA.ISigma1Transfer.haltSentence`). `hb` is the PA witness certificate, as in
[`../isigma1-transfer`](../isigma1-transfer/README.md).

## `ConPAUnconditional.lean`

Imports `PA196PACertificateComplete` from `../pa196-vs-u208/ipra` and instantiates the
transfers with its `certificate`, so that only the machine statement is left as a hypothesis.

```lean
theorem machine_endpoint (T : Table) (h : ℕ) (hc : Calibrated T h) :
    standardTheory ⊢ nativePAConsistency 🡘 ∼machineHaltSentence T h

theorem ipra_of_models (halt : Semisentence language 1) (hopen : halt.Open)
    (hbounded : Hierarchy 𝚺 0 halt)
    (h : ∀ (M : Type) [Nonempty M] [Structure language M] [Structure.Eq language M]
      [M↓[language] ⊧* PRA], ReductISigma1 M →
        ((M↓[language] ⊧ ∃⁰ halt) ↔ (M↓[language] ⊧ mappedPARefutation))) :
    standardTheory ⊢ nativePAConsistency 🡘 ∼native (∃⁰ halt)
```

`ipra_of_models` is for a halting matrix of the PRA language, such as the atomic matrices
`haltMatrix` of `PA194ForwardGG` and `PA196ForwardGG`, for which `native (∃⁰ haltMatrix)` is
the halting sentence of those endpoints. `classical_reductions` gives the two classical PRA
reductions from the same hypothesis.

## What is not proved

- `Calibrated T h` for any table. This is the whole machine-specific content: the machine
  has to be verified inside an arbitrary model of `𝗜𝚺₁`, in both directions.
- That the arithmetic of `step` agrees with another formal semantics of Turing machines, for
  example the zipper machine `M6.Zip` used elsewhere in this tree. `haltDef_standard` relates
  the sentence only to the iteration of `step` over the natural numbers.
- That `machineHaltSentence T h` is equivalent in iPRA to a halting sentence built from a
  function symbol.

## Checking

```sh
bash Computability/BusyBeaver/Research/PA/isigma1-machine/check.sh
```

It compiles `../isigma1-transfer/ConPAISigma1Transfer.lean` and the two files of this
directory against the root Lake workspace, prints the axioms of `isigma1_iff` and `endpoint`
(`propext`, `Classical.choice`, `Quot.sound`) and fails if `sorryAx` occurs. It
passed on Windows and in an independent Linux replay with Lean 4.32.0 and the
iPRA/Foundation overlays, after rebuilding the missing PA-consistency
dependency from the repository source. That check does not prove `Calibrated`
for a machine or discharge the bound certificate.

```sh
python3 Computability/BusyBeaver/Research/PA/isigma1-machine/check_unconditional.py
```

compiles `ConPAUnconditional.lean` with everything it imports outside the root Lake
libraries: the upstream `M6.Zip` and `PA196.Literal`, the modules of `../pa196-vs-u208/ipra`
that the certificate needs, and the files of the two `isigma1-*` directories, 100 modules in
all, one `lean` process at a time. It prints the axioms of `certificate`, `machine_endpoint`
and `ipra_of_models` and fails if `sorryAx` occurs in any log. With `--out DIR` it keeps the
objects and skips modules already compiled there. `IPRA_LEAN_OVERLAY` and
`IPRA_FOUNDATION_OVERLAY`, when set, are searched before the root Lake objects.

The unconditional check was run on Windows (Lean 4.32.0) with objects built
in two passes. An independent Linux replay also passed from an initially empty
tmpfs output directory, using the iPRA/Foundation overlays and privately
rebuilt missing PA-consistency dependencies. That replay was resumed after
fixing the checker and rebuilding missing overlay dependencies, reusing the
already checked objects and logs in the same directory. All 100 module logs
were checked for `sorryAx`; the reported axioms are `propext`,
`Classical.choice`, and `Quot.sound`. No machine calibration follows from this
certificate check alone.

## One-direction transfers

`ConPAISigma1Directions.lean` separates the two calibration obligations. For
an open, bounded halting matrix, it proves:

- If in every candidate PRA model with an IΣ₁ reduct an internal PA refutation
  implies halting, then standard iPRA proves that nonhalting implies Con(PA).
- If in every such model halting implies an internal PA refutation, then
  standard iPRA proves that Con(PA) implies nonhalting.

Each hypothesis concerns **all** the relevant models, including nonstandard
proofs and clock times. Neither hypothesis is established here for any
machine. The proof separately transfers each implication through the
open-existential conservation theorem, the PA witness certificate, and the
Gödel–Gentzen interpretation; it does not require the opposite implication.

With the audited `IPRA_LEAN_OVERLAY` and `IPRA_FOUNDATION_OVERLAY` set, run
`bash Computability/BusyBeaver/Research/PA/isigma1-machine/check-directions.sh`
for a fresh dependency and certificate rebuild and an axiom check. An
incremental check of the new module has passed against independently rebuilt
transfer and certificate objects, reporting only `propext`, `Classical.choice`,
and `Quot.sound`.
