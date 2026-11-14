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
(`propext`, `Classical.choice`, `Quot.sound`) and fails if `sorryAx` occurs. It was run on
Windows under Git Bash (Lean 4.32.0).
