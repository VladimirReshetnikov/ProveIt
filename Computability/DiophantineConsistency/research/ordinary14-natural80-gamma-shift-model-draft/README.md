# Natural 80-to-81 gamma shift: source proposal

`Natural80GammaShift.lean` is an **unelaborated source-only proposal** for
transporting zero existence between the 80 and 81 natural graphs. It uses
the separate proposed [gamma-positivity client](../ordinary14-natural80-gamma-client-draft/);
none of the graph, model, positivity, or dependent source proofs has been
compiled here. The checker pins the graph edit and source assumptions and
tests 300 signed modular evaluations; it does not run Lean or establish a
model theorem.

The proposed ring identity compares an 80 valuation with the 81 valuation
whose gamma slot 12 is one smaller. The model relation instead states that
the 80 gamma is the successor of the 81 gamma; all other slots agree. A
related pair is proposed to have equivalent `InternalZero` statements.
For existential transport, the source assumes representations of all four
ports by model naturals, `beta>0`, `K0>0`, `MC<beta`, and `MF<2*beta`,
then invokes the unelaborated gamma-positivity client to obtain a natural
predecessor. The reverse witness map increments gamma. It does not assume
gamma positive at the outset or assert same-valuation zero equivalence.

The three `#print axioms` commands have not been executed. Supplying the
selected symbolic port representations and bounds, elaborating the entire
dependency chain, proving iPRA derivability, and linking symbolic ports to
physical bytes and the displayed PDF remain separate obligations.

An [independent source review](../../reviews/ordinary14-natural80-gamma-shift-model-independent/README.md)
checks the graph edit, valuation directions and explicit predecessor-order
conversion without elaborating the model declarations.

```
python3 -I -S -B research/ordinary14-natural80-gamma-shift-model-draft/check_source.py > /tmp/natural80-gamma-shift.json
cmp /tmp/natural80-gamma-shift.json research/ordinary14-natural80-gamma-shift-model-draft/result.json
```
