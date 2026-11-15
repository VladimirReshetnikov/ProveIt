# Ordinary PA axiom suppliers under arbitrary arity-zero packets

`ordinaryAxiom_shift` proves that every modeled member of the existing ordinaryPAeq Δ₁ axiom classifier is shift-invariant, including nonstandard induction instances. The fixed-axiom case uses the exact finite theory classifier and syntactic sentence quotation; the induction case uses the existing modeled closure theorem.

`ordinaryAxiom_root_packet` combines that fact with the independently replayed closed-sentence environment theorem. For any internally valid ordinaryPAeq axiom and any valid source-arity-zero packet, it identifies the packet's translation with the root-packet translation as an exact formula code. `ordinaryAxiom_packet_of_root_supply` transports a hypothesized source-provability supplier for every internally valid ordinaryPAeq axiom from root packets to any valid arity-zero packet. This transport uses no unguarded derivation invariant and needs no packet-length bound.

The root source-provability supplier remains an explicit hypothesis, including the arbitrary internal induction case. These results do not prove that supplier, the guarded existential rule, a full guarded compiler, or an iPRA implication. The theorem is stated in every IΣ₁ model, including nonstandard models.

Reproduce from the repository root with a fresh empty output:

```sh
bash Computability/BusyBeaver/Research/PA/pa194-work/pa194-model-logic/check-ordinary-packet.sh "$PWD" /dev/shm/pa194-ordinary-packet-repo-NEW
```

The checker rebuilds two source modules and a four-report audit. It retains the separately replayed closed-sentence theorem, the finite ordinaryPAeq classifier, and other explicitly listed prebuilt paths; it does not rebuild the full dependency closure.
