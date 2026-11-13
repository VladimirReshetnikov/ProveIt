# Independent-k 84-operation graph: conditional zero correspondence

This **candidate**, generated from the pinned [eta/zeta-natural 85-row probe](../ordinary13-eta85-zeta-zero-boundary-audit/probe.json), deletes the single operation `kbase=n_eta+n_zeta` and uses a natural coordinate `n_k` directly for every occurrence of `kbase`. It has 13 natural inputs, four unchanged ports and 84 binary arithmetic operations. Its original syntactic degree bound is 110. A subsequent [exact polynomial certificate](../ordinary13-eta-zeta84-independent-k-degree99/README.md), checked by an [independent leading-form calculation](../../reviews/ordinary13-independent-k-degree99-independent/README.md), gives degree 99 for every fixed integer beta at least 3, including the compact beta, with the remaining ports arbitrary. That certificate is external and does not establish the zero correspondence or a Lean theorem.

There is an exact forward map on natural input tuples: keep every coordinate except number 10, and set child `n_k=parent.n_eta+parent.n_zeta`. The generated rows then coincide by structural induction, so the complete outputs agree at the same ports. Conversely, a child tuple with `n_k≥n_eta` maps back by `parent.n_zeta=n_k-n_eta`; the two outputs again agree. Thus, for any fixed integer ports,

```
parent has a natural zero  ↔  child has a natural zero with n_k ≥ n_eta.
```

The corresponding inequality and truncated subtraction have the same elementary meaning in an ordered model of IΣ₁, but **no Lean theorem or provider replay is supplied**. The identity above does not establish that every child zero satisfies the inequality, or that a child zero outside it can be replaced by one inside it. In particular, this is **not yet a proven 84-operation equation equivalent to Con(ZFC)**. The compact-port full-zero question for `n_k<n_eta` and any witness-replacement argument remain open. The parent eta/zeta zero-map and its parent bridge are themselves unelaborated.

The checker pins the parent, confirms that its old zeta input occurs only in the deleted addition, verifies every generated row by exact substitution, and checks the forward/inverse coordinate arithmetic on 300 deterministic modular controls. Those controls are only checks of the transcription; the structural row identity is the proof of the displayed conditional correspondence. No full-zero or inequality conclusion is inferred from samples.

From `Computability/DiophantineConsistency` run:

```
python3 -I -S -B research/ordinary13-eta-zeta84-independent-k-candidate/check.py | cmp - research/ordinary13-eta-zeta84-independent-k-candidate/receipt.json
```
