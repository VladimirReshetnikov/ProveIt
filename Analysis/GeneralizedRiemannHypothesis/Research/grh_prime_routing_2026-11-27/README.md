# Locally resilient rainbow routing with small prime multipliers

Research packet, 27 November 2026. Main result: under the Dirichlet GRH exported by the pinned vendored Lean source, even arbitrary vertex-dependent deletion of arcs retaining more than half of the incoming and outgoing edges permits prime-disjoint directed linkages of optimal asymptotic capacity at cutoff `(log q)^A`, `A>2`.

## Files

- `prime_routing.tex`, `prime_routing.pdf`: complete mathematical paper, including finite theorem, proofs, arithmetic corollaries, matching-order upper bounds, and references.
- `SOURCE_AUDIT.md`: reviewed GitHub paths, exact Git blob identifiers, comparison with article results, and limitations.
- `FORMALIZATION.md`: proposed Lean dependency structure; **not** a completed formalization.
- `routing.py`: standard-library Python route constructor and exact verifier.
- `examples.json`: explicit route certificates for moduli 1009, 1155, and 5003, reconstructed against seeded locally damaged graphs.
- `experiment.log`: actual verifier output.
- `SHA256SUMS`: integrity checks for the deliverables.

## Reproduce

```sh
pdflatex -interaction=nonstopmode -halt-on-error prime_routing.tex
pdflatex -interaction=nonstopmode -halt-on-error prime_routing.tex
python3 routing.py --verify examples.json
# or regenerate the examples:
python3 routing.py --output examples.json
```

Run the verifier before editing the archived files; `sha256sum -c SHA256SUMS` checks the original packet. The experiments are finite illustrations, not an empirical or formal proof of GRH. The paper uses classical analytic estimates under Dirichlet GRH and proves the finite combinatorial transfer. Novelty relative to the merged article is supported by targeted comparison; absolute literature priority has not been established. No repository changes have been made.
