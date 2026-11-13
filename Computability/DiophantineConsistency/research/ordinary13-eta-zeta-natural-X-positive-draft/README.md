# Proposed X positivity for the eta/zeta-natural probe

This unelaborated source-only adaptation proposes X=q*w>0 for an actual
probe zero at natural ports with represented beta>0. It uses the separately
adapted J-positivity and signed-unit sources and the existing source-only
`xzero_impossible` arithmetic client. It does not establish zeta positivity,
a zero map, provider coherence, a Lean theorem or an endpoint.

The essential graph changes relative to the prior eta-natural proof are
`k=eta+zeta` and the signed shift
`U*gamma−(eta+zeta−R−1)`; the latter has an extra +1 compared with the old
literal's kbase expression. Under w=0, the proposed graph binding is
`Dstar=U*(Y*c)+(3+4Y)*shift` and the norm is
`Dstar²=U²*(1+(3+4Y+Y²)*c²)`. The x-zero arithmetic lemma takes q≥2 and
Y≥q³, which the proposed J>0 and beta>0 source facts provide. Eta and zeta
may both be zero in this fact-level application; no strict eta/zeta premise
is assumed.

The checker pins the original and adapted sources, checks the exact source
transcription and evaluates 400 changed-graph w=0 main shapes. These do not
validate expression-pattern rewrites, graph units, model arithmetic, source
imports or compiled providers. From `Computability/DiophantineConsistency`:

```
python3 -I -S -B research/ordinary13-eta-zeta-natural-X-positive-draft/check.py | cmp - research/ordinary13-eta-zeta-natural-X-positive-draft/receipt.json
```
