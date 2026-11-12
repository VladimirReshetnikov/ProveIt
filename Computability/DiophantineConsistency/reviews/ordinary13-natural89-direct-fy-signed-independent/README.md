# Independent review of natural 89 direct f/y source

This is a source-level mathematical review of
`research/ordinary13-natural89-direct-fy-model-draft/`. It does not elaborate
Lean or establish the imported source providers.

The four forward graph maps change coordinates 0, 12, 6 and 9, respectively,
so f at coordinate 3 and y at coordinate 11 are unchanged. The checker
compares all four successive JSON row sets and exact source shift declarations;
the last graph is the stated 85 prototype. The maps use the forward
`zero_iff` implications and require the same natural compact port tuple.

For f, the cited strong equation is `I² + Delta = Delta*f²`; the separately
proposed fact lemma forces f positive when `Delta>0`. For y, the cited *raw
signed* auxiliary equation is `y² - Delta*(f²-1)*(y²-z²)=1`. Setting y to
zero gives `Delta*((f²-1)*z²)=1` in the difference ring, using the same graph
witness z. The receipt independently verifies this identity as a complete
integer polynomial, including its sign. It also checks the exact prototype
factor rows and the source signature reflecting signed divisibility of natural
casts back to the model naturals. Since `Delta=3+4*a+a²≥3` for natural a,
reflected `Delta ∣ 1` contradicts the natural divisor bound. This argument
does not need a signed-rank orientation, eta positivity, or a prior f/y
positivity premise.

The intended conclusion is exactly the `DirectFY K` interface needed by the
89-to-positive-80 proposal. It does not provide a positive-r replacement,
the positive-80 bridge, or an iPRA endpoint. In particular, the graph maps,
signed factors, model arithmetic, imported reflection and cast rewrites
remain source-level proposals pending Lean/provider validation. The independent
polynomial and graph checks do not validate their tactics or kernel proofs.

Reproduce the receipt from `Computability/DiophantineConsistency`:

```
python3 -I -S -B reviews/ordinary13-natural89-direct-fy-signed-independent/check.py
```
