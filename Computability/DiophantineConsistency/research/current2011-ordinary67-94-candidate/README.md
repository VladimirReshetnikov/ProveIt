# Current-port ordinary 67-operation degree-94 candidate

This is a 14-positive-variable integer-leaf equation at the four current2011 ports. The graph copies the first 51 rows through `V` of the pinned 71/80 graph and finishes with

```
I = i*c²
Aaux = Delta*(f²−1)
Na = Aaux*(V²−y²)+y²
Ns = 1+I²−Aaux
N0*N1*Na*Nt*Ns−1 = 0.
```

All 67 binary gates, 14 coordinates and four ports are live: 37 multiplications, 17 additions and 13 subtractions. This is an adaptation of the separately recorded ordinary 67/94 construction in [`arithmetic-intake-20261026b`](../arithmetic-intake-20261026b/README.md), with the actual current-port prefix and coefficient bytes. A later [current-base Lean endpoint](../current2011-ordinary94-fresh-endpoint/README.md), [independently reviewed](../../reviews/current2011-ordinary94-fresh-endpoint-independent/README.md), checks the existential no-zero bridge and standard-iPRA derivability; this improves the 67/106 degree tradeoff. The external graph/byte and Lean syntax correspondence retains its stated scope. It does not replace the maintained equation or PDF.

`check.py` authenticates the exact parent prefix and complete port bytes, verifies the gate graph and liveness, and gives degree at most 94 using the pinned exact prefix leader certificate. It then evaluates the full 67-row graph on the ray with all witnesses equal to `t`, over the fixed actual-port residues modulo 1,000,000,007: the resulting degree is 94 and its leading coefficient is 495,675,807. Hence the specialized integer polynomial has exact degree 94, conditional on the separately audited prefix degree certificate. No Lean total-degree theorem is claimed.

The algebraic forward map is `i_new = Delta*i_old` with every other coordinate unchanged. Let `S_old = f²−Delta*(i_old*c²)²` and `G=V²−y²`. `forward_check.py` proves in a sparse universal polynomial ring that

```
I_new²−Aaux = Delta*(1−S_old)
Na_new−U_old = Delta*(S_old−1)*G.
```

Thus when the original strong norm is one, the new strong norm is one and its auxiliary norm equals the old auxiliary norm. Positive original witnesses have positive transformed `i` because `Delta>0`. The existing original-zero norms theorem supplies the needed strong-norm condition in its checked IΣ₁ setting. This is a paper/external algebra observation here; neither the forward witness map nor this graph has been checked as a Lean model theorem in this packet.

The simple same-witness reverse map is insufficient: a candidate zero only yields `(i*c²)²=Delta*(f²−1)`, and its `i` cannot simply be divided by `Delta`. The later checked endpoint uses relaxed Pell index recovery and machine soundness for the existential reverse direction; it does not claim a same-valuation reverse map. The examples in [`ordinary67-relaxed-same-f-obstruction`](../ordinary67-relaxed-same-f-obstruction/README.md) show why changing witnesses can be necessary, without giving a full graph counterexample.

Run from the repository root:

```
python3 -I -S -B Computability/DiophantineConsistency/research/current2011-ordinary67-94-candidate/check.py
python3 -I -S -B Computability/DiophantineConsistency/research/current2011-ordinary67-94-candidate/forward_check.py
```

`build.py` is deterministic and refuses to overwrite the existing graph. These checks use no Lean.

The graph's original `coefficient_binding.path` points to `coefficients/` in
this directory. That path was initially missing; the four byte-identical
payloads have now been copied from the audited 71/80 sphere packet so the
unchanged graph metadata resolves directly. `check-metadata.py` verifies those
paths, the recorded hashes and lengths, and the referenced certificate and
proof. This does not prove Lean file semantics or establish new byte-to-port
identities.

| Artifact | SHA-256 |
| --- | --- |
| `build.py` | `16e395bf42e20142b531aa87dbf3278f10940b679d7e9f5a83050c85290854` |
| `polynomial.json` | `d76264440a60d1fbdf6a98ddd0997ae28a504a61a96e5f7e494fc5c3f423badb` |
| `check.py` | `d55b77eeb02635efbb6a91e38571c347ab057b7d0876fdd07f33282d88a22770` |
| `result.json` | `28fa605de3c317d649e240f9e71da3d576f50d812a4e1212edb52df64ac9cf9d` |
| `forward_check.py` | `ef40da2418160ddf166b9ef817311722c667e1a36ba041e7475f6113b8136b18` |
| `forward-result.json` | `1be665151dff6a537821624f3dfe7aec9ec42d375c54840813f85165927b1a53` |
