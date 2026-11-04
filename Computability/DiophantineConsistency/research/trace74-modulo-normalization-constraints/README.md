# Constraints on same-q, same-k modular normalization

This note examines a proposed witness transformation, not an established one. Keep ports, J, q=beta·J+1 and k fixed, and suppose the chosen replacements have `F′=F−aq`, `C′=C−bq`. Write Δ for new minus old, `R` for the signed 74 rank, and `B=(K0+w)C−F`. Direct ring expansion gives

```
ΔR = q(q²−1)(aq+b),
ΔB = q(a−(K0+w)b).
```

For two actual positive 74 graph zeros with the same q and k, the previously checked guard-free offset theorem gives `q⁴ | (k−R−1)` for each. Hence their rank difference must be divisible by q⁴. This necessary condition holds regardless of how the other witnesses, including T and the carrier variable, are adjusted. For example, at any ordinary integer q>1, changing F=q+1,C=1 to the positive residue representatives F′=1,C′=1 gives ΔR=q²(q²−1), which is not divisible by q⁴. At q=2 the nondivisibility is `16 ∤ 12`. This is an algebraic obstacle for that specific same-k rule; it does not assert the existence of an initial graph zero with those coordinates or exclude a transformation that also changes k or q.

Further constraints appear if additional registers are preserved. With c and f fixed, `V=f(cT−R)−c` gives `ΔV=f(cΔT−ΔR)`. Preserving V exactly, with nonzero f, requires `cΔT=ΔR` and hence signed divisibility `c|ΔR`. Preserving only V² leaves both V′=V and V′=−V sign cases; the latter instead requires `f(cΔT−ΔR)=−2V` and is not discarded here.

If h,D,H,K and L=V² are fixed, the 74 carrier numerator is

```
Z = hD(H(N−LB)+K)−H(DB+he),     e=k−R−1,
ΔZ = H[hDΔN − (hDL+D)ΔB + hΔR].
```

Here N is the carrier variable, distinct from the first-Pell index. Preserving Z exactly and using nonzero H requires `hD` to divide `(hDL+D)ΔB−hΔR` in the signed ring. Preserving only Z² permits the additional Z′=−Z case. These constraints explain why adjusting T and N is not automatically sufficient; they do not prove a global nonexistence of an alternative witness transformation.

The pinned `check.py` verifies the rank, B, V and Z equalities in a free commutative polynomial ring over the integers and checks the q=2 nondivisibility sample. Run `python3 -I -S -B research/trace74-modulo-normalization-constraints/check.py` from `Computability/DiophantineConsistency`. Author exit 0; checker SHA-256 `249304bcd3455ac7ee4b89fd0cc96473148ded99d71e5d03f79bf5550c3bdc11`; stdout SHA-256 `484ec20ec5cbc5f36cc01c41bf3fa9ffc401dd77daa54b8a920359019997e38c`; stderr empty. This is external arithmetic with pinned source bytes; it is not a Lean theorem of witness nonexistence or a formal binding to every graph register.

Independent [result audit](../../reviews/trace74-modulo-normalization-constraints-independent/README.md) passed, SHA-256 `de83ff11425f1e2ba5a99a1f2b0abc047047ba3148f4ccfeef60ec03147592b6`. It checked the correction that K is fixed in the displayed ΔZ identity, all Δ signs, and the conditional q⁴ necessity; it does not assert a Lean witness-transformation theorem.
