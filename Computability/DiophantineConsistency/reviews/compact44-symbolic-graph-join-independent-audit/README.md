# Independent audit: paired conditional symbolic graph join

The paired evidence at `868493c860` records actual protected outer session 36951 exit 0 at HEAD `4634912ff5281950cf4517ed0146062a06dff813`, with receipt SHA-256 `9bc91a18e8a8159621c97eb24b20a09bb0c8da82d0931904a3cf2082849e59be`. The independent artifact audit actually exited 0 in session 96636 without launching Lean. It reran both complete graph-digit and low-even parent audits and checked the 14 frozen source, object, compiler-log and dependency rows; both complete 127-object same-side inherited overlays; exact source imports and required package Init; matching outputs; and all ten named axiom reports per side. The natural high-residue report lists `[propext]`; all nine remaining declarations list `[propext, Classical.choice, Quot.sound]`. No warnings or `sorryAx` occur in the retained logs.

`CompactSymbolicGraphDigits.graph_digits` is a theorem in an IΣ₁ model with an actual positive graph zero and positive witnesses, port inequalities, `p₀ ≥ 46`, positive `N`, the stated radix and repunit identities, both low- and high-symbolic-port equalities, the high-port split and `1 ≤ HP*v₀` as hypotheses. With `q = 1+v₀p₀` and `C = q−v₁−v₂`, it concludes `dig 67 C 0 = 1` and `dig 67 C k ≤ 3` for `k < 8807*N`. It derives the needed symbolic population, parity, high residue and bound; it does not discharge either retained graph-port equality or prove checker calibration, machine semantics or an iPRA endpoint. The parent's historical superseded-draft audit qualification, incomplete provider/axiom inventory, external package/dynamic ancestry and sampled-resource limitations remain.

To rerun this independent check from the repository root, use:

```sh
python3 -I -S -B Computability/DiophantineConsistency/reviews/compact44-symbolic-graph-join-independent-audit/audit.py 868493c860 9bc91a18e8a8159621c97eb24b20a09bb0c8da82d0931904a3cf2082849e59be
```

These are point-in-time checks of retained artifacts, not claims of continuous protection outside the protected run. The recorded Lean axiom sets describe metatheory and are not an inventory of object-theory axioms.
