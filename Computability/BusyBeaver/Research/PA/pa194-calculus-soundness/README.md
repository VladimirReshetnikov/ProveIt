# PA194 numerical calculus and scheduler

`PA194CalculusSoundness.initial_halts_iff_refutable` proves that the actual
initial PA194 command scheduler halts if and only if code 1 has a finite
derivation in the separate-diagonal numerical calculus defined by
`../pa194-derivation-compiler`. The forward direction uses a proved-top,
proved-cached-head, and proved-stack invariant for every command. The reverse
direction uses the finite derivation compiler and scheduler fairness. The
zero formula's derivation is constructed from the actual restricted
implicational basis; consistency is not silently assumed. The final theorem
prints `[propext, Classical.choice, Quot.sound]`.

This is a standard-natural-number Lean equivalence for this specific
numerical calculus. It does not identify that calculus with PA, translate PA
refutations, or formalize either implication in PRA/iPRA. The source tree
retains the pinned Python grammar-translation boundary documented in
`../pa194-source-tree`.

Run from the repository root:

```sh
Computability/BusyBeaver/Research/PA/pa194-calculus-soundness/check.sh
```

The script rebuilds the source, scheduler, compiler, and fairness prerequisites
in private tmpfs and checks the proof invariant and equivalence. The full
standalone fresh build has passed; both final modules also passed an independent
replay from the retained fresh fairness objects.
