# The dual-rho6 gap and measured repairs

The frozen252-state candidate is still experimental. Replacing old rho6 by
its familiar dual is not automatically conservative for the actual relative-
falsity calculus. The general refutation-equivalence statement with arbitrary
common extra axioms is in fact false. The counterexample below concerns that
general calculus transformation; it is **not** a countermodel to the candidate's
particular C/G bundle theory.

## Exact formulas and source boundary

Write `A→B` for the actual coded implication, `Q_a A` for universal
quantification and `F=1=Rel(0,0)`. The candidate uses

```
N A = A→F
E_a A = N(Q_a(N A))
old(a,B)  = E_a(Q_a B) → B
dual(a,B) = B → Q_a(E_a B).
```

The common logical rules are truth0, modus ponens, theorem generalization,
rho8 `((C→U)→A)→((A→C)→(B→C))`, rho2
`Q_a(B→C)→(Q_a B→Q_a C)`, and rho4
`Q_a Q_b C→Q_b Q_a C`. Membership vacuity is a component of the actual gated
bundle, with gate `c≠a,b`; it is not an additional ungated runtime row.

Read-only reference sources are the pinned upstream
`ZF/m254/coq/logic/Thm254.v`, `Comp_Prop254.v`, `CD254.v`, `Wff254.v` and
`Sound254.v` under `lib/jeff-busy-beaver-zfc254`. The upstream commit is
`297ab8df7e5de329605c3875b4934643b371a5e3`; CD254's source SHA-256 is
`898b6498cc50b81f465c2cac72fcfe1bb5eaf8e4af91359a02b18906202a8a4a`.
Jeff supplies the original Coq verification; no Coq code was executed here.
Its107 condensed-detachment certificates derive K, S and Peirce from rho8.
`Comp_Prop254.v:59–67` then uses old rho6 to prove `F→B`, and `:69–76`
uses that explosion theorem for relative double-negation elimination.

With ordinary classical falsity, old and dual are equivalent schematic
presentations: apply old to `¬B`, contrapose and eliminate double negations.
The actual code uses a membership atom instead of primitive false. Quantifier
label0 can capture that atom. The98 Boolean tests in the generator assume
ordinary false and do not prove the code-calculus replacement correct.

## A concrete logical obstruction

Use two worlds `w,v`. Let Q0 use accessibility

```
w sees w and v; v sees only v.
```

Every Qn for n>0 is the identity. Let

```
            w       v
F=Rel00     false   true
A=Rel01     true    false
```

All other membership atoms are constantly false. Implication is material
implication at each world, and the displayed relative N/E definitions are
used literally.

Every dual instance is globally valid, for every two-world truth assignment
to B. For a>0, it is `B→((B→F)→F)`. For a=0, at v the existential is true
because F is true; at w, if B is true, that same w witnesses the relative
existential needed at w, while the existential needed at v is already true.
Rho8 is an implicational tautology; rho2 is the usual box distribution;
rho4 holds because the only operators are Q0 and identities. MP preserves
global validity, and GEN does too. All freshly gated atomic membership-
vacuity formulas are also valid: c>0 uses an identity, while c=0 is fresh
only for an atom having neither index0, hence a constant atom here.

Put `DN_F B=(B→F)→F`. Then `DN_F A` is true at both worlds, so its GEN is
also globally true. But `DN_F(Q0 A)` is false at w: Q0 A and F are both false
there. Thus relative-DN transport through GEN is not an admissible rule of
this logic. Deriving `F→Q_a F` from dual at B=F does not fix this obstruction.

There is also a generic refutation counterexample. Give both calculi the
same additional axioms

```
Γ = { DN_F A, (Q0 A→F) }.
```

Both Γ-formulas are globally true in this model, so the dual calculus with Γ
cannot derive F, which is false at w. The old calculus derives explosion
`F→B`: from F, K gives `E_a(Q_a B)`, and old rho6 gives B. Explosion and
Peirce give relative DNE. It therefore derives A from Γ's first axiom, Q0 A
by GEN, and F by Γ's second axiom. This refutes generic refutation equivalence
for arbitrary common theory extensions. No assertion here says that Γ occurs
in, or is derivable from, the actual C/G bundle theory. The later finite-sort
model described below independently establishes nonrefutation for both actual
reduced variants; it rules out their proposed consistency calibration.

An explicit explosion schema repairs the specific classical-logic issue:
with `F→B` for every code B, relative DNE is derivable. GEN/rho2 then lift
double-negation equivalence through quantifiers, so dual and old schemas
can be interderived even at binder0. This argument has not yet been exported
as a Lean theorem about the actual code calculus. Putting explosion inside
a relative conjunction is not a repair: when F is true every such conjunction
is already true, so extracting its components would assume the very DNE/
explosion principle being sought.

## Measured repair search

`calculus_repair_search.py` keeps the252 generator untouched. It reuses the
same pinned backend and checks macro expansion before/after sharing. A lane
tries every logical-row order, every C/G/V order and both conjunction
associations. The EFQ lanes emit a separate ungated `F→payload` row.
Swapped-tag measurements retag after the same sharing pass and charge the
F2 constructor and NIP-target changes.

| Lane | Variants | Minimum working states |
| --- | ---: | ---: |
| Old rho6; Imp0/Rel1/All2, base3 | 288 | 254 |
| Old rho6; Imp0/Rel2/All1, base3 | 288 | 255 |
| Dual rho6 plus separate F→B | 1440 | 255 |
| Dual rho6 plus separate F→A | 1440 | 254 |
| Dual rho6 plus separate F→C | 1440 | 254 |

The retained original-rho6 best order is8,2,4,6 with bundle `V∧(C∧G)`.
The best A/C-explosion order starts with EFQ, then8,2,4,dual6, with the same
bundle. These are selected-family compiler measurements, not global lower
bounds or verified consistency-machine results. The ordinary old-rho6 route
avoids this new logical-row replacement gap, but still needs the equality-free
theory calibration and exact changed-compiler simulation.

Reproduce all lanes offline (generated named tables remain in scratch):

```sh
uv run --no-project python Computability/BusyBeaver/Research/ZFC/calculus_repair_search.py \
  --scratch /tmp/zfc-calculus-repair \
  --lanes old-base3 old-base3-swapped dual-efq-b dual-efq-a dual-efq-c \
  --output-evidence /tmp/calculus-repair-results.json
```

`calculus-repair-results.json` records each distribution, minimizer, best
named-table hash and source-script pins. The named outputs still have the
public backend's undefined `1.inc/read1` row; they are not presented here as
new total standard machines. The frozen252 table and its audits remain
unchanged. No calculus/equiconsistency or end-to-end machine theorem is
claimed by these search results.

Later intake provides a [finite-sort model](typed_countermodel.md) of the
actual reduced C/G bundle with **both** quantifier rows and target false.
Thus both unchanged abstract variants fail as consistency searches, independent
of this generic replacement counterexample. Their literal-table consequence
remains conditional on compilation correctness. Repair lanes that add further
axioms must be assessed separately; eliminating this model alone would not
establish their completeness.

