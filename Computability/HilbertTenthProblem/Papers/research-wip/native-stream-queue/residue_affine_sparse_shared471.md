# Share control pairs back into the U21 prime selectors

The complete [source and receipt](residue_affine_sparse_shared471.json) cost
**471 = 175M + 296A operations**, six fewer than the
[one-program477 parent](residue_affine_sparse_shared477.md). The full polynomial
and every supplied coordinate are unchanged. The source retains **67 positive
witnesses**, ordinary positive input x, the single fixed program parameter
E=3^e, seven comparisons in the parent's convention, and degree **at most5091**.
Its certificate has **451 = 168M + 283A** operations. All471 rows and69 free
ports are live.

Five additions disappear by reusing paid control-state/target pairs inside
prime-selector prefixes. One multiplication disappears by reusing a paid
population prefix inside the current-control sum. These six edits work
simultaneously; the complete emitted schedule checks their dependency order.
They are exact identities without selector typing, positivity or a zero
equation. The separate universal84 bound remains unchanged.

## 1. Exact parent and unchanged interface

The immediate source is the complete array in
`residue_affine_sparse_shared477.json`. The new
[standard-library helper](residue_affine_sparse_shared471.py) authenticates
its entire trio and reads the array as inert data. No predecessor helper is
executed or imported. The original one-program interface remains literal:

    height_83 = program + input
    height_85 = height_83 + height_slack
    radix_86 = 64 * height_85.

Thus h=E+x+eta and B=64h; all three operations remain paid. No program-dependent
radix port, additional witness or altered fixed-numeral recipe is introduced.
The literal U21 transitions, input loader, prime/action masks, range bounds,
chronology, native kernel and finalizer are unchanged as polynomials.
The inherited ordinary-input theorem uses valid fixed E=3^e recipes.

A finite exact affine-expression search suggested these rewrites. Only the
six proved source identities below are claimed; this packet gives no global
optimality statement or negative result about other linear circuits.

## 2. Five existing pairs remove five additions

Write E_j=edgej_hat−1, without assuming these expressions have Boolean digits.
All five pairs in the middle column already have live paid producers in the
parent, used by the control expressions.

| Retained prime prefix | Reused paid pair | New single addition |
|---|---|---|
| `prime_selector_99` | `control_codes__target_class_35=E17+E28` | E16 + reused pair |
| `prime_selector_101` | `control_codes__duplicate_state_3=E30+E31` | prime_selector_99 + reused pair |
| `prime_selector_105` | `control_codes__duplicate_state_2=E18+E19` | prime_selector_103 + reused pair |
| `prime_selector_107` | `control_codes__duplicate_state_5=E20+E21` | prime_selector_105 + reused pair |
| `prime_selector_109` | `control_codes__duplicate_state_8=E24+E25` | prime_selector_107 + reused pair |

Each parent prefix used two additions to incorporate the same two terms.
The replaced definitions leave the five intermediate registers
`prime_selector_98`, `prime_selector_100`, `prime_selector_104`,
`prime_selector_106`, `prime_selector_108` dead. Each had only the corresponding
replaced prefix as a consumer. Delete those five additions.

The original pair producers remain paid and live in both their old control
consumers and their new prime consumers. They depend only on supplied edge
hats and their retained one-step shifts. They can therefore move earlier
without depending on any changed prime prefix. The successive dependencies
99→101 and105→107→109 are preserved, rather than individually checked and
then assumed safe in combination.

## 3. The paid population prefix removes one multiplication

The actual parent definitions include

    prime_selector_93 = E2+E3+E13 = G3,
    prime_selector_95 = E32+E33+E34 = G5,
    u21_grouped_J_0 = G3+G5,
    control_codes__current_multiple_9 = 2*G5,
    control_codes__current_positive_19 = G3+2*G5.

Replace only the last definition by

    control_codes__current_positive_19 = u21_grouped_J_0 + G5.

The new row is one addition, just like the old row, and has exactly the same
polynomial. Its old scalar product `control_codes__current_multiple_9` was
private to this consumer and disappears. The multiplier by2 was a paid
operation; the saving is one multiplication. The population prefix remains
paid and used in the whole selector sum, so no expression is treated as free.

The newly rescheduled prime-class producers still define the same G3/G5
values. The full dependency traversal confirms that this edit creates no
cycle with the five prime-prefix edits.

## 4. Complete source proof and paid ledger

The checker rebuilds the entire simultaneous graph from fresh row lists,
then traverses it from the actual output. Exactly the six named producers
are dead. No new register is introduced. Every other definition except the
six explicitly replaced rows is literal. The original parent array and
entire packet are checked to remain byte-identical in memory.

Each changed target is expanded independently through the actual old and
new ancestor cones as a formal affine polynomial in the36 raw selectors,
with each supplied hat represented as E_j+1. The coefficient vectors agree
exactly. A full expression interpreter binds those proved identities to the
actual supplied hats and compares every one of the471 retained registers,
including the complete output. Therefore, over every commutative ring,

    F471(E,x,witnesses)=F477(E,x,witnesses).

All72 native-prefixed rows, the six ordinary residuals and all20 finalizer
rows remain literal. In particular the identities are valid off the zero
set and at arbitrary signed inputs; no native positivity theorem is used to
justify an algebraic cut. Whole-polynomial equality gives an identity map
between the complete supplied positive zero sets and transfers the parent's
ordinary-input representation directly.

| Stage | M | A | Operations |
|---|---:|---:|---:|
| Parent certificate |169|288|457|
| New certificate |168|283|451|
| Unchanged finalizer |7|13|20|
| Complete new polynomial |**175**|**296**|**471**|

Counts are derived from the complete emitted array, including the moved
pair producers, all multiplications by fixed numerals, the positive-domain
input machinery and the full finalizer. The source audit checks unique
definitions, binary operand types, acyclicity, sequential availability,
unchanged69-port interface and complete liveness.

## 5. Degree bound and fresh evidence

The full identity already transfers the parent's bound5091. The new helper
also checks the exact main-norm cancellation and propagates a fresh bound
through the actual471 rows. Let a,c,X denote the computed native fields,
H=4a+3 and G=ga*H. The literal main norm is

    (X+ac+G)^2 − (a^2+H)c^2
      = X^2+2acX+2GX+2acG+G^2−Hc^2.

Twelve actual row definitions are checked before this expansion is used.
With every supplied port of degree1, the degrees of X,a,c,G,H are bounded
by308,374,67,375,374. The six displayed terms therefore have bounds
616,749,683,816,750,508. This gives816 for the norm instead of the naive882.
The eight native/repunit factor bounds are

    816,1900,442,65,1018,375,375,2,

which sum to4993. The largest ordinary residual has degree at most49, so
the final bound is4993+98=5091. Naive gate propagation gives5157 instead.
The bound also holds after fixing E; no exact degree is claimed.

The receipt saves the six complete affine identities, private-consumer lists,
all471 source rows, the unchanged interface, the small exact norm expansion
and the derived degree/cost data. Another32 signed modular source pairs and
four signed rational pairs verify every retained register. These finite tests
are off-zero algebra checks and do not materialize accepted histories or full
native Pell witnesses. The symbolic full-output identity is the basis of the
positive-zero claim.

The standalone helper binds its exact bytes into the receipt, rejects duplicate
keys and noninteger JSON number encodings, and compares canonical type-sensitive
JSON. All guards remain active under optimized Python. Fresh normal and
optimized exact receipt replays from `/` both pass:

```sh
u21_wip=/absolute/path/to/native-stream-queue
python3 "$u21_wip/residue_affine_sparse_shared471.py" \
  --root "$u21_wip" --expect "$u21_wip/residue_affine_sparse_shared471.json"
python3 -O "$u21_wip/residue_affine_sparse_shared471.py" \
  --root "$u21_wip" --expect "$u21_wip/residue_affine_sparse_shared471.json"
```

## 6. Pins and limits

| Inert dependency | SHA-256 |
|---|---|
| `residue_affine_sparse_shared477.py` | `21463ce43e33aea904401277940f83990e033018ab624d8367b11c7eee9c2b0f` |
| `residue_affine_sparse_shared477.json` | `3472269ef557bfbcb6dd2697f9a780990bb394d7e370cadb282f7b03a4cd3716` |
| `residue_affine_sparse_shared477.md` | `95c37d45ea3ca2d7e7d653173f22e9821ee85036abe3a345ec0c563348b8f2b9` |
| `residue_affine_sparse_control_codes.md` | `be133b5d93c082c3f3022e4b9990140ff3de71cf7202a7ba281a48e8c77d34da` |
| `native_binary_norm_units.py` | `1f088e43e60f068f2ca7c78a607f4cc5cd4ec34b7d2d5259c9ce545f74fdfee9` |

New helper SHA-256:
`8940d9c5b008bbe9d6ea210d938634afec1e59a76362b2c3a4aa25c53d460246`.
New receipt SHA-256:
`4732844a06fb9285d9fc57aa8dcd220e3664f965ec850393c830d2a453832ced`.

Only this default one-program coupled-product successor is emitted here.
No other historical source, alternative controller plan or two-program
successor is claimed. No repository or frozen predecessor file was edited.
The theorem concerns this concrete arithmetic rewrite, not optimality of the
U21 route or the complete universal polynomial problem.
