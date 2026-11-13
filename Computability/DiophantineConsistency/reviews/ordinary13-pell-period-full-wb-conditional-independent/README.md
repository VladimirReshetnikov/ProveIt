# Independent source review of the six-witness Pell WB proposal

The proposed six binder contexts, bound-term indices and inside-out `wb_exs_bt'` sequence match the inspected source formulas. The zero-coordinate replacement argument is mathematically valid at the displayed-body level. No concrete source-level index or premise mismatch was found. The hierarchy and replacement facts are all still **explicit hypotheses**, and neither quotation matching nor any Lean tactic has been elaborated.

Starting with `[m,a]`, adjoining witnesses in order `c,h,x,y,r,t` gives these environments before each witness and the intended bounds:

| Witness | Prior environment | Bound |
| --- | --- | --- |
| c | `[m,a]` | `2^(2*(a+2)*m)` |
| h | `[c,m,a]` | `2*m*c` |
| x | `[h,c,m,a]` | `2^(2*(a+2)*h)` |
| y | `[x,h,c,m,a]` | `2^(2*(a+2)*h)` |
| r | `[y,x,h,c,m,a]` | `x` |
| t | `[r,y,x,h,c,m,a]` | `y` |

The literal bound terms select these slots; in particular both final terms use `#1`, but they select different witnesses in different contexts. The nesting `bodyR=∃t finalBody`, then `bodyY=∃r bodyR`, and so on up to `∃c bodyC`, is in the right reverse order for `wb_exs_bt'`. Each application receives the corresponding explicit `Σ₁` hierarchy, replacement and body-`WB` premise. Whether the separate quotation `periodDef.val` is definitionally equal to `∃c bodyC`, and whether `wb_auto` and the proposed providers elaborate, remain unchecked.

For `c>0`, natural arithmetic makes `c²≥1`; the displayed equations `x=1+c²r` and `y=t*c²` give `r≤x` and `t≤y`. At `c=0`, they instead give x=1 and y=0 while allowing arbitrarily large original r and t, so a same-witness bound is false. Replacing r or t by zero preserves those two equations and the other displayed conjuncts, which do not mention the replaced witness. The generic `Replacement` premise permits exactly such a replacement. These are informal model-arithmetic obligations, not discharged theorems in the draft.

The proposed c, x and y bounds additionally depend on extracting the represented-coordinate evaluations and proving the source-only growth estimate; the h bound depends on extracting its literal equality. All six `Replacement` implications and all six hierarchy facts remain open despite the plausible calculations. Even a checked `WB M` result would quantify a monotone model function and would not alone provide a single uniform primitive-recursive bound across models, an evaluation bridge, or an iPRA proof-existence theorem.

The independent checker pins the proposal and interfaces, reconstructs all six source contexts and nested arities, checks the explicit hypotheses and call order, and tests the positive- and zero-coordinate arithmetic on finite controls. It does not inspect Lean's generated AST or execute the proposed proofs. From `Computability/DiophantineConsistency`:

```sh
python3 -I -S -B reviews/ordinary13-pell-period-full-wb-conditional-independent/check.py | cmp - reviews/ordinary13-pell-period-full-wb-conditional-independent/receipt.json
```

No Lean, build, staging, provider audit, axiom report or iPRA derivation was run.
