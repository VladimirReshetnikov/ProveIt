# Independent logical-seed review for the scanner-sharing 217 candidate

**Current physical status:** the scanner deletion was rejected by its arbitrary-clean-frame primitive audit. This note proves only that its observed clean seed is logically admissible.

## Exact reviewed seed

At a clean source-command root, the proposed complete bootstrap has logical registers

```
[np,tw,ws,ac,d,h,s1,s2,pl] = [4,3,0,0,3,0,0,0,0].
```

This note verifies the logical admissibility of that vector. It does not itself
verify the binary bootstrap, frame geometry, scanner patch, or primitive runtime.
Those are separate obligations. The source is the unchanged accepted K218 source.

The native code `3` is **E(0,0)**. It is not `I(0,0)`, which equals native truth `0`.
The exact Code254 constructors are `I(a,b)=4P(a,b)`, `R(a,b)=4P(a,b)+1`,
`Q_a b=4P(a,b)+2`, and `E(a,b)=4P(a,b)+3`, with `P(0,0)=0`.

## Equality reflexivity is a theorem of the retained calculus

Write `F=1`, `N A=I(A,F)`, and `Ex_i A=N(Q_i(N A))`.
The existing `KEqCodes222.refl222` proves `C222(E(x,x))` for every natural x.
For completeness, its ordinary derivation is short once the inherited K/S
basis is available:

1. Set `r=R(x,x)` and `X=E(r,x)`. The retained merged equality row at
   `(x,x,r)` is `X -> (X -> Q_r E(x,x))`.
2. Propositional contraction yields the closed theorem
   `X -> Q_r E(x,x)`.
3. Closed-theorem generalization, rho2, and intuitionistic contraposition
   give existential monotonicity. Applying it to step 2 gives
   `Ex_r X -> Ex_r(Q_r E(x,x))`.
4. Rho1 at `(r,x)` gives `Ex_r X`.
5. Rho6 at `(r,E(x,x))` gives `Ex_r(Q_r E(x,x)) -> E(x,x)`.
6. Two modus ponens steps finish.

At x=0 this proves code3. No model existence, consistency assumption,
unrestricted formula substitution, quantified stability, or extra axiom is
used. K/S are the already derived native consequences of unrestricted rho8.
All generalizations occur on closed theorems.

## Soundness from the proposed seed

The exact `Enum222.Inv(s)` is

```
C222(s.tw) and C222(s.h) and Good(s.ws),
```

where `Good` says that every successive head of the Cantor-decoded stack is
derivable. `Good(0)` follows because repeated unpairing of zero gives zero and
native truth0 is an axiom. Thus the proposed vector satisfies the invariant:
`tw=3` by equality reflexivity, `h=0` by truth, and `ws=0` by `good_zero`.
There is no restriction on `np`, `d`, or `pl` in this invariant.

The existing `Enum222.step_inv` preserves this invariant for every command.
In particular, successful MP uses the theorem in the cache and the current
theorem, DROP pushes a theorem, NIP reads a theorem from a good stack, and AX
pushes the retained native axiom instances and generalized cache theorem.
Only NIP halts, and it halts only when the cached theorem is F. Therefore
halting from this seed implies a finite C222 derivation of F. This is an
induction on finite executions, without assuming Con(ZFC).

## Completeness with candidate cutoff four

The maintained `Enum222.complete` is stated for the zero seed, so invoking
that theorem alone would leave a gap. The arbitrary-cutoff extension is
explicit and uses only its existing contracts.

For any C222 derivation of F, `Enum222.build` provides a finite command list
`p` such that, for **every** current formula T and stack S, starting `p` at
`(tw,ws,d,h)=(T,S,0,0)` either halts or returns `(F,S,0,0)`.
The `Contract` quantifier does not require `Good S`.

For any U, prepend `START_U=AX(c=0,x=1,y=1,u=U)`. Its literal `cstep_ax`
equation resets d and h to zero from every working tuple. Then run p, followed
by `[DROP(0),NIP(0),NIP(0)]`. If p has not already halted, the suffix pushes F,
reads F into the cache, and halts. Thus the entire block halts from every
working tuple, including arbitrary previously accumulated stack contents.

Let R be one plus the candidate code of the fixed nonempty suffix
`p ++ [DROP(0),NIP(0),NIP(0)]`. The complete block's candidate number is

```
N_U = P(3, P(1, P(1, P(U,R)))).
```

Cantor pairing is at least either component, so `N_U >= U`. Choose U=4.
Then the successful candidate is at least the initial cutoff4. Every
positive proof-list pointer strictly decreases until zero unless execution
has already halted (`step_pl`, `drain`); from a zero-list boundary the next
candidate counter increases by exactly one (`step_start`). Therefore, if
the run has not already halted, it eventually executes candidate N_U and
halts there. The current additive value d=3 presents no obstruction because
START_U resets it before p.

This proves for this seed, and more generally every clean root seed with a
derivable current formula/cache and good stack,

```
enumerator halts <-> C222 F.
```

## Exact source connection and proof status

`L2Root219.toAS` maps an enumerator state to the nine registers as
`[np,tw,ws,0,d,h,0,0,pl]`. Therefore the proposed vector is exactly
`toAS( pl=0,np=4,tw=3,ws=0,d=3,h=0 )`.
`L2Root219.root_step` and `iter_iff` are universal in that enumerator state;
they do not assume the historical bootstrap vector. The accepted K218
ordinary source/CFG correspondence is also for all initial register vectors.
Combining these existing source contracts with the proposed candidate's
separately established complete bootstrap/runtime bridge is legitimate.

The retrieved declarations were inspected at ProveIt commit
`704b87442afbd571833a628cd558f1d207fd8b2f`:

- `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/Code254.lean`;
- `KCode222.lean`, `KEqCodes222.lean`, `Enum222.lean`, and `L2Root219.lean`
  in the same directory;
- `SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/146-r218-res-src218-general_seed_lemma.md`;
- `Computability/BusyBeaver/Research/ZFC/k217-protected-tail-seed/source-contracts.md`.

The ordinary arbitrary-cutoff argument is independently rechecked here.
It is not a claim that a new arbitrary-seed Lean theorem was compiled.
The equality fact is an existing exact theorem (`KEqCodes222.refl222 0`),
and the accompanying small executable certificate uses only K/S and the
retained rho1, rho2, rho6, G rows. No protected-tail theorem is needed for
the proposed clean empty stack.

Once the physical obligations pass, the inherited finite-refutation
calibration of C222 with ZFC gives the requested equivalence in ZFC.
The seed creates no new mathematical assumption or consistency-strength gap.
