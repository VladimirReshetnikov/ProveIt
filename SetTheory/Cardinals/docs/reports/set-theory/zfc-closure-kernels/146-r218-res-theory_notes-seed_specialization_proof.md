# Independent seeded specialization audit

## 1. Finite inductive invariant

`audit_abstract_certificate.py` reads the exact source and the proposed invariant as data. It independently resolves the structured source's branch targets, then checks the initial register tuple `(3,0,0,0,3,0,0,0,0)` and every enabled abstract transition. It does not invoke or trust the original worklist implementation.

Each abstract register is a union of `{0}`, `{1}`, `{2}`, `{3}`, and `{n:n>=4}`. A source location denotes the Cartesian product of its nine register sets; `null` denotes the empty set. Increment maps the first four cells forward and retains the tail. A positive decrement maps the tail into `{3} union {n:n>=4}`; a zero decrement refines its tested register to `{0}` on the zero branch. Thus every transfer is sound for all natural register values. Inclusion at all finitely many edges and inclusion of the initial tuple imply, by ordinary induction on execution length, inclusion of every reachable configuration.

For source SHA-256 `837e92d7b1c107330f160f654f6c36ff0b03dfbf6bc2b89c6f782eb7db4c4ce7`, the independent check passed 6,161 enabled edges. Locations 4604, 4719, and 4720 have empty invariant; decrements 4603 and 4718 are always zero. At location 4598, the entry to the halting comparison, register 6 is zero while register 5 is unconstrained.

Independent fixed-point calculations with cells `{0},...,{k-1},{n>=k}` for `k=8,16,32,64` found the same dead locations and zero tests, and no always-positive decrement. These are bounded abstract-domain searches, not a completeness result about all invariants.

## 2. Restricted halting comparison

Write `D_i` for decrement register i with a zero break; `I_i` for increment; `C_j` and `B_j` for structured continue and break; and `(A,B)` for the binary source constructor. Set

```
Clear = (D_5,C_1)
Tail  = (D_5,(Clear,B_1))
A     = (D_6,((D_5,C_2),(I_5,(D_6,C_2))))
Old   = (I_6,((A,Tail),Halt))
New   = (D_5,(Tail,Halt)).
```

Assume register 6 is initially zero and register 5 initially `x`.

In `Old`, `I_6` makes register 6 equal to one. The first decrement in `A` makes it zero. If `x=0`, the zero branch of `D_5` bypasses its continue and the next block sets register 5 to one; its zero `D_6` exits, so `A` returns `(r5,r6)=(1,0)`. If `x>0`, `D_5` decrements to `x-1` and its `C_2` causes another entry to `A`. The now-zero `D_6` returns normally. Thus `A` returns `(x-1,0)` in this case. These are its only cases.

`Tail` returns normally exactly when its input register 5 is zero. When its input is positive, it decrements once, clears the remaining value with `Clear`, and returns the break that skips `Halt`. Consequently `Old` halts exactly when `x=1`; otherwise it returns normally. All its loops terminate because their loop counters strictly decrease. At both its normal and halted exits, registers 5 and 6 are zero; all other registers are untouched.

For `New`, `x=0` makes the first decrement exit the whole block normally. For `x>0`, its first decrement leaves `x-1` and passes control to `Tail`. As above, it reaches `Halt` exactly when `x=1`, and otherwise clears the remaining value and returns normally. Its postconditions are identical to `Old`.

The actual old source subtree also has a common suffix `Rest`: `(I_6,(((A,Tail),Halt),Rest))`. The new subtree is `(New,Rest)`. Literal checking confirms that the two copies of `Rest` are identical and that `Rest` has no escaping break, escaping continue, or halt. This closure matters: deleting an enclosing source constructor would otherwise change the destinations of some continues. The remainder of the complete source is byte-for-byte the same tree outside this replacement.

The invariant establishes `r6=0` at every visit to the old comparison, not just on its first visit. Replacing each such terminating block by its equivalent block therefore preserves the complete seeded execution up to the number of primitive instructions used. In particular the two source programs halt from the seed in exactly the same circumstances. This argument uses all-natural local reasoning plus an inductive invariant; it does not infer unbounded correctness from sampled runs.

`halt_specialization_audit.py` pins the literal old and new patterns, checks the common suffix and the unchanged exterior source, and confirms the entry invariant. Its separately written structured interpreter checks 257 finite inputs only as supplementary regression evidence. The new source SHA-256 is `fc3b722445cf800d0a565a53fbc66cbe13347cf9a3ff6b35088390a71e9b3e7c`. Correct execution by a particular binary table remains a separate obligation.
