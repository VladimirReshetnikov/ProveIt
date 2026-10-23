# Checked sparse signed-borrow decoder

[`SparseBorrowCarry.lean`](Lean/DiophantineConsistency/SparseBorrowCarry.lean)
proves the sparse `+1` decoder used by the degree-separated source. Its
polynomial theorem is `tau_polynomial_iff`. For `B=2^t`, `t>=2`, a finite set
of targets below `n`, and `p : Polynomial ℤ`, it assumes

```
p.natDegree<n,
|p.coeff i|<B/4   for every i<n,
0<=J=2*p.eval B+sum(target q) B^q.
```

It proves precisely

```
tau 2 J.toNat ((B-2)*sum(target q) B^q)=0
  iff every target coefficient of p is zero.
```

The finite-word theorem `tau_sparse_iff` uses the convenient equivalent
sufficient magnitude condition `4*abs(h_i)<B`; the polynomial wrapper accepts
the stated strict quarter-base bound directly. Targets may include zero and
the finite-word statement permits an empty word and empty target set.

The proof constructs a borrow sequence by a sign test. It begins at zero;
each next borrow is `-1` for a negative incoming raw digit and zero otherwise.
The normalized digit is

```
d_i=2*h_i+delta_target(i)+borrow_i-B*borrow_(i+1).
```

Every borrow is explicitly `-1` or zero. The coefficient bound proves
`0<=d_i<B`. The identity

```
sum(i<n) d_i*B^i+B^n*borrow_n=sum(i<n) raw_i*B^i
```

then telescopes. The finite normalized word is below `B^n`, so nonnegativity
of the raw value excludes an outstanding final borrow and proves exact
word equality. Thus no signed integer is silently interpreted as a digit
word, and no higher coefficient is discarded by the polynomial wrapper.

At a target the raw digit is `2*h_i+1+borrow_i`. Its normalized digit is
below two exactly when `h_i=0`, for either possible incoming borrow.
The checked binary mask lemma with parameters `k=1` and `K=t` equates that
range with avoidance of `B-2`. The checked base-word theorem combines all
cells into one carry test. This argument does not add a dense half-base bias.

Regression checks cover a negative lower coefficient whose borrow makes a
zero target digit zero, both signs of a nonzero target coefficient, a target
at zero, and the full polynomial theorem for `X^2-1`. All definitions and
proofs contain no `sorry`, new axioms, or selected existential data. This
module proves the numerical decoder only; source coefficient bounds,
positivity of its specific word, calibration, and machine semantics remain
separate obligations.
