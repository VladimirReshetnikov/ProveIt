# Canonical input blocks the old shared83 field and forces a unique affine repair

The accepted non-dyadic shared83 construction does not transfer to the no-wrap branch of direct-X83 by restoring its input offset. Two exact obstructions intervene: its constructed inputs exceed the canonical width, and its field choice fails the retained transport equation. Within the natural repair class `F=K*Z+lambda*W`, with nonnegative integer lambda and the old resonance `2^R=2^u modulo(q-1)`, the unique possible choice is

```
lambda=K+Z+W,       F=(K+W)*(Z+W).                (1)
```

The resulting positive transport quotient is exact, but positivity now requires W²<q. These are all-size statements about authentic outer interfaces. They do not construct a direct-X83 zero, settle q³|Y for the canonical half-binomial, or change any paid operation count. The repair gives a specified next arithmetic problem instead of transferring the old odd-prime proof without its hypotheses.

## 1. Full-zero premises and the exact general transport condition

On every positive no-wrap zero of the unchanged direct-X83 source on its inherited original compiler slice, the accepted proofs give

```
B=2^d, q=(B-1)*J+1 even, q>=16, m=q-1,
u=2d*x+b, W=2^u<q, X=2^R, R>u, R=3 modulo4,
C=q-F-Z-alpha-2d*x=Z+W,
F,Z,alpha,x,K>0,
R=(q^2-Z-qF)*(q^2-1)+(MC+q*MF_source)*J,
(K+X)*C+q-F-tau*m=1.                            (2)
```

Here x is the original positive ordinary input, tau is the supplied positive unsheared transport quotient, K is the unchanged fixed `Kconstant`, and `MF_source=MF_native+B-1`. None is a new uncharged source port. The first-index no-wrap proof supplies the transport sign +1; the congruence below is not inferred from a factor with unknown sign.

The exact general transport condition is

```
m divides (K+2^R)*C-F,
tau=1+((K+2^R)*C-F)/m.                           (3)
```

This is not the sheared shared83 formula with X/q in place of X. Because q is even, m is odd, and both X and W are units modulo m. Also the literal positive slack yields

```
q=F+2Z+W+alpha+2d*x,       0<C<m.                (4)
```

No native Boolean interpretation of C or F is used in this note.

## 2. The two direct transfers of the old field both fail

The old shared83 family has `C=Z`, `F=KZ=KC`, W=0, and uses `R-u` divisible by a period of2 modulo q-1. Restoring W=2^u makes C=Z+W. There are two natural readings of keeping that old field rule.

**Keep F=KC.** Equation(3) would give m dividing X*C. Since gcd(X,m)=1, this gives m dividing C, contrary to 0<C<m. This obstruction needs no resonance assumption: F=KC is impossible at every canonical no-wrap direct-X83 zero.

**Keep F=KZ and the old resonance.** Suppose

```
X=W modulo m.                                    (5)
```

Then (3) gives

```
0=(K+W)*(Z+W)-KZ=W*(K+Z+W) modulo m.
```

After cancelling the unit W, m must divide K+Z+W. But (4) with F=KZ gives

```
m-(K+Z+W)=(K+1)*(Z-1)+alpha+2d*x>0.
```

Thus `0<K+Z+W<m`, a contradiction. This rules out the same resonant transport recipe at every positive input; it is not an asymptotic or diagnostic-numeral claim.

## 3. The unique nonnegative W-multiple repair

Assume only the displayed positive outer data, (5), and the natural repair class

```
F=KZ+lambda*W,       lambda a nonnegative integer. (6)
```

The auxiliary lambda is a proof parameter specifying this class, not a supplied circuit witness. Write S=K+Z+W. Then

```
m-S=(K+1)*(Z-1)+lambda*W+alpha+2d*x>0,
0<S<m.
```

Also lambda*W<=F<q=m+1. Since W>=2 and m>1, this implies `0<=lambda<m`. The transport congruence is now

```
W*(S-lambda)=0 modulo m.
```

Cancelling W and using the two strict representative bounds forces lambda=S exactly. This proves (1). There is no freedom to add a positive multiple of m: such a lambda violates the original slack.

Conversely, set F=(K+W)(Z+W), retain (5), and suppose the literal alpha from (4) is positive. Then the positive integer

```
tau=1+(X-W)*(Z+W)/m                              (7)
```

satisfies the exact transport equation. Integrality follows from (5); positivity follows from R>u. Substitution shows the transport value is `(X-W)*(Z+W)+q-tau*m=1`. Thus (1) and (7) are necessary and sufficient for transport within class(6) and resonance(5), subject to the stated positive slack.

In particular `q>F=(K+W)(Z+W)>W²`. This conclusion is stronger than the canonical input width W<q. It holds only in this specified repair class, not for every direct-X83 zero.

## 4. The old radix shapes and an exact next congruence

For the previously used shapes, write Q=B^n=2^D, D=dn, n=1 modulo4:

```
PLUS:  q=Q*(Q+1)/2,    period L=2D*(D-1),
MINUS: q=Q*(2Q-1),     period L=2D*(D+1).         (8)
```

The accepted pairwise-factor argument proves `q-1 divides 2^L-1`. Therefore `R=u modulo L` is sufficient for (5), though not asserted necessary. The branch choice from the old theorem was made for its old slope involving K. This note does not assume that choice solves the new congruence involving K+W.

For either shape q<2^(2D+1). Canonical W=2^(2dx+b)<q, with b>=1, implies x<=n-1: if x>=n then u>=2D+1, impossible. The old basic family chooses x>=n, and its stronger source-coupled/growing-selector versions choose x>=5n. Their actual input tuples cannot be retained when setting e=0. This is an input-domain mismatch even before the transport contradictions of Section2.

In the repaired class q>W² and q<2^(2D+1) imply u<=D. Since b>0 and n is odd,

```
x <= (n-1)/2.                                    (9)
```

To state the genuinely changed finite problem, fix an actual compiler, a choice in(8), and a positive input x. Put W=2^(2dx+b), Kc=K+W and

```
A0=q^2*(q^2-1)+(MC+q*MF_source)*J,
Ac=A0-q*Kc*W*(q^2-1),
Gc=(1+q*Kc)*(q^2-1),
R(Z)=Ac-Gc*Z,
S=q-(Kc+1)*W-2d*x.
```

These are ordinary proof expressions obtained by substituting (1) into the literal packed index; no circuit is being re-costed. Exact resonance and slack become

```
Gc*Z=Ac-u modulo L,
(Kc+2)*Z<S,           Z>0.                       (10)
```

Let g=gcd(Gc,L). The congruence is solvable precisely when g divides Ac-u. When it is solvable, let Z0 be its least positive solution modulo L/g, taking Z0=L/g for residue zero. A positive solution satisfying the slack exists precisely when `(Kc+2)*Z0<S`. This is the ordinary exact linear-congruence criterion; it is not an uncharged Diophantine algorithm.

The parity requirement is visible as well. In(8), q is0 modulo4, J is1 modulo4 and the authentic MC is2 modulo4. Hence R(Z)=Z+2 modulo4. Both L in(8) are divisible by4. Combining the sufficient resonance R=u modulo L with R=3 modulo4 therefore requires u=3 modulo4, or **x odd**, since b and d are1 modulo4. For an odd x, every solution of the congruence in(10) automatically has Z=1 modulo4. This is a restriction of this sufficient-period construction, not a new universal parity statement about ordinary input.

There is a useful actual-recipe simplification at the prime5. The fixed compiler imposes `2DC-DR!=0 modulo5`, and B=2 modulo5, so `2K=2DC-DR!=0 modulo5`. For odd x, W=3 modulo5. In the PLUS shape q=3 modulo5, whence

```
Gc=(1+3*(K+3))*(3^2-1)=4K!=0 modulo5.            (11)
```

Thus the repaired PLUS congruence is invertible at the entire5-primary part of L for every authentic fixed compiler in this recipe. The old split according to K was for a different field and is unnecessary at that local prime after the repair. Other prime divisors of L, the positive interval and (12) remain unresolved; local invertibility is not a full construction.

Even a successful(10) does not prove a full zero. One must verify all remaining authentic packed-index and mask/repunit hypotheses and, decisively, the canonical cubic scale

```
q^3 divides Y_R,
Y_R=(1/2)*sum_(j=0)^((R-1)/2)
          binom(R-1,(R-1)/2+j)*(2^R)^j.           (12)
```

At every odd p dividing q, the canonical X=2^R is a p-unit. The old shared83 reduction to three terms used v_p(X)>=v_p(q), and its input lifting varied `X=2^R-2^u` while keeping R fixed. Both facts fail here: with R fixed, changing x does not change canonical X or Y_R. Thus the old odd-scale completion theorem supplies no proof of(12) for repaired canonical data.

## 5. Retained failures, scope and an open alternative

**Review remark 1 (the old offset family is not a canonical counterexample).** The proposed transfer was to keep the successful shared83 non-dyadic family and replace W=0, X=2^R-2^u by W=2^u, X=2^R. Keeping its constructed x already violates W<q for both old radix shapes. Keeping F=KC fails (3) even without resonance; keeping F=KZ and the old resonance fails Section2. The exact repair(1) avoids that transport contradiction but changes the index polynomial and does not inherit the old odd-scale theorem. These failures do not refute direct-X83 or all canonical non-dyadic constructions. The previously reviewed q=54 weak-kernel example remains a different, explicitly noncompiler diagnostic.

**Open question 1 (root's short-period alternative).** Root suggested keeping the compiler B fixed and taking `C0=B^n`, `k0=B-1`, `m=1+C0+...+C0^(k0-1)`, q=m+1. Then m is odd and divisible by B-1, while q=2 modulo C0 and q>2, so q is even nondyadic. Also m divides `2^(dn*k0)-1`; its available period is linear in n, hence logarithmic in q for the fixed compiler. These elementary identities offer another outer arithmetic host. No compatible packed R, positive repaired field/slack, canonical cubic divisibility, or full compiler zero is asserted for it. In particular a short period alone does not prove the remaining half-binomial condition.

## 6. Binding and evidence limits

The companion JSON pins this note and its dependencies, records exact read spans, and binds the literal direct-X outer rows as inert data. The new arguments are the transport obstruction, unique nonnegative repair, positive quotient and width bound. The no-wrap input recovery, R=3 modulo4, original compiler masks, old family existence and its old odd-scale proof remain inherited at their explicit scopes.

No source row, fixed compiler numeral, positive-witness interface or ordinary input interpretation is changed. No supplied, frozen, archived, predecessor or copied helper/program is executed or imported, no saved source array is evaluated, and no complete native tuple is materialized. Only fresh metadata and handwritten scalar identities, if recorded in the companion, may run before freezing. No repository or Git mutation is made. This is a bounded arithmetic boundary and exact proposed repair class, not a paid compiler construction or universal-operation improvement.
