# Supplying the packed word directly loses the ordinary input width

**The proposed 83-operation shortcut is not a valid replacement for the
universal86 construction.** It keeps F positive, but replaces the positive
raw slack alpha by a supplied positive packed word C. A canonical accepting
certificate at width N can then be reused for the different ordinary input
`x+N`, with all nineteen new witnesses positive and all eight factors equal
one. In particular, the valid fixed compiler for a singleton language acquires
a false positive. This is a full-zero construction, not just an off-zero
failure of a coordinate inverse.

The [source checker](complete86_marked_word_obstruction.py) and
[receipt](complete86_marked_word_obstruction.json) authenticate the actual
normalized [first-root86 parent](complete86_factored_first_root.md) and its
canonical compiler/Pell proofs. They expose the whole syntactic84 and83
sources solely for this obstruction. No new universal operation bound or
unrestricted lower bound is claimed. The established86 source stays unchanged.

## Two literal deletions and one shared-gap rewrite

The actual parent computes

```
u=q-F,
uZ=u-Z,
C_after_alpha=uZ-alpha,
ell=2d*x,
C=C_after_alpha-ell,
W=C-Z,
G=(q-1)*u+uZ.
```

The source names C and G are `marked_rhs` and `gap`. Alpha has just one
consumer, `C_after_alpha`, whose only consumer is `marked_rhs`. Supplying a
positive `C_word` in place of alpha and aliasing C to it removes the two
subtractions defining that chain. The intermediate full source costs
**84=48M+36A**. The old `uZ` is now used only by the gap. Replacing

```
(q-1)*u+(u-Z) = q*u-Z
```

and deleting the now private `uZ` subtraction gives **83=48M+35A**. The
ordinary input product `ell=2d*x` stays paid because the input Pell index
still uses it. Every main, first, input, strong, auxiliary, index, transport
and linear factor and the complete product-minus-one remain in the source.

Both sources retain nineteen supplied coordinates. The signed inverse is

```
alpha=q-F-Z-2d*x-C_word.
```

Two exact polynomial cut identities, followed by literal unchanged downstream
rows, prove the entire graph identity with the parent on that inverse over
arbitrary scalar assignments. The missing positive bound is substantial:
the old raw slack implies a width restriction on C and its marked input
power W. A positive C alone supplies no such upper bound.

## Start from a canonical complete accepting certificate

Fix a valid parent compiler for a recursively enumerable positive-input
language S, with all of its numerals fixed, and choose an accepted `x>0`.
Use the canonical positive completeness construction in the pinned
[fixed raw proof](../../1980/FIXED_RAW_UNIVERSAL_75_PROOF.md), then the
normalized strong and first-root constructions. It supplies a complete
positive zero with all eight factors one and

```
B=2^d, d>=4, q=B^N=2^t, t=dN,
e=2d*x+b, odd e>=3, W=2^e<q, C=Z+W,
R>=q^2, R=3 mod4,
X=2^R, Y=s*q^3, E=X*Y,
a=Y*(X+1), A=a+2, Delta=A^2-1, H=4a+3,
c=psi_A(R), D=chi_A(R).
```

Here N and t describe existentially chosen certificate data. They are not new
program numerals or additional circuit inputs. The actual asymmetric source
still uses `X=w*q`. All main/first/auxiliary coordinates are the actual positive
canonical coordinates of the parent; no new rank or divisibility theorem is
assumed for an arbitrary zero of the unsafe child.

Let K denote the fixed source `Kconstant`. The parent transport factor is

```
Nt=(K+X)*C+(q-F)-zplus*(q-1)=1.
```

Define for the fixed main parameter A

```
gamma_n=(chi_A(n)-a*psi_A(n)-2^n)/H.
```

These are integers, since their recurrence has integer initial values:

```
gamma_0=gamma_1=0,
gamma_(n+1)=2A*gamma_n-gamma_(n-1)+2^(n-1), n>=1.
```

In particular gamma_2=1 and the sequence is positive and strictly increasing
from index2. This follows by applying the recurrence to successive
differences. The canonical shared quotients are
`rho=gamma_e`, `sigma=gamma_R-gamma_e`; their sum is gamma_R. The proof uses
exactly this coupled interface, not an independent main quotient.

## Shift the ordinary input by one width

Put

```
x'=x+N,
e'=2d*x'+b=e+2t,
W'=2^e'=q^2*W,
C_word'=Z+W',
zplus'=zplus+(K+X)*(q+1)*W.
```

Because `W<q`, we have `e<t`. Hence `e'<3t<q^2<=R`, with strict middle
inequality for q=2^t>=16. In particular the new input exponent is still below
the old main Pell index. It is odd and at least3.

Keep every supplied parent witness except alpha, zplus, delta, rho and sigma.
Replace alpha's coordinate by the displayed positive C_word', use zplus',
and reconstruct just the input witnesses at e':

```
kappa'=psi_A(e'), mu'=chi_A(e'),
delta'=(kappa'-e')/Delta,
rho'=gamma_e', sigma'=gamma_R-gamma_e'.
```

The standard odd-index congruence `psi_A(e')=e' mod Delta` makes delta' an
integer; strict Pell growth at e'>=3 makes it positive. The gamma recurrence
and `3<=e'<R` make both rho' and sigma' positive integers. C_word' and zplus'
are positive by their displayed formulas. All fourteen other supplied
coordinates remain positive without alteration. The new supplied list is

```
Jrep,F,C_word,zplus,f,h,i,j,o,s,w,tau_root,eta,zeta,y_aux,Z,delta,rho,sigma.
```

No compiler numeral is changed. The ordinary input has changed to x'.

The complete factors can now be verified in their actual source order:

- The first, auxiliary, index, strong and linear factors use only unchanged
  supplied data and computed registers. In particular R depends on q,F,Z
  and the fixed masks, so it is unchanged. Each factor remains one.
- The main root remains `X+a*c+(rho'+sigma')H=D`, since the quotient sum
  is gamma_R. The main norm therefore remains one.
- The input factor computes `kappa'=e'+delta'*Delta` and
  `mu'=W'+a*kappa'+rho'*H=chi_A(e')`; its Pell norm is one.
- The transport factor remains one by the exact all-value identity

```
(K+X)*(Z+q^2*W)+(q-F)
  -[zplus+(K+X)*(q+1)*W]*(q-1)
 = (K+X)*(Z+W)+(q-F)-zplus*(q-1).
```

Thus every factor of the entire syntactic83 polynomial equals one on a
positive nineteen-witness tuple at x'. The same holds for syntactic84, since
its gap expression is identical.

The inverse raw slack is strictly negative:

```
alpha'=q-F-Z-2d*x'-C_word'
      =q-F-2Z-2d*x'-q^2*W<0.
```

This explains exactly which original domain condition is lost.

## A valid fixed compiler with a false ordinary input

Take the existing universal compiler for the singleton positive language
`S={1}`. Its canonical completeness theorem supplies an accepting parent
certificate at x=1 with some positive width N. The preceding construction
gives a complete positive child zero at `x'=1+N`, which is outside S.
The program and every one of its fixed numerals are identical before and
after the shift. No toy choice of masks is being substituted for a genuine
compiled program in this existence proof.

This refutes preservation of the parent's input language by this shortcut.
It does not assert that the changed source accepts every input for every
program, or that every possible83/84-operation universal representation is
impossible. It identifies input-width aliasing in these two literal sources.

## What the executable checks establish

The helper checks the actual private source consumers and emits both complete
live circuits, including every fixed-numeral product and finalizer gate. Its
two sparse coefficient identities prove the bound substitution and the gap
rewrite. Ninety-six signed graph comparisons, including rational assignments,
supplement that full algebraic proof. A separate exact coefficient check
proves the entire transport-compensation identity.

Four bounded Pell component cases verify both old and shifted input norms,
strict positive delta/rho/sigma, and the unchanged shared main root. These
are expressly components, not complete compiler-width zeros. The actual
canonical parent and its enormous auxiliary tower are not materialized;
the proof transports their existence from the pinned full completeness
theorem. It leaves those auxiliary values untouched.

Replay with the six authenticated predecessor files available under ROOT:

```sh
python complete86_marked_word_obstruction.py --root ROOT \
  --expect complete86_marked_word_obstruction.json
```

`--output FILE` writes a deterministic receipt. Optimized Python is rejected
and receipt comparison uses exact recursive types. This is a research CLI,
not a maintained unsafe compiler API. No historical author suite is rerun.
