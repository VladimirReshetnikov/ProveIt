# Selecting the input interface for a ternary counter compiler

The cheap ternary ripple does not justify selecting a two-counter machine
with the raw query initially stored in one counter. The input interface
can change the computational power of that model. A separate read-only
digit stream is a viable alternative, provided its consumption is included
in the arithmetic certificate. No operation bound is established here.

## Two counters initially holding x and zero

[Ibarra and Tran, *A note on simple programs with two variables* (1993)](https://www.researchgate.net/publication/220152440_A_Note_on_Simple_Programs_with_Two_Variables)
study deterministic machines with increment, decrement and zero tests,
no input tape, and the input initially in one counter. Their Theorems 3.2
and 3.3 exclude the primes and the perfect eth powers, for each fixed
e>=2, from the sets recognized by this model. Section 1 distinguishes
that limitation from universality with exponential input encodings and
from three-counter machines on raw numeric inputs.

Consequently an instruction to "let the two-counter program convert the
raw input itself" cannot supply a general raw-input universal interface.
This statement concerns that deterministic model and initial condition.
It is not a theorem about machines with an input tape, nondeterministic
machines, or two arbitrary nonzero initial counters.

## Two counters with a finite input stream

[Machida and Shibakov, *Stack and register complexity of radix conversions*](https://arxiv.org/pdf/1604.08878)
define a two-counter machine with input commands and epsilon computation
between successive symbols. Proposition 1 uses prime-exponent storage to
process digits while retaining encoded intermediate values. Proposition 2
gives an ordinary-value decoder for most-significant-digit-first input.
Theorem 3 excludes the corresponding online decoder in the opposite order;
its requirement that the end marker leave the counters unchanged matters.
The [published article](https://doi.org/10.1016/j.tcs.2019.04.020) appeared in 2019.

Use encoded virtual counters (n,k)=(0,0). For each least-significant
ternary digit d, simulate

    n := n + d*3^k,
    k := k+1.

The prime-exponent simulation implements this finite update in two
physical counters. After the end marker, run the desired semidecision
procedure on encoded n. This deduction does not require an ordinary-value
decoder or immediate termination at the marker. The displayed powers
describe a simulated algorithm; they are not certificate primitives.

## Connection to the existing raw-input split

The equation x=I0+I1 from `EXPLORATION_TERNARY_COUNTER_CONTROL.md` gives
two Boolean ternary words. A stream reader can consume their aligned digit
pair (i0,i1) and interpret d=i0+i1. Both encodings of digit one are valid.
The fixed finite control can make the same choice for these two symbols.
Leading zero pairs are harmless if a correctly placed end marker is used.

Thus a possible compiler has two work counters and a separately verified
input stream. It must charge the initial link to x, the stream position,
exact one-time consumption of every supplied digit, and the end marker.
It must also verify the machine's instructions, counter zero branches and
halting state. Merely setting the work counters to the binary values of
I0 and I1 does not implement this stream interface. Whether its complete
arithmetic cost beats a three-or-more-counter construction remains open.
