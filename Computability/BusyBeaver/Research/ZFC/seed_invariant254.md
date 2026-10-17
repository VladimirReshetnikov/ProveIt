# Proof-carrying startup data

The initializer search now accepts a larger, proved family of formula data.
`SeedInvariant254.lean` supplies six certificate constructors: truth,
generalization, implication identity, weakening by K, ex falso, and equality
reflexivity. Every certificate denotes an actual `Code254.C254` theorem.
Lists of these certificates give `Enum254.Good` stacks using the original
unshifted Cantor pairing. No theorem oracle or consistency assumption is used
to establish these positive certificates.

For arbitrary `N,A,D,X,Y,L`, the checked example

```text
[N,3,9,A,D,6,X,Y,L]
```

is a safe structured-program root. Code3 is reflexive equality, code6 is
generalized truth, and stack9 contains truth and generalized truth. Actual
structured219 halting from this state is equivalent to a refutation of the
native CP/full-GIC/IR theory, by composition with `DirtyProgram254`.
The logical register tail at indices9 and above is zero. A binary frame,
spare-space invariant, complete runtime simulation, and ZFC calibration
remain separate requirements.

Code60 demonstrates why register roles matter. As a formula it is
`wim 5 0`, so weakening truth certifies it. As a stack it decodes to heads
`[5,0,0,1]`; the last entry is falsity. A checked caller proves
`Good 60 → C254 F`. Moving a physical value between a formula register and
the formula-stack register therefore changes the startup proof obligation.
This motivates the physical-register permutation experiment without changing
the original logical calculus.

`safe_seed254.py` recognizes a sufficient family of these certificates and
reconstructs the exact input code before accepting it. Its fuel limits can
cause rejection, so it is deliberately incomplete. Every stack entry is
examined; buried falsity is not ignored. The Lean theorem concerns the explicit
certificate datatype; there is no claimed formal Python-to-Lean compiler.
A candidate found by Python must supply the corresponding literal Lean
certificates and the separate complete binary frame.

The bounded census below65536 accepts13516 formula codes and4051 stack codes;
all accepted certificates reconstruct their exact inputs. Falsity1, stack1
and stack60 are rejected. Reproduce with

```sh
python -B Computability/BusyBeaver/Research/ZFC/safe_seed254.py
```

The module passed Lean4.32.0 in0.62seconds. Its axiom dependencies are standard
`propext`, `Quot.sound`, and, for the existing stack/program interfaces,
`Classical.choice`. The final99-unit umbrella,12 axiom audits and three
callers pass using verified matching dependency caches. Full commands,
source identities and the independent source reviews are recorded in
`results/breakthrough99-integration-verification.json`. This is a useful
search invariant, not a new state-count result.
