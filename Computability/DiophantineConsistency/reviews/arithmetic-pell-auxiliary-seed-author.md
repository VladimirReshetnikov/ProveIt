# ArithmeticPellAuxiliarySeed — author construction and replay

27 October 2026. PASS. controller_certificate authored and fully read the
281-line main, 59-line Checks and full executed replay driver. The final pair
passed in 41.975/2.717 seconds. Main output is empty;
all five reports use only propext, Classical.choice and Quot.sound. Independent
replay remains pending. No accepted source, shared object or Git state changed.

## Exact internal arithmetic endpoint

The only imports are ArithmeticPellSquaredSeed and ArithmeticPellHalfIndex.
Every public theorem quantifies over arbitrary elements of an arbitrary-universe
IΣ1 arithmetic model. The final auxiliary_seed theorem takes only a, R and
R%4=3. In particular a=0 remains legal, and no supplied Pell norm, desired
residue, strong seed, index divisibility, CRT or positive auxiliary witness
premise occurs in that endpoint.

For c=ycoord R a, the accepted strong_seed supplies the actual f=xcoord(R*c,a)
and positive i with ycoord(R*c,a)=i*c*c and the squared norm. Set
I=delta(a)*i*c*c. Positivity and I>=2 are derived, not requested. The new
quotient_square_pair uses a genuine Sigma1 successor induction, keeping both
Q(2t)=Y(4t+1) modulo f*f and Q(2t+1)+Y(4t+3)=0 modulo f*f. The second
quotient_divisor_pair induction keeps Q(2t)=4t+1 and Q(2t+1)+4t+3=0 modulo c.
These are actual interpreted oddQuotient and coordinate functions at arbitrary
internal indices. The invariant definability obligations are discharged by the
accepted arithmetic interface. The finite private modular transport helpers
are explicitly adapted from HalfIndex; its old mod-f/signless statement is
not substituted for this mod-f*f oriented result.

phase_indices derives R>0, R=2*((R-1)/2)+1 and (R-1)/2=2*(R/4)+1 by the
actual division equation. Hence u=oddQuotient((R-1)/2,I-2) has both oriented
residues (u+c)%(f*f)=0 and (u+R)%c=0. Its positivity follows from the actual
coordinate identity xcoord(R,I-2)=I*u. The ordinate y=ycoord(R,I-2) is positive.

positive_quotient extracts o from u+c=f*f*o, proves o>0, and uses the derived
identity f*f=1+c*H to remove a c-divisible summand from u+c+R. This yields
c|(o+R). The actual T=(o+R)/c is positive and satisfies
f*f*c*T=u+c+f*f*R. The same identity establishes
u=absdiff(f*f*c*T,f*f*R+c), with the subtraction order proved first. There is
no coprimality or Chinese-remainder premise. Finally the actual norm at base
I-2, together with delta(I-2)+1=I*I, gives
I*I*u*u+y*y=1+I*I*y*y, retaining the terminal +y*y term.

The full public theorem returns all five positive witnesses f,i,T,u,y,
their exact seed/coordinate identities, both residues and both additive norms.
Checks repeat the full all-internal statement, expose both negative phases,
exercise offset a=0, and derive positive witnesses at the least admitted rank
R=3 without computing a giant Pell numeral. Five axiom reports audit all
public lemmas. The finite phase arithmetic is not a standard-Nat substitute
for the represented induction.

This closes the positive auxiliary Pell witness checkpoint for the maintained
fourteen-variable route. It does not construct outer simultaneous source
witnesses, prove a full polynomial converse or internal HA equivalence, or
supply the signed-y/carrier-m refinements of the thirteen-variable route.
Those remain separate obligations.

## Validation and provenance

Immutable plan SHA:
59de0e399ed01693294f7c5d6363287c5268797619abc9a2f4b42b0f7ebc3e35.
Five-file plan manifest SHA:
0cafc70c5112c819bd12a3a0c44fdd16eebeb289ee08957b45be06634b22a26f.
The independent ROOT authorization note and audit JSON are pinned separately;
the audit SHA is
77164779f6904ff1f6918a76200087f3a5b0d2e57a733b398f49aea10075dd66.
Exact scope is 108 cached modules, including 95 Foundation modules, 393 custom
artifacts, 38 boundary primaries plus 76 companions, 507 first providers and
zero prerequisite refresh. Only these two new leaves were compiled.

The accepted direct prerequisites were authored by ROOT (SquaredSeed) and
complemented47_review (HalfIndex). I independently reviewed/replayed SquaredSeed
previously, and supplied scoped read-only mathematical challenges of related
Pell work. This author receipt is not an independent review of my new pair.
No Foundation or Mathlib prerequisite was authored or rebuilt in this task.

The complete source-header DAG, immutable selected pins, compiler, all actual
first providers and ROOT authorization were reauthenticated. The private
LEAN_PATH contains only pinned custom symlinks and explicit package/toolchain
paths; no shared project cache fallback is used. Both full input snapshots
precede the first compiler command in each attempt. Fresh outputs are regular
files. Pinned Lean4.32 uses -M6000 -j1 -DElab.async=false with one thread and
512MiB reserve checks. Full main, Checks and executed driver were read before
each attempt. Source statements, imports and caps stayed unchanged.

Both attempts and all three compiler invocations are retained. Attempt 1 failed
only at two unqualified odd_one references (ambiguous with the general Odd
lemma) and a simplification of 2<=3. Qualifying ArithmeticPellHalfIndex.odd_one
and deriving the numeral inequality explicitly from lt_add_one are the only
main changes before the final clean pair. Checks remained identical. There was
no first main object. No cap increase, omitted branch or assumed premise was
used. All final logs are warning/error-free and all five reports standard-only.

A first freeze-only pass stopped at an incorrect expected Checks line count
(58 instead of the actual 59). Its complete partial evidence and executed
freeze script are retained separately; no Lean command or source change
followed from that bookkeeping correction. The final line counts are 281/59.

The final driver authenticated 4515 observations across
1929 paths. Freeze rehashed 5906 observations across
2729 paths. Input snapshots, failed diagnostics, commands, full logs,
timings and all available objects are retained as immutable regular hardlinks,
with original private paths intact. Final provider: /tmp/pell-auxiliary-seed-controller-author-m9oqkohg/lib.

Main source: 9674bc9b071e7f3bb8d5a403c23dc6405b8e7ea417f713992d1a2b9f3e3657f7.
Checks source: 29993e8d7e16fabdad207c012e74bb73d3d384ea460ca63568e0ddc9a13499d3.
Main object: 3eebf1b9f8db2347ca3c8e0a1fc1828f7928d14352dfd2445317d053895e7c32.
Checks object: 678966029747fe9a5ede2d3a392d10aa41f45925773b042a41e65db3a84d1c71.

Evidence: [replay](arithmetic-pell-auxiliary-seed-replay.json), SHA
7d7346624ade7c38d074d90456c1ba108f33a68466a373514e167110dbba2301, and [manifest](arithmetic-pell-auxiliary-seed-author-replay/FILES.json).
