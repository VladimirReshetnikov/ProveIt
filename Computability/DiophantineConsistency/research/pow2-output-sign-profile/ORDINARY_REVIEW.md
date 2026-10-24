# Independent ordinary review of raw104 sign recovery

Verdict: **PASS for the final73-predicate ordinary source equivalence.** This
review independently read the final `research/pow2-output-sign/PROOF.md`, its
complete focused checker, certificate interfaces, source pins, and the inherited
signed comparison and paired-index argument. The reviewed proof SHA256 is
`d6ed6e6d7f15148bdac0204ec7ba30067b3ae24051425a023470b19aa7ada6df`;
the checker SHA256 is
`f1a3015ac0ca1c609d35c9b25879d7092825d710440d65e3914e3f486af6ee06`.
The ordinary packet manifest SHA256 is
`9b1496050ee8edafc2a6647fc8b586ad0eb7d1db7892fcfb010b102c7410acf0`.
No mathematical gap was found in the final shorter branch proof. The full74
chain is used only after raw104>=0 has been recovered.

Write B=raw104,D=raw105,t=raw4,f=raw87,M=raw129. All early cuts are complete
polynomial combinations of original rows. The directly retained f>=2,r>=0,s>=0
first give N>=2. The digit/radix rows then give b>=2,M>=1,E>=0 without a
raw59 or B sign. The actual product-modulus and range cuts give

    f*D=M+raw131+2>=3.

Thus integral D>=1 and B=D-2>=-1. This argument uses neither an intended
power nor the later moduli-product semantics. In particular it does not
assume D>=2 while trying to exclude the one possible negative output.

The modified prefix skips only the two actual inference rows88 and114,
whose conclusions D>=1 and E>=0 were established directly. The five lower
bounds contain no B; the two raw59-dependent ones use the already reviewed
complete rewrites through M. The source occurrence audit checks that104
occurs only at88,693,1151 and59 only at114. The remaining ordered steps
therefore do not require either missing sign. The replay gives641
nonnegative prefix coordinates,573 sign inferences and429 strict
constructors. Seeding D's positivity directly is sufficient for the actual
k122=t+D constructor; no full643-coordinate prefix closure is presumed.

The actual43-argument frame includes B once and excludes59. Its exact
identity rewrites as

    W=D+sum(other42 actual arguments).

Every other argument is nonnegative, so D>=1 bounds each of them strictly
below W. Also |B|<W: for B>=0 use B=D-2, and for B=-1 use W>K>=3.
The literal K constructor and23 squares give K>t(t+1). This justifies
the weak frame, W>=3, all positive bases and indices below W, and every
other output in[0,W), without a B sign. The retained base0 modulus then
gives A>=2, and the unchanged bootstrap descent gives A>W^W. Its proof
depends on W>=2, not on the separate sign of B. All actual positive-base
moduli are consequently at least A. The V product, common unit and signed
comparison-base interfaces are valid in this weakened domain before any
power meaning or factorial argument is used.

The remaining proof is conditional on B<0. The justified bound B>=-1 then
forces exactly B=-1,D=1,k122=t+1. These are consecutive positive indices,
so one is even. This parity fact requires no f-evenness, no preliminary
call2 parity calculation, and no factorial interpretation.

At that even index, the inherited paired-index argument excludes |Y|=1
before using the short-interval theorem. Indeed the main Pell solution
then has index1, while the signed comparison abscissa congruence forces
its comparison index h to be odd. The actual R congruence modulo4 forces
h to have the even parity of k, a contradiction. This remains valid for
negative Bcmp and independent signs of its Pell coordinates. Hence
|Y|>=2; classification gives |Y|>=2A>W>k, supplying the previously missing
short interval for the signed index theorem.

The supporting calls are the actual call0 at base5=t+1 with directly
guarded output6, or call9 at base531=b+1 with output560 nonnegative by
the modified prefix. Both bases are at least2. No support uses output104.
The three unwanted X/Y orientations would make the actual modulus divide
respectively m*n^k+1,m*n^k-1,m+n^k. Their absolute values are below T;
the first and third are positive, and the second cannot vanish because
n>=2,k>=1. Thus that even seed is positive and its actual slack Y-k is
strictly positive. The retained product of the two slacks supplies the
other nonnegative slack. Its Y>=k>0 licenses the same signed-index theorem,
and its own safe support0 or9 orients its abscissa positively. Both t-seed
coordinates are now the intended positive Pell coordinates, still only
inside the B=-1 branch.

Only now is actual call2 used. Its base n103=1+(t+1)f>=2 is already positive
by its constructor; its t index and its positive t pair are now available.
The universal Pell residue gives B=n103^t modulo its actual T>=A. Under
B=-1, T divides n103^t+1. But the weak frame gives

    0<n103^t+1 <= (W-1)^(W-1)+1 < W^W < A <= T,

which is impossible. This final step proves B>=0 without using its desired
power equality as a premise. A fresh Legendre triple for104 reaches74 at
the unchanged body; its accepted chain is then licensed. The converse
forgets exactly that triple. No uniqueness of private triple choices is
claimed.

The independently initiated normal and optimized focused source replays
both pass and agree with the sealed receipts. They check47 complete
original-row combinations, the641-coordinate prefix,573 ordered signs,
429 strict constructors, actual43/weak frame, calls0/2/9 and both paired
seeds;42 arithmetic controls supplement the universal argument and nine
corruptions are rejected. These finite checks are not a proof by sampling.
This review makes no projected metric, native calibration, Lean or
internal-ZFC claim. No frozen source was changed and Lean remains paused.
