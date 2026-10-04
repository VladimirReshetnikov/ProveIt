# Independent mathematical review of the complete82 all-input collapse

**PASS; no correction requested.** I independently read the complete frozen
[all-input construction](complete82_all_input_outer_collapse.md), its helper
as inert text, the actual saved 82-row source, and the relevant inherited
projection, compiler and exact-ratio proofs. The construction gives infinitely
many full positive zeros at every positive ordinary input on each unchanged
valid fixed-program slice. It preserves the original positive outer slack.
This refutes the intended 82-operation representation, including its
empty-language compiler instance; it does not refute arbitrary other
82-operation polynomials or coefficient recipes. The established sound
universal bound remains 84.

## Mathematical checks

The outer choice `W=2^(2dx+b)`, `Z=1`, `C=W+1`, `F=(K+1)C`,
`X=Y=q^3` obeys the literal original bound when
`alpha=q-F-W-2dx-2>0`. Substitution into the current sheared transport gives
exactly one. The packed-index identity uses the **shifted** source numeral
`MF_source=MF_native+B-1`; its remainder is
`MC*J+1+q*(MF_native*J-1)`, not the unshifted expression. The actual mask
ranges make that remainder strictly between zero and `q^2-1`. Thus the
fixed packed index R is positive and odd, and `0<R+1<E=q^6`.

The input construction does not assume a recovered native index. Direct
Pell recurrence proves
`chi_A(v)-(A-2)psi_A(v)=2^v+(4A-5)gamma_v`, with
`gamma_0=gamma_1=0`, `gamma_2=1` and
`gamma_(v+1)=2A*gamma_v-gamma_(v-1)+2^(v-1)`.
Induction gives positive increasing gamma from index two. At the actual odd
input exponent `u=2dx+b`, the odd-index residue gives integral positive
`delta=(psi_A(u)-u)/Delta`; `rho=gamma_u` is positive. The computed input
root is consequently the positive `chi_A(u)`, and its norm is one.

The main progression `p=3Dwidth+4Lr`, where `2^L=1 mod H`, makes the main
quotient integral and eventually larger than the already fixed rho. It
does not impose `p=R`. The ratio argument legitimately works along this
entire arithmetic progression: Delta is odd, whereas
`v2(P^2-1)=9Dwidth+2` is odd, so the two quadratic fields differ and their
unit-logarithm ratio is irrational. Rotation modulo `E/2` can therefore
hit the stated interior interval in every tail. Taking the floor gives
`n=(R+1)/2 mod E/2`; the pinned exact conjugate-error estimate preserves
both strict inequalities `kY<c<k(Y+1)`. These recover positive eta and
zeta. Since `P=1 mod E`, the same hits make `h=(k-R-1)/E` an integer and
eventually positive. The first norm and index factor are both one.

The auxiliary extension uses the actual square/product chart, not a
nonintegral inverse into the sound parent. Here c is odd, so the congruences
`v_aux=R mod c` and `v_aux=3 mod 4` are compatible. With
`i=1`, `F_aux=Delta*c^4+1`, `S_aux=Delta*c^2`, the odd Pell quotient
`V=chi_(S_aux)(v_aux)/S_aux` is positive integral and satisfies
`V=-R mod c`. Hence `U_aux=(V+R*F_aux)/c+1` is positive integral.
Its substitution recovers the literal V, auxiliary norm one, and scaled
strong factor Delta. The actual paid finalizer is the product of the
seven factors minus Delta; its factor list is therefore
`(1,1,1,1,1,1,Delta)` and its output is zero.

All 18 supplied witnesses have explicit positive values:
`Jrep,F,alpha,transport_quotient,L16,h,i,auxiliary_Tf,s,w,tau_root,eta,zeta,`
`y_aux,Z,delta,rho,sigma`. In particular `L16=F_aux` is distinct from the
unchanged packing witness F. Arbitrarily late rotation hits give distinct
c and thus infinitely many tuples. Choosing the tail with `p>R` also
exhibits the missing rank restriction. No positive parent-zero theorem
or canonical-fiber assumption is used to infer these signs.

## Verification scope

This is a mathematical review, not another exhaustive source or degree
audit. I checked the source interface and finalizer against the actual
saved packet, and read the helper and its final evidence section without
executing author, predecessor or archived code. The cost
`82=45M+37A`, 18-witness interface and exact degree 185 remain inherited
from the pinned source packet. The helper's finite component evidence is
accurately distinguished from a materialized full compiler zero.

As supplementary independent checks, a fresh second-order Pell recurrence
checked 600 quotient identities, 300 positive odd-index input residues,
and twelve complete positive auxiliary blocks. Those bounded checks do
not prove irrational density, join a full first/main ratio fixture, or
certify diagnostic numbers as valid compiler constants. The unbounded
conclusion rests on the proof above and its explicitly inherited exact
error estimate. No prime-distribution theorem is needed here. No
repository or frozen predecessor file was changed.

## Frozen dependencies

The author trio was read and its SHA-256 hashes checked after its final
normal/optimized receipt replays. This review did not rerun that helper.

| File | SHA-256 |
| --- | --- |
| `complete82_all_input_outer_collapse.py` | `00894d55c070aa60897012e9e6bbd069e7ab567f5629dba9cf99a6c43f95a871` |
| `complete82_all_input_outer_collapse.json` | `53e801aa2e4f3f1a105e5fbca453de7829d11a7ace4c7d915526fbc108863e8a` |
| `complete82_all_input_outer_collapse.md` | `7c645a49f617bb628b203a3cda3117d459944b39e595b339734ec0ed7c390725` |
| `complete82_auxiliary_square_product_chart.py` | `5ff4a91d10551eafedd1d44673f64f10aa2ed283ab071d2c969d38410999f6dc` |
| `complete82_auxiliary_square_product_chart.json` | `7c029ad047c9db4652621334cb4c57d1781b5833dfac19de734ef0cb4c05fc7a` |
| `complete82_auxiliary_square_product_chart.md` | `10b83a1800550674298c797e97f4e3ccadb45e7f4c532045e869e03b55caf1c9` |
| `complete75_weakened86_infinite_outer_family.md` | `74b6c968500c5177440096bd3da3c9c07f9208f10aea79cad73554e9814bf1a2` |
| `complete75_half_binomial_compiler.md` | `68edf3bc40238ccf47b023d7358e4be62664a2d78a60b6fae19de14b67208117` |
| `complete75_weakened86_rejecting_compiler.md` | `186fc8a89c99455361fd0eb0b90d53c1fa90af32191a741c02e950d3bb0d8e78` |
