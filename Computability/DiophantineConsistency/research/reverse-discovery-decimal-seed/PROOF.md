# Reverse-discovery seed with a decimal numeral

This is an exact finite change of representation. It replaces the old
781-digit decimal seed by a 715-digit decimal seed while preserving every
machine action. It leaves the indexed tile table, polynomial coefficients,
all four whole integer ports, and hence the entire specialized polynomial
unchanged. It does not establish a new consistency theorem or change the
number of variables, arithmetic operations, or degree. Whole-page size is
not measured here: the shorter numeral requires a different decoder.

The construction follows the reverse-discovery packing lemma in the inert
`proofs/SEED_PROOF.md` member of
`docs/incoming/ConZFC_Pell_Carrier65_2026-10-25.zip`. Upstream subsequently
placed the exact two text files in
`con-zfc-diophantine-forms/183-pell-carrier65/` and removed that incoming
archive. The auditor authenticates those byte-identical placed texts;
the receipt separately records the historical archive provenance. No code
from either submission location is executed. Its base62 numeral is used only as
a cross-check after deriving our new integer independently from all 430
authenticated old actions. The repository's earlier
`research/mixed-radix-bfs-seed/PROOF.md` and README already study mixed-radix
target packing; this note claims the specific reverse-distance identity,
not priority for mixed-radix compression.

## Finite packing lemma

Let active states be numbered 0 through H-1, with halt H. For m actions,
let nu_j be one when action j first discovers its target, and zero otherwise.
Put sigma_j=sum_{k<j} nu_k. A discovery target is sigma_j+1; a non-discovery
target is in 0 through sigma_j or is halt H. Assume sigma_m=H-1. Set

    r_j = (sigma_j+2)^(1-nu_j),
    P_0 = 1,              P_{j+1} = P_j r_j,

and define digits

    d_j = 0                    if nu_j=1,
    d_j = sigma_j-target_j     for an old active target,
    d_j = sigma_j+1            for halt.

In every case 0<=d_j<r_j. In particular, a discovery has radix one and
digit zero. Define T=sum_{j<m} d_j P_j. Induction on the number of digits
gives 0<=T<P_m. If E is any nonnegative integer, let Q=T+P_m E. Then

    (floor(Q/P_j) mod r_j) = d_j,       floor(Q/P_m) = E.

For the first equality, the sum of the terms preceding j is below P_j,
and each later term, including P_m E, is divisible by P_j r_j. The second
follows from T<P_m. These assertions remain valid for radix one.

All three target cases are recovered by the single expression

    target_j = (sigma_{j+1} - (floor(Q/P_j) mod r_j)) mod (H+1),

where modulo denotes the least nonnegative residue. Discovery gives
sigma_j+1, an old active target gives itself, and halt gives -1 modulo
H+1, namely H. Thus this is a complete exact encoding, including early
halt actions. A second decoder can repeatedly apply divmod to Q by r_j;
its remainders are d_j and its final quotient is E.

## Exact 430-action specialization and decimal recipe

Here m=430 and H=215. Derive the discovery bits independently from the
authenticated old actions, starting with sigma_0=0: a target equal to
sigma_j+1 and different from halt is a discovery; every other active target
must be at most sigma_j. The resulting final count is 214. Independently
form each four-bit flag F_q from the two write and move pairs at state q:

    F_q = write_(2q) + 2 direction_(2q)
          + 4 write_(2q+1) + 8 direction_(2q+1).

Let m_q=1 when F_q differs from the default 14, and zero otherwise. Pack
the exceptional nibbles in increasing q into E, and set

    N = sum_{j<430} nu_j 2^j + sum_{q<215} m_q 2^(430+q).

For these actual actions N fits 636 bits: the highest nine exception marks
are zero. All 636 bits of N and the entire E agree with the old seed fields;
there are 71 exceptional nibbles. Define T and P_430 by the preceding lemma
and print the integer

    A = N + 2^636 (T + P_430 E)

in ordinary decimal notation. Its complete decimal representation is
`DECIMAL_INTEGER.txt`. The complete old decimal numeral remains in
`OLD_DECIMAL_INTEGER.txt`; neither file is an abbreviation.

To decode the new numeral, first let N=A mod 2^636 and Q=floor(A/2^636).
Extract nu_j from bit j of N, form sigma_j and all P_j, and put
E=floor(Q/P_430). The target formula above now applies with modulus 216.
For the flags, extract m_q from bit 430+q of N, let
tau_q=sum_{k<q} m_k, and put

    F_q = 14 + m_q ((floor(E/16^tau_q) mod 16)-14).

The write and direction bits for j=2q+b are bits 2b and 2b+1 of F_q.
There is no circular definition: all radices depend solely on N. Every
quantity here is a fixed finite integer, independent of the Diophantine
witnesses. The only halt is action 125, with sigma_125=80. Its digit is 81;
the raw subtraction is -1. Removing the outer modulo therefore changes
an actual action, rather than only a hypothetical input.

## Transfer to both complete coefficient layouts

The auditor independently transcribes the complete admissible942 table
from the recovered actions, checking unique coverage of indices 0 through
941 and equality with the old decoded table after removing its already
forbidden selector 1. The current2953 layout uses this order. The
reversed2521 layout keeps selector 0 and reverses selectors 1 through 941;
its initializer is physical selector 14. Both tables retain every old
tile quadruple exactly.

For either layout, the auditor constructs all 3297 coefficients of the
actual doubled clause polynomial. Its selector coefficients are

    2 [1+1024(1+w_i+256 n_i+131072 p_i+33554432 s_i)].

The label coefficients, before doubling, are 2^(35+j) at 942+j for
j<9, 2^(18+j) at 960+j for j<9, 2^(27+j) at 969+j for j<8, and
2^(10+j) at 978+j for j<8. All remaining coefficients are zero. The
physical support additionally retains the zero-weight dummy 977 and marker
A, with A=1005 or 1004. Equality is checked for the entire arrays, not only
their supports or hashes.

For clarity, write rho=2^47 and G_k(x)=sum_{j<k} x^j. Given the actual
doubled coefficients c_e, the independently reconstructed whole ports are

    beta = rho^L - 1,
    DC = rho^18 + rho^A + sum_e c_e rho^(C-e),
    K = DC + rho^(L+9),
    MC = beta - G_951(rho) - rho^960 G_26(rho) - rho^A,
    core = rho^960 G_9(rho) + rho^987 G_8(rho) + rho^A.

At (A,C,L)=(1005,1945,2953), use

    MF_source = beta + 4 G_917(rho) + (2^45-4) rho^1945 + core.

At (A,C,L)=(1004,1515,2521), use

    MF_source = beta + 8 G_917(rho) - 4 + (2^45-4) rho^1515 + core.

The summands at coincident DC exponents are added; in particular the
reflected coefficient at the marker is not overwritten by its unit term.
Every whole integer is compared with the corresponding frozen complete
certifier and its pinned receipt. Equal actions imply equal complete
tables, coefficient arrays and whole ports, so the specialized P66 and
Carrier65 polynomials are literally unchanged at each respective layout.
The native and arithmetic proofs already attached to those layouts apply
without modification.

## Audit scope and reproducibility

`audit.py --write` reconstructs the artifacts. A run without `--write`
requires byte-for-byte equality with the stored deterministic receipt and
data files. Both normal Python and `python -O` enforce all checks through
explicit exceptions; no assertion is used. The receipt pins the exact
old source page and decoder, both complete current/reversal certifiers
and their ordinary proofs, the old decimal file, this note, and the two
inert texts read from the numbered form. The historical archive hash is
recorded as provenance, not claimed as a fresh archive check by this auditor.

The two new decoding routes agree on all 430 action triples, every
discovery bit and every flag. The old base216 target stream is also rebuilt
from the actions and reconstructs the entire old integer. Three actual
decimal mutations, at the first, middle and final digit, are fed through
the new decoder and rejected by the action/invariant comparison. The
halt-modulo omission is tested against the actual action 125. These are
finite identity and negative controls; they are not bounded simulations
of a consistency statement. No archive executable is imported or run.

The new numeral has 2373 bits and 715 decimal digits, versus 2594 bits and
781 decimal digits. It saves 66 numeral digits. The raw whole-port totals
remain 69449 bytes at2953 and 59297 bytes at2521. No complete-page printed
size, PDF-size, or polynomial-size reduction is claimed by this isolated
identity audit.
