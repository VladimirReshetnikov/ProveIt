# Four short odd lengths excluded for the fixed49-bit controller

CODE-FREE ordinary proposal, pending two independent full reviews and
separate ROOT acceptance. ROOT is the author/contributor, not a peer.
This note uses the exact tile-biased family and the preserved observed
49/L2033 result; no new numerical program or mathematical helper ran.

Fix b=49 and the complete family in
`../tile-biased-single-clause-family/README.md`. Its allowed lengths are
fixed odd L>=2031. Write rho=2^49,d=49L,B=2^d and
H=1+BK+B², using the WHOLE kernel at the chosen length. P_bias requires
gcd((B²-1)H,d*lambda)=1 for an auxiliary prime lambda>d, in addition
to its other premises. If a prime p divides d and (B²-1)H, that gcd is
not1 for ANY lambda. This necessary-condition obstruction alone suffices.

For L=2031 or2037,3 divides L and d. The exponent d is odd, so
B=2^d=-1mod3. Thus3 divides B²-1. These two lengths fail P_bias
independently of K,lambda,orders or lifts.

For L=2035=5*11*37,11 divides d and d=49L=5mod10. Since
2^5=32=-1mod11 and2^10=1mod11, again B=-1mod11. Therefore11
divides B²-1, excluding this controller for every K and lambda.

For L=2033, the first separately released and reproduced computation
retains B=13,K=3 modulo19 for the ACTUAL new whole kernel. Hence
H=1+13*3+13²=209=11*19=0mod19. Since19 divides2033=19*107
and d, the same necessary gcd fails for every lambda. This uses the
new encoding's whole K and the three agreeing residue routes; it does
not substitute an old coefficient certificate. All five actual calls
exit0 and preserve identical whole RESULTS plus the full coefficients,
four ports and all ten first captures. No prime search was attempted.

The odd integers2031<=L<2039 are exactly2031,2033,2035,2037. Thus
NO member of this exact49-bit family in that interval satisfies P_bias.
If a later independently accepted computation establishes P_bias at
49/L2039, that length will be the least allowed odd length for THIS
controller in THIS fixed family. This is a conditional minimal-length
statement, not an assertion that2039 succeeds. No2039 residue, unit,
auxiliary prime or existence statement is supplied.

None of these exclusions refutes the native encoding, equation or
other completeness/controller arguments. In particular a nonunit
transport increment only defeats the stated arbitrary-target tuning
proof; it is not a consistency decision or proof of impossibility for
all rank constructions. No global minimum, measured validated equation
saving, new page, code/Lean/kernel replay or actual unsolvability follows.
The current complete decimal page remains the verified display.
