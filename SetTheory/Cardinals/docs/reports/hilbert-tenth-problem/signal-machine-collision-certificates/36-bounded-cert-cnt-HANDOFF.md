# Handoff

The proposed counting continuation is proved, including its floor formula and slope 743/1125. The shell formula is simpler: with v=v_2(N), the number of encoded triples of total N is v^2 if 5 divides N, and floor(v/4)^2 otherwise.

For E(N)=(743/1125)N-A(N), the proof gives 0<=E(N)<L^2+4L+6, L=floor(log_2 N), and exact normalized liminf 0 and limsup 1 after division by (log_2 N)^2. The residue-class formula at N=10*2^M is in Section 5. The inverse with triple multiplicity has slope 1125/743 and normalized deviation liminf 0 and limsup 1125/743.

The only qualification to the initial proposed argument is that a special primitive scale with maximum counter above M may still be <=10*2^M; what is false for all such scales is divisibility into 10*2^M. This does not affect the square jump or the error proof.

Distinct represented totals are precisely multiples of 10 or 16, with density 3/20. They are not counted with the triple multiplicities in A or its inverse.

Fresh gcd-derived exact checks passed for every total through 200000, digital identities in bases 2 through 20 and arguments 0 through 5000, exact subsequence formulas through M=300, and independent gcd-based subsequence counts through M=32. No previous packet was changed and no upstream code was run. See `checks.json` for the precise finite scope and `PROOF.md` for the proofs.
