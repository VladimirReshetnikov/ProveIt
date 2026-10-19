E663: THE SAME SEVEN EQUATIONS, A SHORTER CALIBRATED GROUND QUERY

Keep E667's complete ordered signature and all seven equations unchanged.
Replace N(d,d)=d (four total term nodes) by Q(d)=d (three term nodes).
The unchanged four-bit-node codec now charges 663 instead of 667 bits.

Both equalities collapse the entire carrier to a singleton. For Q(d)=d,
Head and Tail(j=d) give x=V(P(x,s),d)=V(P(x,s),Q(d))=V(s,d), for all x,s.
For N(d,d)=d, the Boolean reduct has d=not d and therefore 0=1.
Hence equational completeness makes their derivability statuses equal.

Run from the E667 companion directory:
  python3 -B e663/build_e663.py

The parent build_e667.py is an explicit runtime dependency. This add-on
does not alter any E667 artifacts. The generated E663.bin is 83 bytes,
with one zero padding bit; crop transport to the supplied bitlength.
query663.tex is an additional report subsection.

The full calibration inherits exactly the E667/E692/raw-EPSC/ZFC ordinary
model argument. This is not a TM state count or newly compiled proof-kernel
endpoint. Attribution and license are those of the parent companion.
