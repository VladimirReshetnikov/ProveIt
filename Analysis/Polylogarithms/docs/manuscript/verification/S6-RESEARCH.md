# Selected higher-depth S6 experiments

The original full-Cayley obstruction concerns the specified 5131 bounded
relations. It remains valid. S6 is conjectural; this follow-up explores
additional relations without interpreting finite nonmembership as a period theorem.

The adapted alphabet is Z,Y,H,B,X, with X=C-B. For admissible v, DS(X,v)
is a linear combination of standard one-divergence DS(C,v) and convergent
DS(B,v) identities. The proved full-Cayley retraction Pi preserves periods
modulo its kernel. Explicit conjugation-odd projection is required before
indexing the odd ambient space; the raw source target contains even components.
The initial indexing failure and superseded Python run are retained.

probe_S6_depth_five.py considers 22 admissible permutations of ZZXXXY.
All projected rows lie in depth at most four; 19 have nonzero pairing with
the old separator and escape that bounded span plus the full Cayley ideal.
A zero pairing is not membership evidence.

probe_S6_depth_five_extended.py considers 190 inputs from ZZXXXY, ZZXXYH and
ZZXXYB. Some projections retain depth-five coordinates. These are never
dropped. intersect_S6_depth_five.py eliminates that sector over Q, carrying
lower components and source combinations. Its rank is 166; the kernel is
24 dimensional. All 24 resulting bounded relations are reconstructed from
the originals; every outside coefficient cancels. They span the bounded
information obtainable from this selected family modulo the Cayley ideal.

export_S6_intersection_matrix.py exports 5131 old plus 24 new bounded rows,
and the target, in 2546 coordinates. The positive scale is 384; all entries
fit int64. S6-intersection-integer-matrix.json binds the exact input digest.
s6_modular_solver.cpp gives rank 1897 modulo 2147483647 and target residual
132 terms. The smaller 22-input search had rank 1896. These finite-field
results do not prove nonmembership over Q: bad-prime rank loss remains possible.
No period nonidentity is inferred.

Binary matrices, executables and the exact projector cache are scratch artifacts.
The Python search/exporters regenerate inputs from immutable source modules
and source-pinned exact projector images. From this verification directory:

```
g++ -std=c++20 -O3 -march=native s6_modular_solver.cpp -o .scratch-real-orders/s6_modular_solver.exe
.scratch-real-orders/s6_modular_solver.exe .scratch-real-orders/S6-intersection-integer-matrix.bin S6-intersection-native-search.json
```

Run after exporting the matrix. The earlier native receipt records three
implementation fixtures and matching Python prefix ranks. The intersection
receipt separately binds its input metadata and C++ source digest. Future
membership candidates require rational reconstruction and complete exact
residual certificates before supporting the analytic period identity.
