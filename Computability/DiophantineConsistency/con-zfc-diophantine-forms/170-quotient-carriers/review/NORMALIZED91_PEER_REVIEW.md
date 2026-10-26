# Independent review of the normalized-ordinate 91-operation construction

Reviewed: `agent_compression/NORMALIZED_ORDINATE_PROOF.md`, the retained
complete90/92 norm-elimination proofs, the source-specific signed-quotient
proof, and the canonical P66 completion proof. This is an auxiliary
universal-compiler improvement; it is not a comparison winner for the
fixed consistency instance.

The mathematical proof is valid relative to its explicitly retained whole
compiler and signed-quotient interfaces. In particular, those interfaces
must not be replaced by arbitrary numerical port assignments.

* Substituting `y=Qz-1` gives the exact factorization
  `Q V^2-(Q-1)y^2-1=Q(V^2-W)`, with
  `W=1+(Qz-z)(Qz-2)`. The factor `Q` is nonzero on the positive source
  domain. The lower degree arises from removing it before taking the
  quadratic field norm.

* In the displayed notation, `D=1+Delta*i^2*c^4>c`, `u=cT>0`, and
  `b=c+RD` is nonzero for every integral `R`. Therefore the proof-only
  quotient `f=A/(2ub)` is well-defined without a decoded rank or native
  sign. The new unit factor is `1` or `2 mod 4`, hence cannot be -1.
  It follows that `P5=1` and `K=0`. Thus `f^2=D`; rational square-root
  integrality gives integral, nonzero `f`, and direct substitution restores
  both old Pell norms.

* The sign argument has the necessary whole-source hypothesis. In the
  retained source the only direct consumers of `f` are `f*f` and `T*f`.
  If restored `f<0`, changing both signs would preserve the old equation
  while making the restored root positive and its quotient negative.
  This contradicts the retained signed-quotient theorem for the valid
  compiler. The local pair of Pell norms alone would not justify that
  conclusion, and the new proof does not pretend that it does.

* The residue claim is an all-index induction. Odd ordinates satisfy
  `v_(m+1)=(4S^2-2)v_m-v_(m-1)`, with `v0=1` and `v1=4S^2-1`.
  Therefore `psi_S(2m+1)=(-1)^m mod 4S^2`. Canonical rank `R=3 mod 4`
  consequently gives `4Q | psi_S(R)+1` and a positive integral new `z`.

* Canonical `R=3 mod 4` is supplied by the actual low-mask compiler
  interface, not inferred from a generic auxiliary Pell solution. The
  retained signed-quotient proof uses the native shifted-mask convention,
  `MC=2 mod 4`, `MF_native=4 mod 8`, and the reconstructed binary mask
  equation to recover the class. These are also the canonical promises
  consumed by the existing P66 completion.

* There is no confusion between the two quotient parameterizations.
  The older universal source uses `V=c(Tf-1)-R f^2`; the P66 source uses
  `V=f^2(cT_star-R)-c`. The canonical identities make
  `(V_star+c+R f^2)/(c f^2)` integral and positive. Multiplying that
  quotient by `f` gives the positive quotient required by the older
  universal source, whose denominator is `c f`. Thus the stronger P66
  construction legitimately supplies the older tuple.

* The degree calculation is noncircular: `deg(P5)=81`, `deg(Q)=46`,
  `deg(W)=94`, while `deg(p)=46` and `deg(b^2)=76`. Thus
  `deg(K)=188` and the output degree is 269. The displayed coefficient
  `32*Bm1^162` is nonzero on every valid compiler slice. This establishes
  attainment rather than only a degree upper bound.

The result concerns preservation of the accepted ordinary-input set.
The canonical chart need not contain every old positive auxiliary tuple.
No all-tuples bijection, arbitrary-port theorem, or new end-to-end formal
proof is included in this review.
