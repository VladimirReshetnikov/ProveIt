# Independent review of conditional-K 223 source and enumeration

## Verdict and exact identity

The conditional source used by the 223-state candidate is calibrated by the existing ordinary two-marker interpretation, the retained restricted-equality-helper interpretation, and a freshly replayed fusion proof. No missing source, formula, or proof-enumerator obligation was found in this review. TM universal runtime and initialization are separate receipts. This is an ordinary mathematical calibration with executable finite certificates, not a new compiled Rocq endpoint or a minimality proof.

Native table SHA256: `614adb7d387a5ccdaebecd37d8896d62bb162a20fb8b93b73ec2bd80bd75d785`.
Source SHA256: `b4e453a8801597124fd9b3ee1cd2db1cdf80c0bd904c2ffb59b79d95e91a6e96`.
Independent source guarded-CFG SHA256: `0b2d549d691f0e6e2028fcdd0724bf769efe8d61740b069f6cc8977f3b48f0e3`.

## Exact emitter binding

`check_conditional223_source.py` imports no project code. It reads the pinned verified K224 parent source/table, resolves every source decoder prefix, extracts the already verified macro bodies, and independently constructs the old and new core from the logical definitions. It checks the original abstract emitter word against the archived emitter contract before changing anything.

Write F=1, N(p)=Imp(p,F), and X(i,p,q)=N(All_i(Imp(p,N(q)))), the fused expansion of Ex_i(p AND q). With the actual opaque matrix m=c and private binder k=c, let

- r=Rel(b,k)
- Sub=All_k(Rel(k,a)->Rel(k,b))
- W=All_b(m->X(b,m,r))
- U=All_a(Sub->W)
- H=All_b(r->X(a,m,U)).

The old core is X(k,Imp(m,r),H). The new core is Imp(m,X(k,r,H)). H is unchanged. Membership vacuity VR=Rel(a,b)->All_c Rel(a,b) and restricted equality vacuity VE=Eq(a,b)->All_RelCode(a,b) Eq(a,b) are unchanged. The exact emitted fused bundle is

    N(Imp(newcore,Imp(VR,N(VE)))).

The checker compares the entire expanded primitive instruction sequence and every guarded control-flow edge of a literal reference emitter against the actual candidate. The reference changes one occurrence of subtree `111010010011101`; the surrounding source is exactly unchanged. It preserves 4,799 leaves, 210 distinct subtrees, and 6,238 guards. Thus it preserves arbitrary-register behavior relative to the already verified macro contracts, rather than merely agreeing on test inputs. All eight logical rows, parameter decoding, source gate, scratch clearing, stack pushes, command parser, reset and enumeration instructions remain intact.

## Fresh conditional fusion certificate

The new certificate has SHA256 `80172daad7c28801f9f8f1fc7519088a5f331c3679693ae2e946e7d67d866005`, 1,611 closed Hilbert nodes and 1,724 formula DAG nodes. The pinned independent checker passes under Python optimization (`-O`) and rejects its changed-endpoint, broken-MP, and hypothesis-leaf controls. Its only leaves are the already derived K/S/Peirce basis and literal rho2/rho6; inference is MP and closed GEN. No set-theory axiom or freshness assumption appears.

Our source checker independently maps the certificate's meta matrix m and private k to actual c, maps kappa to RelCode(a,b), and matches BOTH endpoints: the ordinary unfused conditional bundle and the exact fused emitted bundle. This is a uniform certificate for every natural a,b,c, including all coincidences and low matrix codes; it is not the old unconditional certificate relabeled without verification.

## Adversarial ordinary conditional calibration review

The archived `conditional_k_calibration.md` was reviewed directly, not treated as a theorem name alone. Its raw singleton construction needs only a seeded conditional instance. Its exact-pair construction uses IR to separate a from its singleton container, then closure at input a; no extensionality is assumed.

For distinct markers t,s, D(x) is witnessed by a raw T containing x whose members each contain both markers and whose non-marker members are hereditary within T. D is a finite nonrecursive first-order formula. The key tagged-object lemma applies Kc once to Sing(y,p) AND (D(y) OR y=C). Closure at a singleton of each needed member puts that member into one T, avoiding any collection or choice of the separate D-witnesses. This is the important step that rules out a hidden collection assumption.

In transferring an arbitrary D-relativized conditional instance, separate singleton inputs for t and s are outside D. They force both markers into the new C. Support makes every other member lie in D; the key lemma then gives D(C). Interpreted subset closure implies raw subset closure because every marker is already in the containing object and every non-marker member is hereditary in D. The exact pair {t,s} is empty in D. Kc plus this interpreted empty object recovers Ku by splitting on the seed premise. The argument uses finitely many schema instances effectively determined by each matrix and preserves IR. The reverse direction Ku=>Kc is immediate with private freshness. No raw empty object, raw extensionality, unrestricted witness collection or Choice is smuggled in.

## Numerical upper direction, including low codes and coincident roles

The archived helper theorem applies to conditional K as well as unconditional K; it is still needed because equality vacuity is restricted to RelCode(a,b). Genuine equality validates this helper, including diagonal endpoint names.

For every enabled a,b,c, the old decoded unconditional core implies the new conditional core by retaining its witness when the seed premise holds. This movement requires the private variable c to be free-variable-fresh in the decoded matrix D(c). The pinned `KDecodeFresh.v` proves `D_private_fresh` for EVERY code, explicitly including zero: D(0) is closed, while D(1)=Rel(0,0), so name1 is fresh. One must not claim that every name of D(0) is below0. For a=b the archived `KDecodeDegenerate.v` supplies the old decoded core using empty/hosting objects; conditionalization remains sound. For a!=b, the archived distinct-role upper theorem applies with the original gate c!=a,b. Therefore neither the low-code nor coincident-role cases require unproved numerical identities.

## Numerical lower direction and actual matrix/code coupling

The restricted-helper proof supplies the full old logical calculus after replacing primitive Eq(a,b) by membership indiscernibility E(a,b), while preserving implication, membership and each binder. It includes safe auxiliary transport and all label coincidences. It does not silently identify primitive Eq with E.

Choose a hygienic ordinary conditional matrix f with active input1/output3; apply the E interpretation first, double-negation-pad the interpreted matrix, and only then set c to its numerical code. Constructor-code induction makes c>3 and greater than every resulting label. Choose the comparison conditional instance's private variable to be this c. The equality-free conditional template commutes literally with the interpretation, so the encoded result is the actual native conditional core with matrix/private code c. It is available from an enabled bundle. Choosing c from the un-interpreted matrix would be invalid; that shortcut is not used. The translated IR is the generalized identity All_0(F->F). The two-marker ordinary calibration then supplies the finite-refutation equivalence with ZFC.

## Exact proof-enumerator adequacy

Unlike the separate experimental UW proposals, this candidate deletes or moves NO logical row. AX still consumes the same four fields and, in bottom-to-top order, pushes old current, generalized cache, rho8,...,rho1: ten entries. Its current formula is the gated conditional bundle; d=h=0 afterward. The disabled gate remains0. The enabled fused bundle is an implication into1, hence is divisible by4, positive, and cannot be1. All skipped logical/generalization rows retain their original non-1 facts.

Consequently the pinned finite block compiler is unchanged:

- DISCARD = [MP(1),AX(1,0,0,0)] followed by ten NIPs.
- A logical leaf at top-first j in1..8 uses DISCARD, AX, j NIPs, DROP, then 11-j NIPs.
- A bundle leaf uses DISCARD, AX, then ten NIPs.
- GEN remains in slot9. The old GEN and MP cleanup blocks are unchanged.

The theoremhood invariant uses the newly calibrated bundle axiom; it does not need the current formula to equal the old unconditional code. START_U=AX(0,1,1,U) still resets the counters for arbitrary retained current/stack. The following Build_F contract quantifies over those arbitrary values. The explicit candidate number P(3,P(1,P(1,P(U,R)))) is at least U, supplying a halting candidate above the initializer's cutoff3. Thus the same cofinal-reset argument handles earlier failed candidates and the nonzero startup additive counter. No assumption of a fixed empty stack or of an unused U field is made.

## Proof boundary

These checks establish exact changed-source semantics and ordinary logical/enumerator calibration. They must be combined with the exact 223 table's universal primitive simulation, local all-tape fold, source decoder and complete blank-startup receipts. They do not imply that 223 is minimal, and no fresh end-to-end compiled proof-assistant theorem is claimed.
