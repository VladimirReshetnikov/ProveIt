# Independent review: zero-spare transfer215 startup

Date: 2026-10-21. Verdict: **PASS for the finite startup, exact source-prefix bridge and protected-tail source calibration.** The all-natural append-zero binary runtime theorem remains a separate premise under review. No completed binary-equiconsistency claim is inferred merely from this note.

Reviewed proof: `research215_alternatives/ZERO_SPARE_TRANSFER_STARTUP_PROOF.md`.

## 1. Fresh independent finite checks

A newly authored standard-library checker reads the two tables and source-site lists as inert data. It imports no repository programs. For each variant it independently:

1. Parses 430 transitions over 215 working states, verifies row198/read0 is (write0,left,state40), and starts the blank tape in native state74.
2. Executes exactly73,172 transitions.
3. Checks state84, head-2, header62 and exactly107 one-cells.
4. Constructs the complete expected tape frame from source ordinal119, its full address `11010011000110110110`, logical registers (N,T,W,A,D,H,X,Y,L)=(0,6,0,0,1,1,10,1,0), and65 spares [0,0,1,0,...,0]. The constructed set of one-cells equals the entire simulated set, so the zero exterior and all omitted cells are checked, not presumed.
5. Reconstructs the source control successors from the binary source tree. Starting at ordinal25 with (0,0,0,0,1,1,0,0,0), it checks every one of the177 stored primitive steps and reaches exactly ordinal119 and the displayed full logical register tuple.

The shorter possible address in the worker's receipt differs only by trailing zero padding; the exact source leaf address above reconstructs the same control tape. This is not a coincidence of nine registers while the source program counter remains unknown.

Files:

- `check_zero_spare_startup_owned.py`;
- `ZERO_SPARE_STARTUP_INDEPENDENT_CHECK.json`.

The two table SHA-256 values are:

- variant0: `29a6ed4a594d7f974cf267a9e6b665af34c9afd8dd7abbbecf0b538ecab151e0`;
- variant1: `b49dd77f055ed4e988da919d25529bc7f604c13379c2a64dd9ab645f66daec8c`.

Their source hashes are respectively `05e7caa159d95cdf9ee254d313c44c52369ac91e52cbc23d54b15f0b64b95922` and `eb74b6919ad6f740241c11904a9af1410fa61a71dc10174e998804dabd919024`.

The177-step logical bridge does not assert that its hypothetical earlier physical tape had the actual blank execution's spare count or gap. Only the represented logical continuation needs to coincide; the universal binary simulation must apply to the actual complete frame, including its arbitrary spare values.

## 2. Completing the matched AX safely without assuming incoming theoremhood

At AX entry the residual private selector is c=0 and proof pointer0 supplies both additive fields x=y=0. The incoming logical tuple is (t,w,d,h)=(0,0,1,1). Therefore the exact all-natural AX contract has

U=1, A=d+x=1, B=h+y=1, C=0.

Its output top is Bundle(1,1,0), enabled because0 differs from both first parameters. This is a native axiom independently of incoming cache theoremhood. The first eight stack heads are the seven retained logical rows at (1,1,0), followed by L(1,1,0,1). Each is a native axiom; the only numerical restriction is U<=A, here1<=1. Counter and cache reset to0. Scheduler N remains0 and proof pointer remains0.

The ninth head is Q_1(1)=4P(1,1)+2=18, because P(1,1)=4. It must not be called a theorem merely because AX normally generalizes a theorem-valued cache: here the incoming cache is raw1 from the initializer, with no theoremhood hypothesis. The tenth head is saved old top0 and the old tail is0. Thus the suffix below the eight safe heads is exactly

P(18,P(0,0))=P(18,0)=171.

Treat this entire suffix as an opaque, arbitrary natural tail. The zero alias P(0,0)=0 correctly collapses the saved-zero/tail code; it does not change the identity of the eight explicitly represented heads above171.

The initial AX body is terminating on all natural inputs and contains no command-level halt guard. Its arithmetic contract therefore completes the verified prefix even with incoming cache1. The source proof does not apply the general theorem-valued command invariant until after this special AX has returned.

## 3. Credit at cutoff0 is exactly the required established case

The source scheduler and fields are unchanged: S tag0 with one field, MP tag1 with two fields, AX tag>=2 with three fields. The next newly fetched candidate is N=0, not1; the initial proof pointer is empty. Hence the applicable syntactic schedule starts with W(0), not the residual word W(p-1) for a nonempty initial pointer.

The already independently proved all-natural credit theorem gives

W(0)=[S], W(1)=[MP], W(2)=[S,S].

Their concatenation has minimum conservative prefix balance-3 under S=-1, MP=0, AX=+10. Every subsequent whole Cantor diagonal has nonnegative relative command-prefix balance, not just nonnegative final balance. Therefore the entire schedule from N=0 has minimum-3. This is the theorem d(0)=3, not an inference from the finite checker or the prior d(1)=2 startup.

The initial eight theorem heads consequently leave at least8-3=5 explicit theorem heads above171 at every later command boundary, unless an earlier sound halt occurs. Successful MP's optional zero push can only improve this conservative count. Each later AX begins with a safe top/cache, so it contributes all ten theorem heads, unlike the special initial AX where only eight were counted.

## 4. Internal guards and the opaque tail

For S=oldDROP;oldNIP;oldNIP, the internal DROP pushes old theorem-valued top and copies the theorem-valued cache to top. The first NIP tests the old cache and pops the temporary saved top into cache. The second NIP tests that old top and pops one head from the explicit safe wrapper. Both tests therefore concern actual theorem values. Each consumes at most the one wrapper head counted by S=-1; the other internal pop consumes its own temporary push.

The permanent margin5 is stronger than required. Immediately before every nonhalting S, the safe wrapper contains enough heads for that final pop. No head from171 is loaded into top/cache, even transiently. If a guard sees1, its theorem-valued status proves a native refutation. Neither the bootstrap cache1 nor the buried Q_1(1) is being used in this inference.

As in the original credit proof, the wrapper length is an explicitly maintained finite list representation, not an injectively decoded stack length. The identity unpair(P(x,v))=(x,v) makes each actual push/pop equation valid even if a zero head over zero changes no numeral.

## 5. Completeness survives the protected unsafe suffix

If ZFC has a finite refutation, the accepted numerical-calculus bridge and complete transfer compiler give a finite successful suffix. Its strong block contract accepts arbitrary incoming top and arbitrary numerical underlying stack once an initial AX resets counter/cache; it does not require the underlying stack to be globally theorem-valued. Therefore the buried171 does not prevent compiling a refutation.

The compiler's cofinal candidate family supplies a successful candidate beyond every finite cutoff. Every preceding nonhalting candidate drains finitely, and all arithmetic macros terminate. Enumeration from N=0 thus eventually halts unless it has already halted. The converse follows from the protected-tail soundness argument. This is the exact source-level equivalence needed for the new initializer.

## 6. Remaining boundary

The finite table replay, source-prefix replay, special AX analysis, d(0)=3 credit application, early-guard safety and cofinal completeness all pass independently. The remaining physical obligation is the universal append-zero primitive simulation for the exact table, with the actual arbitrary-valued spare suffix and full frame domain. Changing the appended spare from1 to0 is not covered merely by a successful finite bootstrap or by the unchanged numerical source.

Once that runtime theorem is supplied, it composes with this reviewed startup and source calibration. No literal simulation of the enormous remainder of the AX macro is necessary: the all-natural terminating macro contract plus the universal primitive simulation is precisely the justified bridge.
