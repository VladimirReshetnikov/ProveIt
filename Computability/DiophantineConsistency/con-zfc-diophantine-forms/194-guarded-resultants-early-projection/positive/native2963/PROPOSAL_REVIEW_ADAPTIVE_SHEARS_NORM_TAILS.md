# Independent review: adaptive eleven-variable shears and shared norm tails

Reviewed 2026-10-23. Both local changes are valid ordinary arithmetic reductions. Lean formalization remains paused. The native/compiler consistency calibration and the proof inside object-language ZFC are not established by these new finite checks.

## Eleven positive variables, 111 operations, degree 211

`candidates/positive11-adaptive-shears/positive11.json` changes precisely one producer in the incoming polynomial-shears eleven-positive circuit: `S=4qY` becomes `S=qY`, and `U=qS`. It has eleven strictly positive integer variables, 111 live binary operations (63 multiplications, 31 additions, 17 subtractions), and exact degree 211. Its two-residual system uses 108 operations. The actual whole compact44 tuple, including its already shifted `MF_source`, is preserved.

The parent archive SHA-256 is `978f7e8be846732c1330f3a75a0fe38871432f79951b8eaad6ef096f3e03e165`; the retained 112-operation literal SHA-256 is `b482a1e952536c445918dd5a9e03fdaea0081e0e016e6a1bcbf7be9a26b5a92d`. All retained-source pins and raw/gzip coefficient hashes check. Ordered row comparison confirms the sole change: rename the old `qY` register to `S`, remove its scalar-four consumer, and leave every other row unchanged. This is an exact certificate of the formula change, rather than a sampled polynomial comparison.

The proof has to recover the quotient `q|X` from the smaller main carrier. It succeeds, with the following dependency order:

1. The unchanged eight-conjugate norm recovers integral first, strong, and auxiliary roots. Its separation and denominator-descent arguments do not use the scalar four. Reducing the integral root-sum equation gives `q^3|Y` and the transport divisibility before `C>0`.
2. The absolute main root and first Pell root give main index `p` and first index `m>=2`, hence `c>8XY^3>=8q^9`, also before `C>0`. The offset `Tbar=T+F+alpha` then forces `V>1` using the unconditional rank estimate. Its small auxiliary gap and the root-sum equation recover positive transport and `C>0`.
3. Authentic mask bounds give `3q<R<q^4-2`. The positive main root, normalized strong root, and signed auxiliary index argument then give `1<=m<p=R`. These inherited index steps do not assume the missing quotient `q|X`.
4. Only now use the adaptive divisibility `U|H(SX-v)` with `v=k-R-1`, `S=qY`, `U=q^2Y`, and `H=4Y(X+1)+3`.

The important cancellation is exact. Since the authentic beta is 1 modulo 3 and `J=3j+1`, one has `q=2 mod 3`. Thus `gcd(q,H)=1` and

\[
g=\gcd(H,U)=\gcd(H,Y)=\gcd(3,Y)\in\{1,3\}.
\]

Because `gcd(q,g)=1`, divisibility `q^3|Y` survives removal of this cofactor: `q^3|(Y/g)`. Consequently

\[
\mu=qY/g\ge q^4>R.
\]

The main relation gives `U/g | SX-v`, so `mu|v`. Also `mu|4XY^2`. The first-Pell recurrence gives `k=2m mod 4XY^2`, and therefore `mu | 2m-R-1`. Since `1<=m<R<mu`, the latter integer has absolute value less than `mu`; it must vanish. This recovers the **exact** first index `2m=R+1` before restoring `q|X`.

Now `v` is a positive multiple of `4XY^2`, and `U|4XY^2` because `q^3|Y`. Returning to the main divisibility gives `U|HSX`, hence `q|HX` and `q|X`. The restored source parameters

\[
w=X/q,\quad h_{\rm index}=v/(XY),\quad
\gamma_{\rm old}=\gamma+w-v/U
\]

are integers. The main-root inequality `d>(a+1)c` and `c>X` force `gamma_old>0`. The restored transport is explicitly translated by `z_old=z_new+1`; it is not silently identified with the old-z row.

The positive converse also survives the smaller carrier. On canonical witnesses, `v` is a positive multiple of `4XY^2`, so

\[
\gamma=\gamma_{\rm old}-w+v/U>0,
\qquad v/U\ge4XY/q^2=4wY/q>w.
\]

The inherited canonical auxiliary growth gives `Tbar>F+alpha` and `Tbar>Cf`, so the new `T` is positive. Choosing the transport weight after this auxiliary witness gives `L=k Tbar>Cf,k`, and the existing bound `r>qW-2k>2L` makes the last root-sum coordinate `n` positive. There is no new restriction on canonical witnesses hidden in the offset or inverse shear.

The product finalizer requires only one residual to exclude the negative-unit branch. Here `N8` is always a square modulo four, because its tail has a factor 64. Hence `(1+N8)(1+A1)=1` cannot have both factors -1: that would require `N8=-2`, impossible modulo four. No assertion that the smaller `A1` is itself square modulo four is needed.

The norm polynomial is unchanged and has the retained exact 229-term double-center certificate and degree 198. The changed main residual has degree 13 and leading form

\[
8q_0^2 k_0 X^2Y^4(q_0^2Y\gamma+R_0).
\]

Together they give degree 211, attained by the coefficient `2^9(3 beta)^48` at `j^48 i^18 eta^39 X^30 Y^67 T^2 F^4 alpha^2 gamma`. This is the parent's coefficient divided by sixteen, consistently with removal of the scalar four from both `U` factors in the gamma term.

I inspected the adapted sparse-ring checker and replayed it normally and under `-O` in a scratch copy; both passed. Its exact cut contracts, double-center expansion, and degree calculation are an adapted parent audit, as the candidate correctly states. The separate review tool authenticates the whole tuple and exact one-gate transform, checks the changed main cancellation/leader and finalizer residue obstruction, and records those scratch replays. The ordinary source reduction above remains a mathematical proof, not a finite-test inference.

## One multiplication saved in each complete two-root tail

The generic identity is

\[
\boxed{(t^2-s(a+b))^2-4s^2ab
=(t^2+s(a-b))^2-4sat^2.}
\]

Both sides expand over every commutative ring to

\[
t^4-2s(a+b)t^2+s^2(a-b)^2.
\]

The right side reuses the already computed `t^2`. The literal candidates save one multiplication with all additions/subtractions included. The equality is unconditional on roots, signs, scales, domains, or coefficient values, so it preserves the entire polynomial, not only its zero set or a chosen canonical witness family.

`tools/build_norm_tail_sharing.py` recognizes the parent tail, retains its complete live prefix, and replaces the final norm. Its verifier first normalizes both tails exactly in four independent cut-point atoms. It then checks every retained node after operand remapping and checks that the retained prefix plus the normalized tail covers **every** child node. Thus a separate unverified definition, leaf, or gate cannot be hidden outside the local identity. Backward-only operands and full liveness are also checked. Canonical ordering of commutative operands and merging identical gates do not change evaluation.

I independently checked the complete prefix and exact four-atom polynomial identity for one saturated case and one 10Z case:

| Case | Domain | Parent operations | New operations | Exact degree inherited from identical parent polynomial |
|---|---|---:|---:|---:|
| `saturated_positive` | nine positive integers | 434 | **433** | 1,628,768 |
| `integer10_cubic` | ten unrestricted integers | 487 | **486** | 1,114,252 |

Both have all nodes live and every fixed leaf authenticated. The saturated case retains the coherent whole compact54-derived eleven-leaf binding. The integer case retains all twelve signed-magnitude fixed payloads of its incoming parent; their signs and magnitudes are decoded, rather than reading the sign tag as part of an unsigned number. Sixty actual-coefficient modular output comparisons per case provide extra transcription diagnostics. The exact free-atom identity and full prefix map, rather than these diagnostics, prove polynomial equality.

The builder also applies the same transformation to seven other pinned parents. Its all-nine receipt records the expected one-operation reductions, including 480→479, 484→483, 521→520, saturated 1074→1073, and the radical 723→722 cases. My selected independent audit does not claim to replay all nine cases or re-prove their parent exact-degree/calibration theorems. The norm10 provenance initially contained a mistyped archive hash; it was corrected by computing the actual incoming ZIP hash before this review passed. That correction changes provenance metadata only.

## Reproduction and boundary

Run the new independent reviewer with the existing SymPy 1.14 environment:

```sh
/tmp/proofs62ff-wave7-review-venv/bin/python Computability/DiophantineConsistency/tools/review_adaptive_shears_norm_tails.py
/tmp/proofs62ff-wave7-review-venv/bin/python -O Computability/DiophantineConsistency/tools/review_adaptive_shears_norm_tails.py
```

Both modes pass and produce identical semantic receipts apart from the optimization flag. No candidate builder is imported by this tool, no archived release entry point is executed, and no Lean, TeX, network, or package installation is invoked. The scratch positive11 sparse-checker replay is recorded at `/tmp/proofs62ff-positive11-adaptive-review/REPLAY.json` and embedded in the receipt.

The result is a valid local ordinary improvement and exact circuit transformation. The original native-to-refutation calibration remains inherited, and a Lean proof of the final statement inside ZFC remains a separate unfinished obligation.
