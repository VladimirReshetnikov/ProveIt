# Three-value singleton algebra search

The [completed search](results/result.json) examined all **78,732** three-value assignments in 0.361 seconds and found **no model** of the proposed `rho8(A,B,C,R(A,B))` calculus. The unrestricted-rho8 calibration control also found no model. This is a bounded negative result: it does not prove consistency equivalence, completeness of this model class, or a state-count improvement.

Membership atoms have one fixed undesignated value `f`, equality atoms one value `e`, and every quantifier uses the same unary operation `q`. The search tries all three choices of `e`, including undesignated equality. Its only structural conditions are the truth alias `I(t,t)=t`, modus ponens `I(t,x) != t` for `x != t`, and generalization `q(t)=t`. Neither classical negation nor quantifier reflection is assumed. It checks the closure of `{f,t,e}` under `I,q`.

The exact existing [Code254](inputs/Code254.lean) and [KCode222](inputs/KCode222.lean) definitions are preserved. With `N(x)=I(x,f)`, the literal seed formulas reduce to

```text
req(m)  = q(I(m, N(q(I(m, N(f))))))
sub     = q(I(f,f))
clos(m) = q(I(f, N(q(I(m, N(q(I(sub, req(m)))))))))
nks(m)  = q(I(clos(m), N(req(m))))
vrel    = I(f,q(f))
bundle(m) = N(I(vrel,nks(m)))
```

Every repeated `q` and the literal outer negation are retained. Syntactically fresh natural labels still enable the bundle for every represented matrix value, despite the singleton interpretation. All retained rho1–rho6 and G rows are checked, followed by restricted rho8 with `u=f`. Of the tables passing the retained rows and bundle, 23 have `e=t`, one has `e=f`, and none have the third equality value; all 24 fail restricted rho8. The unrestricted control uses the same equality freedom. The [scope note](scope.md) explains the enumeration, early-rejection counts and Boolean control in detail.

From the repository root, reproduce into a new directory:

```sh
python3 -B Computability/BusyBeaver/Research/ZFC/k219-fourth-parameter/singleton-search/search.py \
  --output /tmp/k219-singleton-algebra-fresh
```

Python 3 and a POSIX system supporting `SIGALRM` are sufficient. The process sets a hard 60-second alarm for the enumeration and reports incomplete status if it expires. The portable script reads the bundled definition snapshots. Its only change from the executed [original](history/original-search.py) is the [input location](history/portable-paths.diff); no search rerun was performed when packaging it.

The [original author receipt](author-review.json), [independent source peer](peer.json), [raw stdout](results/stdout.txt), [raw stderr](results/stderr.txt), and [publication map](publication.json) preserve exact bytes and historical scratch paths. The peer read the source and result but did not rerun the search. Its independent declarative evaluator is survivor-only; no survivor occurred.

Attribution: `Code254` and `KCode222` are pre-existing repository definitions. This diagnostic was authored by `review_upstream_reflection` during the 20 October 2026 minimization work; `opening_encoder` independently reviewed the literal formulas and bounded scope. The parent [fourth-parameter research](../README.md) supplies the proposal and its still-open calibration question.
