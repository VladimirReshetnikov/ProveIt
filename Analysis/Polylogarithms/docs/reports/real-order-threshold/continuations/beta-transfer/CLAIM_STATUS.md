# Claim-status ledger

The theorem labels below refer to `article/beta_transfer.tex`. Written proofs
are supplied, but they are not externally refereed or proof-assistant checked.
The new/prior distinction is relative to the explicitly inspected baseline,
not an exhaustive priority claim about the literature.

| Claim | Status | Evidence / scope |
|---|---|---|
| Positive double gamma integral | Prior, rederived | `lem:double`; predecessor Theorem 5.1 |
| Finite signed moment threshold `a+b>=1` | Prior | Predecessor Theorem 3.1; not claimed as a new result |
| Beta profile representation | Proved here | `thm:beta`, with endpoint continuation |
| Fixed-total-order Gaussian monotonicity | Proved here | `thm:transfer`; every `w>0`, sufficient radius `rho<=sqrt(3)` |
| Critical constant conjecture 12.3 | Resolved | `cor:endbounds` and `thm:sharpconstant` |
| Optimal critical constant `pi/4+log(2)/2` | Proved sharp | Lower obstruction at `N=1`, `a->0`; full upper bound for all `N>=1` |
| One-sided Euler evaluation below the threshold | Proved here | `thm:allEuler`; positive divided differences, not a finite signed measure |
| Finite Euler weight identity | Prior, rederived | `prop:weights`; stability norm `N/2` also proved |
| Critical atom and total variation | Prior, reconstructed | `thm:measure`; new construction yields additional pointwise bounds |
| Elementary critical density and bounds | Proved here | `lem:D`, `thm:measure`: `1<nu_a(T)<1+1/T` |
| Extra `1/n` harmonic-defect subtraction and strict Hankel positivity | Proved here | `cor:defects`; no period-independence implication |
| Beta/Hurwitz density identity and refined completely monotone remainder | Proved here | `prop:hurwitzdensity`, `cor:Hurwitz` |
| Full positive-coefficient large-T density expansion | Proved here | `thm:densityasympt`; asymptotic, not asserted convergent |
| Parameter-uniform density error bound | Proved here | `thm:uniformdensity`, explicit constants 16 and 4 |
| Uniform Euler asymptotic | Proved here | `thm:uniformEuler`; absolute error uniform in the critical parameter |
| Location and height of every large-N maximum | Proved here | `thm:maximizer`; no uniqueness assertion |
| Monotonicity of every A_N in a | False | `prop:counterexample`; exact rational margin at N=8 |
| General-z rational profile formula | Proved here | `thm:profile`; repeated roots included |
| Elementary half-profile identity | Proved here | `prop:halfprofile`; NOT a value of F_{1/2,1/2} |
| Twelve Gaussian enclosures | Exact finite certificates | Integer-root inequalities plus written analytic remainder bounds |
| Six cyclotomic specializations | Exact finite certificates | 548 rational coordinate equalities; not 548 independent period relations |
| 176 symbolic equalities | Exact symbolic checks | Supplemental; do not certify analytic convergence by themselves |
| Quadrature and asymptotic grids | Diagnostics only | `data/diagnostics.json`, no interval guarantee |
| Eventual unique/unimodal error maximum | Conjectural | `conj:unimodal`; not proved by value asymptotics |
| Sharp maximal radius for integrated order transfer | Open here | sqrt(3) is sufficient, not claimed optimal |
| S4 exact identity | Already proved in baseline | Not a new contribution of this report |
| S6 exact reduction | Unresolved here | No numerical agreement promoted to a proof |
| Broad normalized-radius and below-threshold angular uniqueness conjectures | Unresolved here | Not implied by Gaussian parameter monotonicity |
| Global priority and complete source audit | Not claimed | Targeted baseline inspection only |
| Lean/formal verification | Not supplied | A possible next step, not the status of current certificates |
