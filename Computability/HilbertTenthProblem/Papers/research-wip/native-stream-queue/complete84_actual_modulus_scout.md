# Actual-modulus joint roots and a source-specific norm-product obstruction

No source with at most 83 live operations was found. This note records one complete 86-gate all-value alternative and a uniform source-specific nondivisibility obstruction. It is not a circuit lower bound or a search over all coordinate charts.

The parent is `complete84_scaled_strong_output.json`, SHA256 `8b2bc5d0b4db90c168107b7ded2cb4ca08df0098ed190851a3db4f1e49a9c0cf`. The actual array and the joint-root, auxiliary/strong, earlier norm-composition, discriminant-shear and affine-port notes were read as inert data/text. None of their helpers was executed. The [new helper](complete84_actual_modulus_scout.py) and [receipt](complete84_actual_modulus_scout.json) authenticate the complete parent trio and four earlier scope notes before reading data. The receipt saves the complete alternate source, all free/witness ports and its ledger. This is a bounded source/proof packet, not a maintained compiler or universal result.

## A genuinely H-dependent joint evaluation

Use the actual source names a=R12, H=a4m5=4a+3, c=R10a, kappa=index_rhs, X=wn2. The roots admit the exact joint schedule

    rhoH = rho*H
    sigma4 = 4*sigma
    center = c+sigma4
    center_product = a*center
    sigma3 = 3*sigma
    offset = X+sigma3
    D = (center_product+offset)+rhoH
    mu = (a*kappa+W)+rhoH.

The root equations are polynomial identities using the actual H relation. This costs 5M+6A, compared with the original 4M+5A. The fresh emitter replaces the nine old root rows by these eleven rows, topologically orders the entire graph, and checks that all 86 rows and all 25 supplied ports are live. The whole count is **86=48M+38A**. Every norm factor and finalizer remains identical as a polynomial; hence the parent exact degree 187, positive zero set and valid-program theorem transfer unchanged. Exact sparse coefficients verify the changed main root using H=4a+3. The helper checks both literal H-producing rows, then cuts only at this proved root and independently compares all seven factor expressions and the complete finalizer by exact expression interning. Thus the proof covers the entire polynomial. Thirty-two full signed/rational assignments supplement this row-induction proof.

The failure has a concrete accounting cause: moving H*sigma into a*(4sigma)+3sigma requires both scalar products and a new center addition. Sharing rhoH across the two roots does not repay this cost. Likewise the paid Ac2=Delta*c² remains an input of i*Ac2 in the auxiliary block, so cancelling its appearance in the main norm alone does not delete its producer. The earlier independent-port bilinear bound is not invoked as a bound for this H-dependent schedule.

## Neither H nor Delta divides the actual joint norm product

Let Nm and Ni be the actual main and input factors. For **every valid fixed-program numeral slice**, Nm*Ni is divisible by neither H nor Delta in the polynomial ring over the remaining supplied ports. This statement includes the actual producers of a, c, kappa and W; it does not treat them as unrelated cut inputs.

Here is an explicit rational evaluation proof. Write b=inner_bits and ell=twice_cell_bits; both ell and Bm1 are nonzero on valid slices. For either a0=-3/4 or a0=-1, retain every fixed numeral and set

    Jrep=1/Bm1, w=1/2, s=a0/16,
    x=-b/ell, alpha=b+1,
    delta=F=Z=rho=sigma=eta=zeta=0.

Other supplied ports may be arbitrary because they do not affect the two norm factors. The actual source yields q=2, X=1, Y=a0/2, a=a0, c=0, kappa=0 and W=1. Therefore D=mu=1 and Nm=Ni=1.

At a0=-3/4 one has H=0 and Delta=9/16, disproving H divisibility. At a0=-1 one has Delta=0 and H=-1, disproving Delta divisibility. A formal polynomial multiple must vanish at every rational zero of its factor, so these evaluations are sufficient. They apply uniformly to every valid fixed compiler slice, without varying Kconstant, MC or MF or asserting that diagnostic numeral choices are valid programs.

The helper evaluates the complete actual source at one fixed-numeral numerical instance of each family. Those evaluations are a supplement; the displayed parametrization proves uniformity.

These are signed rational evaluations used only to disprove formal polynomial divisibility. They are not positive integer zeros, accepting computations or compiler counterexamples. The Delta=0 specialization is indeed a complete signed rational zero of F84, because F84=Delta*F85; its role here is only the nonzero value of Nm*Ni at that boundary. In particular they do not prohibit zero-set-preserving coordinate changes or the known complete identity F84=Delta*F85. They rule out extracting another H or Delta factor from the main/input product itself as an all-value shortcut. They do not rule out a different joint circuit, a compensated rational identity with a separately divisible numerator, or sharing with other blocks.

## Replay and limits

Fresh writer and normal/optimized exact receipt replays from `/` pass. All checks use explicit exceptions and remain active under optimized Python. From any working directory:

    python3 complete84_actual_modulus_scout.py --root /absolute/native-stream-queue --expect complete84_actual_modulus_scout.json
    python3 -O complete84_actual_modulus_scout.py --root /absolute/native-stream-queue --expect complete84_actual_modulus_scout.json

Use `--output NEW_FILE` for a deterministic fresh receipt. No predecessor helper, historical census, physical simulator or native Pell witness generator executes. Neither a complete positive integer zero nor a full compiler counterexample is materialized. No repository or frozen predecessor is changed.

A complete operation saving remains open after this bounded scout. No earlier refuted coordinate relaxation is promoted, and no global minimum is inferred from these calculations.
