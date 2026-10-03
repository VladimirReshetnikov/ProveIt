# Audit addendum: full core-monomer Rayleigh differences

Date: October 1, 2026. Verdict: **APPROVED**.

The argument in `CORE_RAYLEIGH_COROLLARY.md` is an ordinary corollary of the
already approved computer-assisted boundary theorem. It needs no additional
finite classification. All earlier approved files and source-hash records are
unchanged.

## 1. Algebra and the private-head support bijection

For distinct `i,j,k`, direct expansion of the stated multiaffine core polynomial
gives

    Δ_(z_j,z_k)F = Q z_i² + M z_i + B,
    Q = a_j a_k − b_jk,
    M = a_j b_ik + a_k b_ij − c − a_i b_jk,
    B = b_ij b_ik − a_i c.

The expression is independent of `z_j,z_k`, as required. The boundary theorem
proves `B≥_coeff0`.

Adjoin a new exterior vertex `x` with its sole arc `i→x`, and set `L=u_i v_x`.
Deleting this forced edge from any support using `x` leaves a unique support
on the other chosen core vertices. Conversely, those supports extend uniquely.
The remaining support does not use physical core vertex `i`, since there are
no internal core arcs. Thus the resulting identities are exactly

    a_i'=a_i+L,  b_ij'=b_ij+L a_j,
    b_ik'=b_ik+L a_k,  c'=c+L b_jk.

The coefficients `a_j,a_k,b_jk` remain unchanged. Residual old supports may
still have several matching witnesses; the bijection is between endpoint
supports and does not count those witnesses. The producer corrected one
potentially misleading witness sentence before this approval.

The enlarged graph satisfies the boundary theorem's hypotheses, and its
boundary gap is identically

    B + u_i v_x M + u_i² v_x² Q.

The variable `v_x` is fresh. Its linear coefficient is therefore precisely
`u_i M` and is coefficientwise nonnegative. Multiplication by `u_i` is an
injective shift of monomial exponents, so `M≥_coeff0`. This is formal monomial
cancellation, not division by a numerical activity assumed to be positive;
zero-activity specializations cause no problem.

The quadratic coefficient `Q` is also coefficientwise nonnegative because
each feasible size-two endpoint support admits at least one pair of matching
single-edge supports in `a_j a_k`. Alternatively, extracting the coefficient
of `v_x²` from the same enlarged gap proves this immediately. Together these
facts give coefficientwise nonnegativity of the full core-variable Rayleigh
difference in all original role variables and all three core monomers.

As an additional algebra check, exact symbolic expansion independently verified
the displayed Rayleigh identity, the enlarged boundary identity, and
`F(z_i+L)=F(z_i)+L∂_(z_i)F`.

## 2. Pairwise negative correlation

Fix nonnegative role activities and strictly positive core monomer activities.
The endpoint-support probability measure weighted by role weight times the
product of unused-core monomers has normalizer `F>0`: the empty support alone
contributes `z_0z_1z_2>0`.

Writing `X_j` for the unused indicator, multiaffinity gives

    E[X_j]=z_j F_j/F,
    E[X_jX_k]=z_jz_k F_jk/F.

Consequently

    Cov(X_j,X_k)=−z_jz_k Δ_(z_j,z_k)F/F²≤0.

Used indicators are `1−X_j`, so their pairwise covariances are equal to those
of the unused indicators. The probability interpretation is therefore correct,
including vanishing role activities. It concerns distinct core vertices and
the endpoint-support measure, not the distribution on individual matching
witnesses.

## 3. Scope

The approved conclusion is coefficientwise positivity and Rayleigh inequalities
for **nonnegative core monomer arguments**, together with the stated pairwise
negative-correlation corollary. It does not prove the all-real Rayleigh criterion
for real stability, negative association of arbitrary events, Rayleigh
inequalities in exterior or role-activity variables, or an internal-core-arc
extension.

The producer's redundant middle-coefficient enumeration is not needed for this
proof and is not a new premise of this approval.

Approved corollary source SHA-256:
`bfc5ba8cd7ee68f3e0c220a825ef2d937be02ed08b4aaf66d1ce70b46e4ff354`.
