# Reducing collected support after pooling

The pooled certificate is quadratic but its residual squares become denser.
Use an exact change of integer coordinates to reduce that cost.

For each of the 14 principal Pell pairs, retain the coordinate Z_i=A Y_i
and replace the X_i coordinate by D_i=X_i-Z_i. This is a triangular
integer linear transformation with inverse X_i=D_i+Z_i. The stored
coordinates have known affine offsets, recorded in the certificate.

The individual Pell residual becomes

    D_i^2+2D_i Z_i+Y_i^2-1.

The quadratic expression in a pooled norm becomes

    sum_i[(m_i-D_i)^2-Y_i^2].

Before making the coordinate change, subtract the sum of the 14 retained
Pell norm residuals from the pooled index-orientation residual. Its
per-pair contribution changes exactly as follows:

    (X_i-1)^2+(Y_i-k_i)^2
       - (X_i^2+Y_i^2-Z_i^2-1)
      = Z_i^2+k_i^2-2X_i-2k_iY_i+2.

After X_i=D_i+Z_i, the orientation residual therefore gains no new
quadratic cross terms in D_i and Z_i. Replacing a residual by itself minus
other retained residuals preserves its simultaneous zero set. Composing
this elementary row operation with the invertible coordinate map preserves
the integer zero set exactly.

For the supplied literal instance this changes the collected quartic
support from 11,937 to 7,912 monomials while retaining 226 variables,
163 quadratic residuals, degree 4, and coefficient height 128,446. The linear
beta-base contraction then gives the principal 225-variable equation with
162 rows and 7,867 monomials. The independent checker verifies every inverse
coordinate map, the row operation, and every collected quartic coefficient.
