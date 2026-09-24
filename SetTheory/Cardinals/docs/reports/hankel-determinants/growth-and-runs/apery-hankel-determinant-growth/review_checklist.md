# Mathematical review checklist

The following are the most consequential points for an independent reader.
All are addressed in the article; they are listed here to make review easier.

1. **Indexing.** D_n has order n+1. The sum of the norm exponents is n(n+1),
   while the conjecture uses the n^2-root.
2. **Imported theorem.** The source is Edgar's positive density theorem and its
   stated local behavior, not an assumed moment representation inferred from
   a finite list of positive determinants.
3. **Full support.** The density is positive on both (0,c) and (c,C).
   The small interval below c must not be deleted.
4. **Interior behavior.** The Frobenius basis at c has leading orders
   0, 1/2, 1. A nonzero positive one-sided solution therefore cannot vanish
   faster than linearly. This justifies the squared-polynomial minorant.
5. **Uniformity.** In the shifted comparison, the two density-envelope
   constants depend on m but not on r or n. The comparison is uniform for
   0 <= r <= T*n, with m and T fixed.
6. **Power-weight norms.** The shifted Jacobi/Rodrigues formula is valid for
   all real s > -1, including the negative upper-comparison parameter.
7. **Corner of the Riemann sum.** At rho=0, log(x+y) is unbounded at one
   corner. Counting the i+j=k pairs controls the corner by
   O(delta^2*(1+abs(log(delta)))) and justifies passage to the integral.
8. **Non-D-finiteness.** Radius zero alone is not the argument. An eventual
   polynomial recurrence imposes exp(O(n log n)) growth, which contradicts
   the established exp(c*n^2+O(n)) growth.
9. **What is not inferred.** Bounded normalized norms are not asserted to
   converge. The O(n) logarithmic error is not a full multiplicative equivalent.
10. **Computational independence.** The binomial-sum check validates recurrence
    inputs; rational and modular Gaussian elimination are algorithmically
    distinct from fraction-free elimination. The exact computations do not
    certify the analytic proof or the imported theorem.

A useful review order is: source audit -> density minorant -> product of norms
-> main sandwich -> power-weight comparison -> limiting integral ->
non-D-finiteness. No external site has been edited or submitted to.
