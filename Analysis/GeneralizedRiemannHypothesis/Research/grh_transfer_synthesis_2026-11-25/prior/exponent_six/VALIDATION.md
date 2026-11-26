# Revalidation of the exponent-six residual interval

## Result and scope

The prior ProveIt archive `grh-exponent-six-and-transfers.zip` contains a substantive extra arithmetic argument, not just a known implication of GRH: it eliminates the residual discriminant interval left open by the published ERH bounds and census. In this turn, its mathematical reduction was read and checked, and both independent supplied implementations of its complete finite paired-norm lemma were inspected in full before being compiled/run. All executed checks passed.

This is a replay and review of an earlier report, not a new priority claim. The published census below 3.1e20 remains an external mathematical/computational input; it was not recomputed in this turn. The source Lean proof was not rebuilt by this reviewer. The theorem uses its quadratic Dirichlet-GRH conclusion.

## Primary-source dependencies verified

1. Elsenhans–Klüners–Nicolae, *Imaginary quadratic number fields with class groups of small exponent*, arXiv:1803.02056v1, Theorem 1/Table 1: the exhaustive census through |D|<=3.1e20 contains exactly 432 fields of exponent 6, maximum |D|=5,761,140. Theorem 3/Table 2 give the ERH upper bound 2.5e25. Their Theorem 2 explicitly does **not** assert completeness for exponent 6 under ERH alone. URL: https://arxiv.org/pdf/1803.02056 .
2. Aiken–Ross–Shvydkoy–Xue, *Boundary CM points and class groups of small exponent*, arXiv:2605.26020v1, Theorem 1.3(5), still conditions the exponent-six order table on exclusion of fundamental discriminants in [3.1e20,2.5e25], even assuming ERH. URL: https://arxiv.org/html/2605.26020v1 .
3. The explicit-formula identity used by the prior report is the usual primitive-odd Dirichlet Guinand–Weil identity. The normalization and archimedean estimate were checked mathematically below. Its cited source is Carneiro–Milinovich–Quesada-Herrera–Ramos, arXiv:2404.08380, Lemma 9; the root agent may wish to open that precise source before quoting its attribution.

## Mathematical reduction checked

Write x=|D| and suppose the class-group exponent divides six. For each split p, P^6=(alpha) and N(alpha)=p^6. Since alpha is not rational (the valuations at P and its conjugate differ), writing alpha=(a+b sqrt(D))/2 gives integer b!=0 and

    a^2+x b^2=4p^6.

If x>3.1e20, no p<=2000 splits because 4*2000^6<3.1e20.

Take the twelve-step function with heights 21,14,10,6,4,1,-1,-4,-6,-10,-14,-21 on intervals of width log(5500)/12. Its normalized autocorrelation F has F(0)=1; its Fourier transform is nonnegative. By Dirichlet GRH, the zero-side of the primitive-odd explicit formula is nonnegative. The gamma contribution equals

    psi(3/4)+2 int_0^infty exp(-3u/2)(1-F(u))/(1-exp(-2u)) du

and is at most psi(3/4)+(14/9)C, where C bounds |F'|. This follows from 1-F(u)<=Cu and the elementary integral bound on sum_j(2j+3/2)^(-2). The report's inequality log(pi)-psi(3/4)>2 is valid.

Let S be the all-inert model sum, and B the maximum nonnegative ramified-prime penalty per log p. Ramification costs at most B log x. Each split prime p in (2000,5500] costs less than 0.216 because no higher power of that p occurs in the supported sum. The rational interval checker proves

    S+2-14C/9-(1+B)log(2.5e25)>5.84.

Since 27*0.216=5.832<5.84, at least 28 primes up to 5500 must split. But 4*5500^6<19^2*(3.1e20), so each has 1<=|b|<=18. Two distinct split primes p<q share b. With a_p=A>=0, a_q=B'>A, set u=(B'-A)/2 and v=(B'+A)/2. Parity is automatic from B'^2-A^2=4(q^6-p^6). Thus

    uv=q^6-p^6,
    M=4p^6-(v-u)^2=x b^2>3.1e20,
    q^3-p^3<u<=sqrt(q^6-p^6).

The strict lower bound is exactly positivity of M. The finite lemma enumerates every such pair and divisor. In every case it finds an odd prime r<=151 (hence <=2000) for which -M is a nonzero square modulo r. Because -M=D b^2, this implies r does not divide bD and (D/r)=1, contradicting absence of small split primes. This completes the missing interval.

## Code inspection

The three replayed sources were extracted unchanged to this directory, then read in full. They use only standard-library rational/integer arithmetic and local C++ compilation. They perform no network calls, credential access, repository writes or destructive actions.

- `zero_test.py`: rational interval arithmetic. Logarithms use a 20-term atanh expansion with an explicit geometric tail; square-root reciprocals use integer square roots; interpolation bins are located by integer powers. The signs and outward rounding were checked.
- `paired_norms.py`: complete arbitrary-precision trial factorization of the four factors of q^6-p^6, exhaustive divisor generation up to the integer square-root bound, and exact quadratic-residue sets. Four worker processes were used.
- `paired_norms.cpp`: independently written divisor recursion, 128-bit products, corrected integer square root after a floating starting approximation, checked factorization products, and exact residue masks. Bounds guarantee no relevant 128-bit overflow. Assertions were enabled.

## Replayed commands and observed results

Run inside this directory:

    python3 zero_test.py > zero_test_replayed.txt
    g++ -O3 -std=c++17 paired_norms.cpp -o paired_norms
    ./paired_norms 5500 151 > paired_norms_cpp_replayed.txt
    python3 paired_norms.py 4 > paired_norms_python_replayed.txt

The interval check and C++ replay each completed in under a second in this environment, after compilation; the Python replay completed in several seconds. All exited with code zero.

| Check | Python | C++ |
|---|---:|---:|
| Eligible primes | 414 | 414 |
| Prime pairs | 85,491 | 85,491 |
| Divisors in interval | 10,144,433 (strict lower endpoint) | 10,229,924 (closed lower endpoint) |
| M>3.1e20 | 9,393,302 | 9,393,302 |
| Survivors without split witness | 0 | 0 |

The divisor-count difference is exactly 85,491, one lower endpoint per prime pair. Those extra endpoints have M=0, so the eligible candidate count agrees. C++ confirms largest first witness prime 151.

## Conservative conclusion

Assuming the verified RH/Dirichlet-GRH input and the published EKN census, the replayed argument establishes the complete list of 432 imaginary quadratic fields of exact class-group exponent six. The complete count is genuine extra arithmetic beyond plugging GRH into the previously published classification statement, because that statement left this interval unresolved. This turn has independently revalidated the earlier ProveIt completion rather than newly discovered it. Worldwide priority and the full low-discriminant census were not rechecked.

The extension to 1,236 imaginary quadratic orders additionally uses Aiken–Ross–Shvydkoy–Xue’s conductor classification and their table. The table-integrity and membership checks have now been rerun successfully, as recorded below; they should be attributed separately from the residual-interval exclusion.


## Supplementary table checks completed

The delivered `exponent-six.csv` contains 432 distinct discriminants, all labeled exponent six, with maximum absolute field discriminant 5,761,140. After full source inspection, `check_order_table.py orders-six.txt exponent-six.csv` exited zero. It verifies the original author table's Git blob hash `fc8d109c749eb73efab6bc5d9f058c5c78cd8c8f`, 1,236 unique order discriminants, exact partition by listed group, maximum absolute order discriminant 43,522,752, and exact equality between its 432 maximal orders and the field CSV. See `order_table_replayed.txt`. These are table-integrity, count and matching checks; all 103,830 individual class powers were not recomputed.
