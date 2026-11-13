# Guard-free odd-Pell projection for trace74

These Lean sources adapt the weighted projection argument to
the actual positive trace74 zero and use the odd main-Pell ordinate supplied by
the checked fold theorem. The claimed result keeps the same graph valuation and
the factor `h*X` in the divisibility statement. The first theorem takes the
Pell-ordinate identity as a hypothesis; the second supplies an odd positive
index from the fold result. Neither asserts an exponential equality, a natural
rank bound, the saturation guard, or a trace74-to-trace75 reduction.

The mathematical source review is
[here](../../reviews/trace74-guardfree-projection-source-independent/README.md).
The two-stage runner pins its sources and selected direct provider objects; it
does not establish complete project, package, dynamic, or intermediate-object
ancestry. The policy test exercises 27 report acceptance and rejection cases.
Author attempt01 passed both stages with actual outer session 20194 exit 0;
its retained terminal SHA-256 is
`05cd1d7e9abb4f7c0ab8954d83f79aaf0ecca5ee7e156c9854da0dfe889b2585`.
The [independent result audit](../../reviews/trace74-guardfree-projection-result-independent/README.md)
passed. The audit retains the direct-provider and search-path limitations above.
