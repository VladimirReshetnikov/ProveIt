# Expanded compact/iPRA rebuild: stage 285 higher-memory retry

The earlier `-M3000` attempt failed with kernel memory exhaustion and no
object. This separate retry preserves that failure, checks its receipt, log
and direct dependency guards, and gives stage 285 alone `-M6000` and a
360-second wall bound. A 12-GiB available-memory preflight applies before this
larger child, alongside the existing two-child limit; other stages retain their
previous limits. The source and theorem statements were not changed.

Lean compiled `ZFCinPA.BaseCertificate` without warnings in 58.660 seconds,
exit 0. Its object SHA-256 is
`615b7081c42d9de9cc1297c93c10b564de12ebe606b5cc6094df3f4996eb6b6a`.
Source and direct dependency guards were unchanged, the full selected overlay,
all source pins, earlier receipts and exact-warning baselines passed, and the
wrapper reported 285/425. Runner SHA-256 is
`9d04ae692ea112c478f5ff96e31c82748e1b08184e86554071b0deb6767b8621`.

Twelve five-second samples during the Lean child recorded maximum RSS
3,395,628 KiB; the full monitor sampled at most one Lean child and minimum
MemAvailable 16,978,960 KiB. Brief peaks or overlaps may be missed. This
author prefix is not an iPRA endpoint, independent replay, or full provider
audit; the remaining 140 stages, compact model-to-iPRA join, package and
dynamic ancestry remain open.
