# Independent review: odd-beta q=10 toy

At the toy ports beta=3, K0=5, MC=MF=2, the proposed witness has q=10, R=8283, and X=2^R≡8 modulo 10. An independent binomial computation sums from the central coefficient outward modulo 2000, proving the stated numerator divisibility and thus 1000|Y. This also gives `U=100Y | m=XY²` without q|X. The positive guard and rank conditions check; the same-index Pell completion is the separately reviewed symbolic construction and is not expanded here.

The fixed-q parent exclusion is conditional on the required exact-index and trace source replay; it does not exclude parent zeros at other q or resolve the actual compact ports. No Lean or PDF semantics is established. Run `python3 -I -S -B check.py` and compare with `result.json`.
