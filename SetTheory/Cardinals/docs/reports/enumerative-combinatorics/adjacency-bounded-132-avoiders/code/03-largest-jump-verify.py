"""Run exact, finite regression tests. Python standard library only."""
from fractions import Fraction as F
from itertools import permutations
from pathlib import Path
import json
import time
from model import (avoiders, avoids_132, catalan, deficit, first_count,
                   independent_clipping, probability_series, reconstruct,
                   skeleton_tail, skeleton_value, skeletons)


def main() -> None:
    started = time.perf_counter()
    report = {}
    g, a, _ = probability_series(40)
    assert a[:31] == independent_clipping(30)
    expected = [F(7, 48), F(223, 2304), F(7657, 110592),
                F(139913, 2654208), F(10681477, 254803968)]
    assert g[1:6] == expected
    assert all(x > 0 for x in g[1:])
    assert sum(g[:9]) < F(1, 2) < sum(g[:10])
    report["clipping_coefficients_checked"] = 31
    report["positive_probability_coefficients_checked"] = 40
    report["median"] = 9

    total = 0
    for n in range(1, 9):
        direct = {p for p in permutations(range(1, n+1)) if avoids_132(p)}
        generated = set(avoiders(n))
        assert direct == generated
        assert len(generated) == catalan(n)
        counts = [0]*(n+1)
        for p in generated:
            counts[p[0]] += 1
        assert counts[1:] == [first_count(n, f) for f in range(1, n+1)]
        total += len(direct)
        if n >= 3:
            extreme = sum(deficit(p) == 1 for p in direct)
            assert extreme == catalan(n-2)+sum(catalan(k) for k in range(n-1))
    report["direct_permutation_enumeration_max_n"] = 8
    report["avoiders_checked_by_direct_pattern_test"] = total

    tested = 0
    skeleton_count = 0
    for t in range(2, 8):
        skels = skeletons(t)
        assert len(skels) == catalan(t+1)-2*catalan(t)
        assert skeleton_tail(t-1)-skeleton_tail(t) == F(len(skels), 4**t)
        holes = [p for p in avoiders(t+1) if p[0] > t]
        seen = set()
        for skel in skels:
            predicted, last = skeleton_value(skel)
            assert 1 <= predicted <= t-1
            for hole in holes:
                p = reconstruct(skel, hole)
                assert deficit(p) == predicted
                assert p not in seen
                seen.add(p)
                if last is not None:
                    assert p[-1] == last
                else:
                    assert p[-1] >= len(hole)+1
                tested += 1
        skeleton_count += len(skels)
    report["skeleton_costs_checked"] = [2, 7]
    report["skeletons_checked"] = skeleton_count
    report["reconstruction_and_injectivity_checks"] = tested
    report["status"] = "PASS"
    report["elapsed_seconds"] = round(time.perf_counter()-started, 3)
    text = json.dumps(report, indent=2)
    print(text)
    path = Path(__file__).resolve().parents[1]/"data"/"verification.json"
    path.write_text(text+"\n", encoding="utf-8")


if __name__ == "__main__":
    main()
