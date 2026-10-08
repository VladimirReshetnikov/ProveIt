"""Independent exact Regina crosschecks for the three tensor arithmetic modes.

Run with --fast-dir pointing to ProveIt's Topology/UnknotRecognition/fast.
Regina is an optional external dependency; --regina-path can select a local
installation.  The audit compares every coefficient, not sampled values.
The residual-twist examples replicate an audit already present in the base
repository; they are not counterexamples to Jones unknot detection.
"""
from collections import defaultdict
from datetime import datetime, timezone
from hashlib import sha256
from importlib import metadata
from math import comb
from pathlib import Path
import argparse
import json
import platform
import random
import sys


def jvp_from_x_polynomial(polynomial):
    """Closed binomial formula for V(x)=a(p)+b(p)x, p=x-x^{-1}.

    Write F_m(p)=sum_k binom(m-k-1,k)p^(m-2k-1).  For m>0,
    x^m=F_(m-1)+F_m x, and x^(-m)=(-1)^m(F_(m+1)-F_m x).
    This implementation is independent of the baseline recurrence audit.
    """
    def fibpoly(m):
        return {m-2*k-1: comb(m-k-1, k) for k in range((m+1)//2)}

    a, b = defaultdict(int), defaultdict(int)
    for exponent, coefficient in polynomial.items():
        if exponent == 0:
            a[0] += coefficient
            continue
        m = abs(exponent)
        aa = fibpoly(m-1 if exponent > 0 else m+1)
        bb = fibpoly(m)
        asign = 1 if exponent > 0 else (-1)**m
        bsign = 1 if exponent > 0 else (-1)**(m+1)
        for degree, value in aa.items():
            a[degree] += coefficient*asign*value
        for degree, value in bb.items():
            b[degree] += coefficient*bsign*value
    answer = [{e: c for e, c in sorted(p.items()) if c} for p in (a, b)]
    recovered = defaultdict(int)
    for offset, p in enumerate(answer):
        for degree, coefficient in p.items():
            for k in range(degree+1):
                recovered[degree-2*k+offset] += coefficient*(-1)**k*comb(degree, k)
    assert {e: c for e, c in recovered.items() if c} == polynomial
    return answer


def residual_twist_pd(length):
    """The explicit fixed-exterior family in the baseline residual audit."""
    host = ((5, 1, 2, 0), (1, 4, 3, 2), (0, 3, 4, 5))
    rows = list(host[:2])
    a, b = host[2][:2]
    for i in range(length):
        c, d = host[2][2:] if i == length-1 else (6+2*i, 7+2*i)
        rows.append((a, b, c, d))
        a, b = d, c
    return rows


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--fast-dir", type=Path, required=True)
    parser.add_argument("--regina-path", type=Path)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    fast = args.fast_dir.resolve()
    sys.path.insert(0, str(fast))
    if args.regina_path is not None:
        sys.path.insert(0, str(args.regina_path.resolve()))
    import regina
    from fastunknot import Diagram
    from fastunknot.tensor_jones import tensor_jones

    def regina_polynomial(link):
        value = link.jones(regina.Algorithm.Treewidth)
        raw = {e: int(str(value[e])) for e in range(value.minExp(), value.maxExp()+1)
               if value[e] != 0}
        assert all(e % 2 == 0 for e in raw), "knot Jones polynomial has odd x exponent"
        return raw, {e//2: c for e, c in raw.items()}

    # Independent named examples fix the variable convention before using PDs.
    calibration = []
    for name, link, expected in (
        ("right_trefoil", regina.ExampleLink.trefoilRight(), {1: 1, 3: 1, 4: -1}),
        ("left_trefoil", regina.ExampleLink.trefoilLeft(), {-4: -1, -3: 1, -1: 1}),
        ("unknot", regina.Link(1), {0: 1}),
    ):
        raw, normalized = regina_polynomial(link)
        assert normalized == expected, (name, normalized)
        calibration.append(dict(name=name, regina_x=sorted(raw.items()),
                                normalized_t=sorted(normalized.items())))

    cases = []
    for name in ("unknot", "trefoil", "figure_eight", "hard_unknot_8",
                 "conway", "kinoshita_terasaka", "torus_3_5"):
        path = fast/"examples"/(name+".json")
        source = json.loads(path.read_text())
        cases.append((name, Diagram.from_json(source),
                      dict(kind="repository_fixture", path="examples/"+path.name,
                           sha256=sha256(path.read_bytes()).hexdigest())))
    for strands, repeats in ((3, 4), (3, 5), (4, 3), (4, 5), (5, 4), (5, 6)):
        word = [i if i % 2 else -i for i in range(1, strands)]*repeats
        cases.append((f"weaving_{strands}_{repeats}", Diagram.from_braid(strands, word),
                      dict(kind="braid", strands=strands, word=word)))
    seed, accepted = 202610082, 0
    rng = random.Random(seed)
    while accepted < 20:
        strands = rng.randrange(2, 5)
        word = [rng.choice((-1, 1))*rng.randrange(1, strands)
                for _ in range(rng.randrange(1, 13))]
        try:
            diagram = Diagram.from_braid(strands, word)
        except ValueError:
            continue
        cases.append((f"seeded_braid_{accepted}", diagram,
                      dict(kind="braid", strands=strands, word=word)))
        accepted += 1
    for length in (9, 23):
        cases.append((f"residual_twist_{length}", Diagram.from_pd(residual_twist_pd(length)),
                      dict(kind="baseline_residual_twist_replication", residual_length=length,
                           source="jones_research/audit_residual_twists.py",
                           host_crossings=3, implied_residual_jvp_cap=22)))

    rows, comparisons = [], 0
    for name, diagram, provenance in cases:
        original = None
        for mirrored in (False, True):
            d = diagram.mirror() if mirrored else diagram
            # Regina begins each row at the incoming underpass.  Both legal
            # rotations are even, so they preserve over/under information.
            pd = [[label+1 for label in row[u:]+row[:u]]
                  for row, (u, _) in zip(d.pd, d.incoming_slots())]
            link = regina.Link.fromPD(pd) if pd else regina.Link(1)
            assert link.countComponents() == 1
            assert link.size() == d.crossings and link.writhe() == d.writhe()
            raw, expected = regina_polynomial(link)
            if mirrored:
                assert expected == {-e: c for e, c in original.items()}
            else:
                original = expected
            variants = []
            for arithmetic in ("laurent", "integer-global", "integer"):
                output = tensor_jones(d, arithmetic=arithmetic)
                actual = {e: int(c, 16) for e, c in
                          output["jones_polynomial"]["coefficients_hex"]}
                assert actual == expected, (name, mirrored, arithmetic, actual, expected)
                assert output["polynomial_identity"]["is_one"] == (expected == {0: 1})
                variants.append(dict(arithmetic=arithmetic, matches_regina=True,
                                     peak_states=output["peak_states"],
                                     max_boundary=output["max_boundary"],
                                     transitions=output["transitions"],
                                     jones_polynomial=output["jones_polynomial"]))
                comparisons += 1
            row = dict(name=name, mirrored=mirrored, crossings=d.crossings,
                       writhe=d.writhe(), source=provenance, pd=d.pd, regina_pd=pd,
                       regina_x_polynomial=sorted(raw.items()),
                       expected_t_polynomial=sorted(expected.items()), variants=variants)
            if provenance["kind"] == "baseline_residual_twist_replication":
                a, b = jvp_from_x_polynomial(raw)
                degree = max(set(a) | set(b))
                length = provenance["residual_length"]
                assert degree == 2*length+(6 if mirrored else 5)
                row["jvp"] = dict(a=sorted(a.items()), b=sorted(b.items()), degree=degree,
                                  fixed_cap=22, exceeds_fixed_cap=degree > 22,
                                  meaning="replicates obstruction to joint prerequisite claims; "
                                          "not a counterexample to Jones detection")
            rows.append(row)

    files = ("fastunknot/tensor_jones.py", "fastunknot/diagram.py",
             "fastunknot/separator_order.py", "jones_research/audit_residual_twists.py")
    result = dict(status="PASS", utc=datetime.now(timezone.utc).isoformat(),
                  audit="independent-Regina-full-Jones-polynomial-v1",
                  scope="full coefficient equality on a finite deterministic corpus; no timing claim",
                  regina_runtime_version=regina.versionString(),
                  regina_distribution_version=metadata.version("regina"),
                  regina_algorithm="Treewidth", python=sys.version, platform=platform.platform(),
                  random_seed=seed, base_cases=len(cases), diagram_variants=len(rows),
                  full_polynomial_comparisons=comparisons, all_matches=True,
                  convention="Regina x=sqrt(t); exponent e maps to t exponent e/2; no mirror inversion",
                  calibration=calibration,
                  source_sha256={p: sha256((fast/p).read_bytes()).hexdigest() for p in files},
                  audit_script_sha256=sha256(Path(__file__).read_bytes()).hexdigest(), rows=rows)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2)+"\n")
    print(json.dumps({k: result[k] for k in ("status", "base_cases", "diagram_variants",
                     "full_polynomial_comparisons", "all_matches")}))


if __name__ == "__main__":
    main()
