"""Reproducible exact finite diagnostics, including empty objects and diagrams."""
import json
from itertools import product
from pathlib import Path
from finite_categories import (
    Category, SetDiagram, thin_category, cyclic_group, functor_category,
    limit, colimit, representable, all_natural_sets, yoneda_expand,
    yoneda_extract, curry, uncurry,
)


def run():
    counts = {"category_and_opposite_checks": 0, "malformed_category_rejections": 0, "functor_categories": 0,
              "yoneda_presentations": 0, "yoneda_natural_transformations": 0,
              "limit_cones": 0, "colimit_cocones": 0, "exponential_round_trips": 0}
    empty = thin_category(0, lambda x, y: x == y)
    point = thin_category(1, lambda x, y: x == y)
    arrow = thin_category(2, lambda x, y: x <= y)
    discrete = thin_category(2, lambda x, y: x == y)
    chain = thin_category(3, lambda x, y: x <= y)
    groupoid = thin_category(2, lambda x, y: True)
    c2 = cyclic_group(2)
    c3 = cyclic_group(3)
    parallel = Category(2, (0, 1, 0, 0), (0, 1, 1, 1), (0, 1),
                        ((0, -1, -1, -1), (-1, 1, 2, 3),
                         (2, -1, -1, -1), (3, -1, -1, -1)))
    cats = (empty, point, arrow, discrete, chain, groupoid, c2, c3, parallel)
    for c in cats:
        assert c.valid() and c.opposite().valid() and c.opposite().opposite() == c
        counts["category_and_opposite_checks"] += 1
    for bad in (Category(1, (0, 0), (0, 0), (0,), ((0, 0), (1, 7))),
                Category(0, (0,), (0,), (), ((0,),)),
                Category(1, (0,), (0,), (2,), ((0,),)),
                Category(1, (0,), (0,), (0,), ())):
        assert not bad.valid()
        counts["malformed_category_rejections"] += 1
    for c, d in ((empty, empty), (point, empty), (empty, point),
                 (arrow, arrow), (arrow, chain), (c2, c2), (groupoid, groupoid)):
        assert functor_category(c, d).valid()
        counts["functor_categories"] += 1

    presheaves = []
    for c in cats:
        for a in range(c.objects):
            presheaves.append(representable(c, a)[0])
        for n in (0, 1, 2):
            presheaves.append(SetDiagram(c, (n,) * c.objects,
                                        (tuple(range(n)),) * c.arrows, True))
    presheaves += [
        SetDiagram(arrow, (2, 3), ((0, 1), (0, 0, 1), (0, 1, 2)), True),
        SetDiagram(c2, (3,), ((0, 1, 2), (1, 0, 2)), True),
        SetDiagram(parallel, (2, 3), ((0, 1), (0, 1, 2), (0, 1, 0), (0, 0, 1)), True),
    ]
    for p in presheaves:
        assert p.valid()
        c = p.category
        for a in range(c.objects):
            r, _ = representable(c, a)
            natural = all_natural_sets(r, p)
            expanded = tuple(yoneda_expand(p, a, u) for u in range(p.sizes[a]))
            assert set(natural) == set(expanded)
            assert len(natural) == p.sizes[a]
            for e in natural:
                assert yoneda_expand(p, a, yoneda_extract(c, a, e)) == e
                counts["yoneda_natural_transformations"] += 1
            for u in range(p.sizes[a]):
                assert yoneda_extract(c, a, yoneda_expand(p, a, u)) == u
            counts["yoneda_presentations"] += 1

    diagrams = [
        SetDiagram(empty, (), ()),
        SetDiagram(point, (0,), ((),)),
        SetDiagram(point, (3,), ((0, 1, 2),)),
        SetDiagram(discrete, (2, 3), ((0, 1), (0, 1, 2))),
        SetDiagram(arrow, (3, 2), ((0, 1, 2), (0, 0, 1), (0, 1))),
        SetDiagram(c2, (3,), ((0, 1, 2), (1, 0, 2))),
        SetDiagram(parallel, (3, 2), ((0, 1, 2), (0, 1), (0, 0, 1), (0, 1, 1))),
    ]
    examples = []
    for d in diagrams:
        assert d.valid()
        c = d.category
        lim = limit(d)
        vertices, classes, quotient = colimit(d)
        index = {v: i for i, v in enumerate(vertices)}
        examples.append({"objects": c.objects, "arrows": c.arrows,
                         "sizes": d.sizes, "limit": lim,
                         "colimit_classes": [[vertices[i] for i, q in enumerate(quotient)
                                               if q == j] for j in range(len(classes))]})
        for size in range(3):
            options = [tuple(product(range(n), repeat=size)) for n in d.sizes]
            for cone in product(*options):
                if all(d.maps[f][cone[c.source[f]][x]] == cone[c.target[f]][x]
                       for f in range(c.arrows) for x in range(size)):
                    lifts = [h for h in product(range(len(lim)), repeat=size)
                             if all(lim[h[x]][j] == cone[j][x]
                                    for x in range(size) for j in range(c.objects))]
                    assert len(lifts) == 1
                    counts["limit_cones"] += 1
            for cocone in product(range(size), repeat=len(vertices)):
                if all(cocone[index[(c.source[f], a)]] == cocone[index[(c.target[f], b)]]
                       for f in range(c.arrows) for a, b in enumerate(d.maps[f])):
                    lifts = [h for h in product(range(size), repeat=len(classes))
                             if all(h[quotient[i]] == cocone[i] for i in range(len(vertices)))]
                    assert len(lifts) == 1
                    counts["colimit_cocones"] += 1
    for m in range(4):
        for n in range(3):
            for k in range(3):
                for table in product(range(m), repeat=k * n):
                    assert uncurry(m, n, curry(m, n, k, table)) == table
                    counts["exponential_round_trips"] += 1
                for codes in product(range(m ** n), repeat=k):
                    assert curry(m, n, k, uncurry(m, n, codes)) == codes
                    counts["exponential_round_trips"] += 1
    result = {"status": "passed", "scope": "exact finite diagnostics, not universal proofs",
              "counts": counts, "limit_colimit_examples": examples}
    dest = Path(__file__).resolve().parents[1] / "validation" / "category_checks.json"
    dest.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    run()
