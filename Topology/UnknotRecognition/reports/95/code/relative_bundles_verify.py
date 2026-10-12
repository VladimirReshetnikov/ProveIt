"""Independent replay of the saturated bundle incidence compilation.

No producer, scheduler, or group-word routine is imported.  The caller first
authenticates and decodes the original source geometry, profiles, and skeleton.
This verifier reconstructs all finite matrix and rank data from those inputs.
"""


def _same(a, b):
    if type(a) is not type(b):
        return False
    if isinstance(a, dict):
        return a.keys() == b.keys() and all(_same(a[k], b[k]) for k in a)
    if isinstance(a, list):
        return len(a) == len(b) and all(_same(x, y) for x, y in zip(a, b))
    return a == b


def _components(vertices, adjacency, check):
    remaining, answer = set(vertices), []
    while remaining:
        check()
        todo, seen = [min(remaining)], set()
        while todo:
            current = todo.pop()
            if current in seen:
                continue
            seen.add(current)
            todo.extend(adjacency[current])
        remaining.difference_update(seen)
        answer.append(sorted(seen))
    return answer


class _CallbackFailure(BaseException):
    """Keep caller cancellation/errors outside malformed-certificate handling."""


def replay_relative_bundle_compilation(geometry, summary, skeleton, certificate,
                                       *, check=lambda: None):
    """Return certified counts/ranks, or None; no knot/handlebody claim alone."""
    def guarded_check():
        try:
            check()
        except BaseException as error:
            raise _CallbackFailure(error, error.__traceback__) from None

    try:
        guarded_check()
        return _replay(geometry, summary, skeleton, certificate, guarded_check)
    except _CallbackFailure as failure:
        error, traceback = failure.args
        raise error.with_traceback(traceback) from None
    except (KeyError, IndexError, TypeError, ValueError):
        return None


def _replay(g, summary, skeleton, proof, check):
    fields = {"schema", "forest", "attachments", "bases", "rows", "joined_components",
              "isolated_bundles", "source_euler_characteristic"}
    if type(proof) is not dict or set(proof) != fields:
        return None
    if proof["schema"] != "saturated-bundle-incidence-v1":
        return None
    core = g["core"]
    if core["handles3"]:
        return None
    zero, one, two = [core["handles" + str(i)] for i in range(3)]
    if any(type(h["id"]) is not int or h["id"] != j
           for handles in (zero, one, two) for j, h in enumerate(handles)):
        return None
    graph = {v: [] for v in range(len(zero))}
    for handle in one:
        a, b = handle["ends"]
        if any(type(v) is not int or not 0 <= v < len(zero) for v in (a, b)):
            return None
        graph[a].append(b)
        graph[b].append(a)
    core_sets = _components(graph, graph, check)
    owners = {v: part[0] for part in core_sets for v in part}

    # Check the supplied original-core forest by its connected components and
    # edge count, rather than reproducing the producer's union-find choices.
    forest = proof["forest"]
    if (type(forest) is not list or
            any(type(e) is not int or not 0 <= e < len(one) for e in forest) or
            len(set(forest)) != len(forest)):
        return None
    forest_graph = {v: [] for v in graph}
    for e in forest:
        a, b = one[e]["ends"]
        forest_graph[a].append(b)
        forest_graph[b].append(a)
    if _components(forest_graph, forest_graph, check) != core_sets:
        return None
    if len(forest) != len(zero) - len(core_sets):
        return None
    forest_set = set(forest)

    profiles, port_owner = summary["base_profiles"], {}
    for base, profile in enumerate(profiles):
        check()
        b, chi, m = [profile[k] for k in
                     ("boundary_components", "euler_characteristic", "multiplicity")]
        if any(type(n) is not int for n in (b, chi, m)) or b <= 0 or m <= 0:
            return None
        orientable = profile["orientable"]
        defect = 2 - chi - b
        if type(orientable) is not bool or defect < 0:
            return None
        if (orientable and defect % 2) or (not orientable and defect < 1):
            return None
        if profile["core_ports"] and m != 1:
            return None
        for port in profile["core_ports"]:
            if type(port) is not int or not 0 <= port < len(g["ports"]) or port in port_owner:
                return None
            port_owner[port] = base
    if set(port_owner) != set(range(len(g["ports"]))):
        return None

    seen_ports, attachments = set(), []
    for index, interface in enumerate(skeleton["attachment_components"]):
        check()
        kind, word = interface["kind"], interface["word"]
        if kind not in ("circle", "interval") or not word:
            return None
        local_bases, local_cores, path, crosses = set(), set(), [], []
        for signed in word:
            check()
            if type(signed) is not int or not signed or abs(signed) > len(g["ports"]):
                return None
            p = abs(signed) - 1
            if p in seen_ports:
                return None
            seen_ports.add(p)
            local_bases.add(port_owner[p])
            port = g["ports"][p]
            if type(port["id"]) is not int or port["id"] != p:
                return None
            d, h = port["core_dimension"], port["core_handle"]
            if type(d) is not int or type(h) is not int or h < 0:
                return None
            if d == 0:
                if h >= len(zero):
                    return None
                a = b = h
            elif d == 1:
                if h >= len(one):
                    return None
                handle = one[h]
                polygon = g["polygons"][port["polygon"]]
                edge = port["edge"]
                if polygon["kind"] != "edge_cap" or polygon["edges"][edge]["kind"] != "face_sector":
                    return None
                directions = {(handle["tetrahedron"], handle["face"]): 0,
                              (handle["target_tetrahedron"], handle["target_face"]): 1}
                if len(directions) != 2:
                    return None
                vertices = [polygon["vertices"][(edge + j) % len(polygon["vertices"])]
                            for j in range(2)]
                positions = [directions.get((v["tetrahedron"], v["face"])) for v in vertices]
                if positions not in ([0, 1], [1, 0]):
                    return None
                if signed < 0:
                    positions.reverse()
                a, b = [handle["ends"][j] for j in positions]
                crosses.append(dict(port=p, handle=h, sign=1 if positions[0] == 0 else -1,
                                    start=a, stop=b))
            else:
                return None
            local_cores.update((owners[a], owners[b]))
            path.append((a, b))
        if len(local_bases) != 1 or len(local_cores) != 1:
            return None
        limit = len(path) if kind == "circle" else len(path) - 1
        if any(path[j][1] != path[(j + 1) % len(path)][0] for j in range(limit)):
            return None
        attachments.append(dict(attachment=index, base_profile=next(iter(local_bases)),
                                core_component=next(iter(local_cores)), kind=kind,
                                crossings=crosses))
    if seen_ports != set(port_owner) or not _same(proof["attachments"], attachments):
        return None

    matrix, row_core = {}, {}
    for handle in two:
        check()
        row, row_owners = {}, set()
        for flag in handle["cycle"]:
            d, h = flag["dimension"], flag["handle"]
            if type(d) is not int or type(h) is not int or h < 0:
                return None
            if d == 0 and h < len(zero):
                row_owners.add(owners[h])
            elif d == 1 and h < len(one):
                row_owners.add(owners[one[h]["ends"][0]])
                if h not in forest_set:
                    row[h] = min(2, row.get(h, 0) + 1)
            else:
                return None
        if len(row_owners) != 1:
            return None
        r = handle["id"]
        matrix[r], row_core[r] = row, next(iter(row_owners))

    bases, isolated = [], []
    for i, profile in enumerate(profiles):
        check()
        attached = [a for a in attachments if a["base_profile"] == i]
        if not attached:
            if profile["core_ports"]:
                return None
            isolated.append(dict(base_profile=i, genus=1 - profile["euler_characteristic"],
                                 multiplicity=profile["multiplicity"]))
            continue
        intervals = len([a for a in attached if a["kind"] == "interval"])
        circles = len(attached) - intervals
        if circles > profile["boundary_components"]:
            return None
        saturated = circles == profile["boundary_components"]
        if saturated and intervals:
            return None
        rank = intervals - profile["euler_characteristic"] + int(saturated)
        if rank < len(attached) - 1:
            return None
        r = None
        if saturated:
            r = len(matrix)
            row = {}
            for interface in attached:
                for segment in interface["crossings"]:
                    e = segment["handle"]
                    if e not in forest_set:
                        row[e] = min(2, row.get(e, 0) + 1)
            matrix[r], row_core[r] = row, attached[0]["core_component"]
        bases.append(dict(base_profile=i, attachments=[a["attachment"] for a in attached],
                          interval_components=intervals, circle_components=circles,
                          saturated=saturated, relative_one_handles=rank, residual_row=r))
    expected_rows = [dict(id=r, counts=[[e, v] for e, v in sorted(row.items())])
                     for r, row in sorted(matrix.items())]
    if (not _same(proof["rows"], expected_rows) or not _same(proof["bases"], bases) or
            not _same(proof["isolated_bundles"], isolated)):
        return None

    # A core-only adjacency graph differs from the producer's union-find.
    # Every pair of owners on one connected base is joined; loops are harmless.
    merged = {part[0]: set() for part in core_sets}
    for base in bases:
        members = {attachments[j]["core_component"] for j in base["attachments"]}
        for x in members:
            merged[x].update(members - {x})
    joined = []
    for part in _components(merged, merged, check):
        part_set = set(part)
        these = [b for b in bases
                 if attachments[b["attachments"][0]]["core_component"] in part_set]
        active = [h["id"] for h in one
                  if h["id"] not in forest_set and owners[h["ends"][0]] in part_set]
        disc_rows = [r for r in sorted(matrix) if row_core[r] in part_set]
        private = sum(b["relative_one_handles"] for b in these) + 1 - len(part)
        if private < 0:
            return None
        rank = len(active) + private
        joined.append(dict(id=part[0], core_components=part,
                           zero_handles=[v for v in range(len(zero)) if owners[v] in part_set],
                           base_profiles=[b["base_profile"] for b in these],
                           attachments=[a["attachment"] for a in attachments
                                        if a["core_component"] in part_set],
                           active_one_handles=active, two_handle_rows=disc_rows,
                           private_one_handles=private, one_handle_rank=rank,
                           genus_if_complete=rank - len(disc_rows)))
    if not _same(proof["joined_components"], joined):
        return None
    numbers = [summary[k] for k in ("core_euler_characteristic",
                                    "bundle_euler_characteristic",
                                    "attachment_euler_characteristic")]
    if any(type(n) is not int for n in numbers):
        return None
    source_euler = numbers[0] + numbers[1] - numbers[2]
    rank_euler = sum(1 - c["genus_if_complete"] for c in joined)
    rank_euler += sum(p["multiplicity"] * (1 - p["genus"]) for p in isolated)
    if not _same(proof["source_euler_characteristic"], source_euler) or rank_euler != source_euler:
        return None
    check()
    return dict(status="READY", counts=matrix, certificate=proof,
                joined_components=joined, isolated_bundles=isolated)
