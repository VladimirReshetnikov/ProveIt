"""Compile source-authenticated bordered bundle attachments to a small matrix.

This module is a conditional geometric adapter, not a source authenticator.
The caller must authenticate geometry, summary, and skeleton with the source
parallelity and ordered-boundary verifiers before using its result as a proof.
Every core occurrence is geometric and unsigned.  No words are freely reduced.
"""

from collections import Counter


def _integer(value, *, minimum=None):
    if type(value) is not int or (minimum is not None and value < minimum):
        raise ValueError("invalid geometric integer")
    return value


def _forest(core, check):
    vertices, edges = core["handles0"], core["handles1"]
    if any(type(h["id"]) is not int or h["id"] != i
           for i, h in enumerate(vertices)):
        raise ValueError("noncanonical core zero-handle labels")
    parent = list(range(len(vertices)))

    def root(v):
        while parent[v] != v:
            parent[v] = parent[parent[v]]
            v = parent[v]
        return v

    tree = []
    for number, handle in enumerate(edges):
        check()
        if type(handle["id"]) is not int or handle["id"] != number:
            raise ValueError("noncanonical core one-handle labels")
        if type(handle["ends"]) not in (list, tuple) or len(handle["ends"]) != 2:
            raise ValueError("invalid one-handle ends")
        a, b = handle["ends"]
        _integer(a, minimum=0)
        _integer(b, minimum=0)
        if a >= len(vertices) or b >= len(vertices):
            raise ValueError("one-handle end outside core")
        a, b = root(a), root(b)
        if a != b:
            parent[max(a, b)] = min(a, b)
            tree.append(number)
    return tree, [root(v) for v in range(len(vertices))]


def _port_path(geometry, letter, check):
    """One midpoint segment, using source face flags even for self-pairings."""
    check()
    _integer(letter)
    if not letter or abs(letter) > len(geometry["ports"]):
        raise ValueError("invalid signed interface port")
    number = abs(letter) - 1
    port = geometry["ports"][number]
    if type(port["id"]) is not int or port["id"] != number:
        raise ValueError("noncanonical port labels")
    dimension = _integer(port["core_dimension"], minimum=0)
    handle = _integer(port["core_handle"], minimum=0)
    if dimension == 0:
        if handle >= len(geometry["core"]["handles0"]):
            raise ValueError("invalid zero-handle port")
        return handle, handle, None
    if dimension != 1 or handle >= len(geometry["core"]["handles1"]):
        raise ValueError("unsupported core-facing port dimension")
    polygon = geometry["polygons"][port["polygon"]]
    edge = port["edge"]
    if polygon["kind"] != "edge_cap" or polygon["edges"][edge]["kind"] != "face_sector":
        raise ValueError("one-handle port lacks its source face sector")
    h = geometry["core"]["handles1"][handle]
    ends = [(h["tetrahedron"], h["face"]),
            (h["target_tetrahedron"], h["target_face"])]
    flags = [(polygon["vertices"][(edge + j) % len(polygon["vertices"])]["tetrahedron"],
              polygon["vertices"][(edge + j) % len(polygon["vertices"])]["face"])
             for j in (0, 1)]
    if ends[0] == ends[1]:
        raise ValueError("one-handle face flags do not distinguish its ends")
    if flags == ends:
        sign = 1
    elif flags == ends[::-1]:
        sign = -1
    else:
        raise ValueError("face-sector flags do not match the core handle")
    sign *= 1 if letter > 0 else -1
    start, stop = h["ends"][::sign]
    return start, stop, dict(port=number, handle=handle, sign=sign,
                             start=start, stop=stop)


def compile_relative_bundles(geometry, summary, skeleton, *, check=lambda: None):
    """Return the active incidence matrix and binary private-handle counts.

    READY means the finite relative presentation was compiled; it is not a
    handlebody conclusion.  All rows still require a verified full cancellation
    schedule.  Closed bases and core three-handles remain INCONCLUSIVE.
    """
    check()
    result = dict(status="INCONCLUSIVE",
                  trust="requires authenticated source charts and boundary skeleton")
    core = geometry["core"]
    if core["handles3"]:
        return dict(result, reason="core_has_three_handles")
    tree, component = _forest(core, check)
    tree_set = set(tree)
    profiles = summary["base_profiles"]
    by_port = {}
    for i, profile in enumerate(profiles):
        check()
        boundary = _integer(profile["boundary_components"], minimum=0)
        if not boundary:
            return dict(result, reason="closed_bundle_base")
        chi = _integer(profile["euler_characteristic"])
        copies = _integer(profile["multiplicity"], minimum=1)
        if type(profile["orientable"]) is not bool:
            raise ValueError("invalid base orientation flag")
        crosscap_rank = 2 - boundary - chi
        if (crosscap_rank < 0 or
                (profile["orientable"] and crosscap_rank % 2) or
                (not profile["orientable"] and crosscap_rank < 1)):
            raise ValueError("inconsistent bordered-surface profile")
        if profile["core_ports"] and copies != 1:
            raise ValueError("ported component must have actual multiplicity one")
        for p in profile["core_ports"]:
            _integer(p, minimum=0)
            if p >= len(geometry["ports"]) or p in by_port:
                raise ValueError("invalid or multiply owned source port")
            by_port[p] = i
    if set(by_port) != set(range(len(geometry["ports"]))):
        raise ValueError("base profiles do not partition all source ports")

    rows, row_owner = {}, {}
    for number, handle in enumerate(core["handles2"]):
        check()
        if type(handle["id"]) is not int or handle["id"] != number:
            raise ValueError("noncanonical core two-handle labels")
        row, owners = {}, set()
        for flag in handle["cycle"]:
            dimension = _integer(flag["dimension"], minimum=0)
            name = _integer(flag["handle"], minimum=0)
            if dimension == 0:
                if name >= len(component):
                    raise ValueError("two-handle vertex outside core")
                owners.add(component[name])
            elif dimension == 1:
                if name >= len(core["handles1"]):
                    raise ValueError("two-handle edge outside core")
                owners.add(component[core["handles1"][name]["ends"][0]])
                if name not in tree_set:
                    row[name] = min(2, row.get(name, 0) + 1)
            else:
                raise ValueError("invalid two-handle source cycle")
        if len(owners) != 1:
            return dict(result, reason="unsupported_empty_or_disconnected_core_cycle")
        rows[number], row_owner[number] = row, owners.pop()

    attachments, per_base, used_ports = [], [[] for _ in profiles], set()
    for index, attachment in enumerate(skeleton["attachment_components"]):
        check()
        if attachment["kind"] not in ("interval", "circle") or not attachment["word"]:
            raise ValueError("invalid maximal attaching component")
        ports = [abs(_integer(x)) - 1 for x in attachment["word"]]
        if any(p < 0 or p not in by_port or p in used_ports for p in ports):
            raise ValueError("interface port is absent or repeated")
        if len(set(ports)) != len(ports):
            raise ValueError("interface repeats a source port")
        used_ports.update(ports)
        owners = {by_port[p] for p in ports}
        if len(owners) != 1:
            raise ValueError("connected interface crosses bundle components")
        base = owners.pop()
        paths = [_port_path(geometry, letter, check) for letter in attachment["word"]]
        if any(paths[j][1] != paths[j + 1][0] for j in range(len(paths) - 1)):
            raise ValueError("midpoint interface path is not source-continuous")
        if attachment["kind"] == "circle" and paths[-1][1] != paths[0][0]:
            raise ValueError("midpoint circle fails to close in core charts")
        core_owners = {component[v] for path in paths for v in path[:2]}
        if len(core_owners) != 1:
            raise ValueError("connected interface has more than one core owner")
        record = dict(attachment=index, base_profile=base,
                      core_component=core_owners.pop(), kind=attachment["kind"],
                      crossings=[p[2] for p in paths if p[2] is not None])
        attachments.append(record)
        per_base[base].append(index)
    if used_ports != set(by_port):
        raise ValueError("ordered interfaces do not partition all source ports")

    base_records, isolated = [], []
    for base, profile in enumerate(profiles):
        check()
        indices = per_base[base]
        if not indices:
            if profile["core_ports"]:
                raise ValueError("ported bundle lost its attachments")
            isolated.append(dict(base_profile=base,
                                 genus=1 - profile["euler_characteristic"],
                                 multiplicity=profile["multiplicity"]))
            continue
        a = sum(attachments[j]["kind"] == "interval" for j in indices)
        c = len(indices) - a
        boundary = profile["boundary_components"]
        if c > boundary or (c == boundary and a):
            raise ValueError("whole-circle classification contradicts base boundary")
        saturated = c == boundary
        h = a - profile["euler_characteristic"] + int(saturated)
        if h < len(indices) - 1:
            raise ValueError("negative relative band cycle rank")
        row_id = None
        if saturated:
            row_id = len(rows)
            row = {}
            for index in indices:
                for crossing in attachments[index]["crossings"]:
                    handle = crossing["handle"]
                    if handle not in tree_set:
                        row[handle] = min(2, row.get(handle, 0) + 1)
            rows[row_id] = row
            row_owner[row_id] = attachments[indices[0]]["core_component"]
        base_records.append(dict(base_profile=base, attachments=indices,
                                 interval_components=a, circle_components=c,
                                 saturated=saturated, relative_one_handles=h,
                                 residual_row=row_id))

    # Only explicit interface incidences enter this union-find.  Numerical
    # genus and unported multiplicity never become graph vertices or loops.
    core_labels = sorted(set(component))
    parent = {c: c for c in core_labels}

    def root(c):
        while parent[c] != c:
            parent[c] = parent[parent[c]]
            c = parent[c]
        return c

    for base in base_records:
        owners = [attachments[j]["core_component"] for j in base["attachments"]]
        first = owners[0]
        for c in owners[1:]:
            x, y = root(first), root(c)
            if x != y:
                parent[max(x, y)] = min(x, y)
    groups = {}
    for c in core_labels:
        groups.setdefault(root(c), []).append(c)
    joined = []
    for representative, core_ids in sorted(groups.items()):
        check()
        selected = [b for b in base_records
                    if root(attachments[b["attachments"][0]]["core_component"]) == representative]
        selected_indices = [a["attachment"] for a in attachments
                            if root(a["core_component"]) == representative]
        active = [h["id"] for h in core["handles1"]
                  if h["id"] not in tree_set and root(component[h["ends"][0]]) == representative]
        disc_rows = sorted(r for r, owner in row_owner.items() if root(owner) == representative)
        private = sum(b["relative_one_handles"] for b in selected) - len(core_ids) + 1
        if private < 0:
            raise ValueError("relative-band graph cannot connect its claimed cores")
        rank = len(active) + private
        joined.append(dict(id=representative, core_components=core_ids,
                           zero_handles=[v for v, c in enumerate(component) if root(c) == representative],
                           base_profiles=[b["base_profile"] for b in selected],
                           attachments=selected_indices, active_one_handles=active,
                           two_handle_rows=disc_rows, private_one_handles=private,
                           one_handle_rank=rank, genus_if_complete=rank - len(disc_rows)))

    source_euler = (_integer(summary["core_euler_characteristic"]) +
                    _integer(summary["bundle_euler_characteristic"]) -
                    _integer(summary["attachment_euler_characteristic"]))
    counted = sum(1 - c["genus_if_complete"] for c in joined)
    counted += sum((1 - p["genus"]) * p["multiplicity"] for p in isolated)
    if source_euler != counted:
        raise ValueError("relative presentation violates authenticated source Euler identity")
    proof = dict(schema="saturated-bundle-incidence-v1", forest=tree,
                 attachments=attachments, bases=base_records,
                 rows=[dict(id=r, counts=[[c, v] for c, v in sorted(row.items())])
                       for r, row in sorted(rows.items())],
                 joined_components=joined, isolated_bundles=isolated,
                 source_euler_characteristic=source_euler)
    check()
    return dict(status="READY", counts=rows, certificate=proof,
                joined_components=joined, isolated_bundles=isolated,
                stats=dict(active_rows=len(rows),
                           active_columns=len(core["handles1"]) - len(tree),
                           active_entries=sum(len(row) for row in rows.values()),
                           saturated_bases=sum(b["saturated"] for b in base_records),
                           private_one_handles=sum(c["private_one_handles"] for c in joined)))


def census_after_complete_cancellation(compilation, *, check=lambda: None):
    """Arithmetic census; caller must already verify all compiled rows vanish."""
    check()
    if compilation.get("status") != "READY":
        raise ValueError("relative presentation was not compiled")
    histogram = Counter()
    for component in compilation["joined_components"]:
        genus = component["genus_if_complete"]
        if genus < 0:
            raise ValueError("impossible full-row cancellation census")
        histogram[genus] += 1
    for bundle in compilation["isolated_bundles"]:
        histogram[bundle["genus"]] += bundle["multiplicity"]
    euler = sum((1 - genus) * count for genus, count in histogram.items())
    if euler != compilation["certificate"]["source_euler_characteristic"]:
        raise ValueError("cancellation census violates source Euler identity")
    return dict(histogram=[dict(genus=g, multiplicity=m) for g, m in sorted(histogram.items())],
                components=sum(histogram.values()), ball_components=histogram.get(0, 0),
                all_balls=all(g == 0 for g in histogram), euler_characteristic=euler)
