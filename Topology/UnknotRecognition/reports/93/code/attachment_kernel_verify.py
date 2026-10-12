"""Independent graph-theoretic checker; imports no producer code."""

import hashlib
import json


def _same(left, right):
    if type(left) is not type(right):
        return False
    if type(left) is dict:
        return left.keys() == right.keys() and all(_same(left[k], right[k]) for k in left)
    if type(left) is list:
        return len(left) == len(right) and all(_same(a, b) for a, b in zip(left, right))
    return left == right


def verify_attachment_kernel(vertices, edges, certificate, *, check=lambda: None):
    """Check every source edge, rooted-tree relation and retained incidence.

    Returns a boolean.  A True value does not establish irreducibility or
    authorize a topological interpretation of Euler-characteristic labels.
    The certificate is linear in the source network even when the operational
    kernel has only O(genus) entries.
    """
    try:
        check()
        vs = sorted([[r["id"], r["euler_characteristic"]] for r in vertices])
        es = sorted([[r["id"], *r["ends"]] for r in edges])
        if not vs or any(len(r) != 2 for r in vs) or any(len(r) != 3 for r in es):
            return False
        if any(type(x) is not int for r in vs + es for x in r):
            return False
        chi = dict(vs)
        if len(chi) != len(vs) or any(v < 0 or c > 1 for v, c in vs):
            return False
        edge_map = {e: (u, v) for e, u, v in es}
        if len(edge_map) != len(es) or any(e < 0 or u not in chi or v not in chi
                                                for e, u, v in es):
            return False
        source = {"vertices": vs, "edges": es}
        digest = hashlib.sha256(json.dumps(source, sort_keys=True,
                                          separators=(",", ":")).encode()).hexdigest()
        if certificate["schema"] != "unused-attachment-kernel-v1":
            return False
        if certificate["input_sha256"] != digest:
            return False
        roots = [v for v, c in vs if c <= 0]
        nonball_count = len(roots)
        if not roots:
            roots = [vs[0][0]]
        fs = certificate["forest_edges"]
        if any(type(e) is not int or e not in edge_map for e in fs):
            return False
        if len(fs) != len(set(fs)) or len(fs) != len(vs) - len(roots):
            return False
        tree = {v: [] for v in chi}
        for e in fs:
            u, v = edge_map[e]
            if u == v:
                return False
            tree[u].append((v, e))
            tree[v].append((u, e))
        mapping, parent_rows = {}, []
        for r in roots:
            stack = [(r, None, None)]
            while stack:
                check()
                v, previous, eid = stack.pop()
                if v in mapping:
                    return False
                mapping[v] = r
                parent_rows.append([v, previous, eid])
                for w, e in tree[v]:
                    if w != previous:
                        stack.append((w, v, e))
        if len(mapping) != len(vs):
            return False
        if not _same(sorted(parent_rows), certificate["parent_forest"]):
            return False
        if not _same([[v, mapping[v]] for v in sorted(chi)], certificate["vertex_roots"]):
            return False
        fset = set(fs)
        kept = [[e, mapping[u], mapping[v]] for e, u, v in es if e not in fset]
        adj = {r: [] for r in roots}
        for _, u, v in kept:
            adj[u].append(v)
            adj[v].append(u)
        reached, todo = set(), [roots[0]]
        while todo:
            v = todo.pop()
            if v in reached:
                continue
            reached.add(v)
            todo.extend(w for w in adj[v] if w not in reached)
        if len(reached) != len(roots):
            return False
        beta = len(es) - len(vs) + 1
        deficit = beta + sum(1 - c for _, c in vs)
        expected = {
            "vertices": [[r, chi[r]] for r in roots],
            "edges": kept,
            "cycle_rank": beta,
            "euler_deficit": deficit,
            "nonball_type_vertices": nonball_count,
            "case": "all_ball_types" if not nonball_count else "retained_nonball_types",
        }
        if not _same(certificate["kernel"], expected):
            return False
        if beta < 0 or len(kept) - len(roots) + 1 != beta:
            return False
        if nonball_count:
            return nonball_count <= deficit and len(kept) <= deficit - 1
        return len(roots) == 1 and len(kept) == deficit
    except (KeyError, TypeError, ValueError, IndexError):
        return False
