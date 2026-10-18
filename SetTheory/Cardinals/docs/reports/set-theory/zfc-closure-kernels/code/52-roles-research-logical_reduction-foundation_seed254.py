#!/usr/bin/env python3
"""Sufficient semantic startup certificates for the original 254 calculus.

Positive results mean that every nonhalting initial formula field is true
uniformly in every model of ZFC.  They do not mean that the formula is a C254
theorem.  The original all-state completeness theorem plus the semantic
soundness invariant gives a paper-level ZFC consistency calibration from any
whole root frame accepted here.  Binary startup is a separate obligation.

The new finite decision procedure handles quantifier-free formula cores by
enumerating equality partitions of their variable names and acyclic choices
of just the queried membership edges.  It allows leading universal prefixes.
The unchanged upstream syntactic seed checker is used as an optional fallback.

All codes use the literal four-tag, unshifted dual-Cantor representation.
Zero is the original truth alias; one is Rel(0,0), false in every ZFC model.
"""
from __future__ import annotations

import argparse
from functools import lru_cache
import importlib.util
import itertools
import json
from math import isqrt
from pathlib import Path


def pair(a: int, b: int) -> int:
    return (a + b) * (a + b + 1) // 2 + b


def unpair(n: int) -> tuple[int, int]:
    if type(n) is not int or n < 0:
        raise ValueError("natural number required")
    d = (isqrt(8 * n + 1) - 1) // 2
    b = n - d * (d + 1) // 2
    return d - b, b


def imp(a: int, b: int) -> int:
    return 4 * pair(a, b)


def mem(a: int, b: int) -> int:
    return 4 * pair(a, b) + 1


def eq(a: int, b: int) -> int:
    return 4 * pair(a, b) + 3


def all_(a: int, body: int) -> int:
    return 4 * pair(a, body) + 2


@lru_cache(maxsize=None)
def decode(n: int) -> tuple:
    if type(n) is not int or n < 0:
        raise ValueError("natural formula code required")
    if n == 0:
        return ("true",)
    tag = n % 4
    a, b = unpair(n // 4)
    if tag == 0:
        return ("imp", decode(a), decode(b))
    if tag == 1:
        return ("mem", a, b)
    if tag == 2:
        return ("all", a, decode(b))
    return ("eq", a, b)


def encode(f: tuple) -> int:
    tag = f[0]
    if tag == "true":
        return 0
    if tag == "imp":
        return imp(encode(f[1]), encode(f[2]))
    if tag == "mem":
        return mem(f[1], f[2])
    if tag == "all":
        return all_(f[1], encode(f[2]))
    if tag == "eq":
        return eq(f[1], f[2])
    raise ValueError(tag)


def qf_names(f: tuple) -> set[int] | None:
    tag = f[0]
    if tag == "true":
        return set()
    if tag in ("mem", "eq"):
        return {f[1], f[2]}
    if tag == "all":
        return None
    a, b = qf_names(f[1]), qf_names(f[2])
    return None if a is None or b is None else a | b


def partitions(size: int):
    """Restricted-growth strings enumerate each set partition exactly once."""
    if size == 0:
        yield ()
        return
    def visit(word: tuple[int, ...], maximum: int):
        if len(word) == size:
            yield word
        else:
            for value in range(maximum + 2):
                yield from visit(word + (value,), max(maximum, value))
    yield from visit((0,), 0)


def queried_edges(f: tuple, assignment: dict[int, int]) -> set[tuple[int, int]]:
    tag = f[0]
    if tag == "mem":
        a, b = assignment[f[1]], assignment[f[2]]
        return set() if a == b else {(a, b)}
    if tag == "imp":
        return queried_edges(f[1], assignment) | queried_edges(f[2], assignment)
    return set()


def acyclic(vertices: int, edges: set[tuple[int, int]]) -> bool:
    indegree = [0] * vertices
    outgoing = [[] for _ in range(vertices)]
    for a, b in edges:
        if a == b:
            return False
        outgoing[a].append(b)
        indegree[b] += 1
    pending = [i for i, n in enumerate(indegree) if n == 0]
    seen = 0
    while pending:
        a = pending.pop()
        seen += 1
        for b in outgoing[a]:
            indegree[b] -= 1
            if indegree[b] == 0:
                pending.append(b)
    return seen == vertices


def evaluate_qf(f: tuple, assignment: dict[int, int], edges: set[tuple[int, int]]) -> bool:
    tag = f[0]
    if tag == "true":
        return True
    if tag == "eq":
        return assignment[f[1]] == assignment[f[2]]
    if tag == "mem":
        return (assignment[f[1]], assignment[f[2]]) in edges
    if tag == "imp":
        return not evaluate_qf(f[1], assignment, edges) or evaluate_qf(f[2], assignment, edges)
    raise ValueError("not quantifier free")


def realize_pattern(names: list[int], partition: tuple[int, ...], edges: set[tuple[int, int]]) -> dict:
    """Induced embedding into HF, represented by an extensional finite set DAG.

    The i-th vertex is x_i={t_i} union {x_j : j->i}, with equal-rank distinct
    tags t_i={i,m}. Each row lists the node IDs of its actual set members.
    Interning child-ID sets makes this a real extensional HF construction,
    rather than interpreting an arbitrary directed graph as membership.
    """
    m = max(partition, default=-1) + 1
    assert m > 0 and acyclic(m, edges)
    nodes: list[list[int]] = []
    interned: dict[tuple[int, ...], int] = {}

    def intern(children):
        key = tuple(sorted(set(children)))
        if key not in interned:
            label = len(nodes)
            assert all(child < label for child in key)
            interned[key] = label
            nodes.append(list(key))
        return interned[key]

    ordinals = []
    for i in range(m + 1):
        ordinals.append(intern(ordinals))
    tags = [intern([ordinals[i], ordinals[m]]) for i in range(m)]
    roots: dict[int, int] = {}
    pending = set(range(m))
    while pending:
        ready = sorted(i for i in pending if all(j in roots for j, k in edges if k == i))
        assert ready
        for i in ready:
            roots[i] = intern([tags[i]] + [roots[j] for j, k in sorted(edges) if k == i])
            pending.remove(i)
    assert len(set(roots.values())) == m
    for a in range(m):
        for b in range(m):
            assert (roots[a] in nodes[roots[b]]) == ((a, b) in edges)
    return {"construction": "HF with distinct tags t_i={i,m}",
            "nodes": nodes, "vertex_nodes": [roots[i] for i in range(m)],
            "valuation": {str(name): roots[part] for name, part in zip(names, partition)}}


def evaluate_hf_witness(n: int, witness: dict) -> bool:
    """Independent literal-code QF evaluation on actual finite-set node IDs."""
    nodes, valuation = witness["nodes"], witness["valuation"]
    def visit(code: int) -> bool:
        if code == 0:
            return True
        tag = code % 4
        a, b = unpair(code // 4)
        if tag == 0:
            return not visit(a) or visit(b)
        if tag == 1:
            return valuation[str(a)] in nodes[valuation[str(b)]]
        if tag == 3:
            return valuation[str(a)] == valuation[str(b)]
        raise ValueError("witness evaluation requires a quantifier-free core")
    return visit(n)


@lru_cache(maxsize=None)
def semantic_core(n: int, max_names: int = 6, max_edges: int = 15) -> dict:
    f = decode(n)
    names_ = qf_names(f)
    if names_ is None:
        return {"status": "unsupported", "reason": "embedded quantifier"}
    names = sorted(names_)
    if len(names) > max_names:
        return {"status": "unsupported", "reason": "name resource cap"}
    partitions_checked = acyclic_cases = cyclic_cases = 0
    for partition in partitions(len(names)):
        assignment = dict(zip(names, partition))
        vertices = max(partition, default=-1) + 1
        possible = sorted(queried_edges(f, assignment))
        if len(possible) > max_edges:
            return {"status": "unsupported", "reason": "edge resource cap"}
        partitions_checked += 1
        for bits in range(1 << len(possible)):
            edges = {e for i, e in enumerate(possible) if (bits >> i) & 1}
            if not acyclic(vertices, edges):
                cyclic_cases += 1
                continue
            acyclic_cases += 1
            if not evaluate_qf(f, assignment, edges):
                witness = realize_pattern(names, partition, edges)
                assert not evaluate_hf_witness(n, witness)
                return {"status": "acyclic_pattern_counterexample", "names": names,
                        "partition": list(partition), "edges": [list(e) for e in sorted(edges)],
                        "partitions_checked": partitions_checked,
                        "acyclic_cases": acyclic_cases, "cyclic_cases_skipped": cyclic_cases,
                        "hereditarily_finite_witness": witness}
    return {"status": "valid", "names": names,
            "partitions_checked": partitions_checked,
            "acyclic_cases": acyclic_cases, "cyclic_cases_skipped": cyclic_cases}


def semantic_fragment(n: int, max_names: int = 6, max_edges: int = 15) -> dict:
    """Complete classification of universal closure of a leading-∀ QF fragment.

    'unsupported' is an unknown result, including every resource cap.
    An HF witness falsifies the quantifier-free core; assigning its free
    names and choosing those witnesses at the leading binders falsifies the
    universally closed input sentence in every model of ZFC.
    """
    prefix = []
    core = n
    while core and core % 4 == 2:
        a, core = unpair(core // 4)
        prefix.append(a)
    return {"code": n, "universal_prefix": prefix, "core_code": core,
            "classification": semantic_core(core, max_names, max_edges)}


@lru_cache(maxsize=None)
def formula(n: int) -> dict | None:
    """Pure semantic certificate.  Failure is not a claim of invalidity."""
    if type(n) is not int or n < 0:
        raise ValueError("natural formula code required")
    if n == 0:
        return {"rule": "truth", "code": n}
    tag = n % 4
    a, b = unpair(n // 4)
    if tag == 2:
        inner = formula(b)
        if inner is not None:
            return {"rule": "all", "code": n, "binder": a, "body": inner}
    if tag == 0:
        if a == b:
            return {"rule": "identity", "code": n, "payload": a}
        if a == 1:
            return {"rule": "exfalso", "code": n, "payload": b}
        inner = formula(b)
        if inner is not None:
            return {"rule": "weaken", "code": n, "antecedent": a, "body": inner}
    result = semantic_core(n)
    if result["status"] == "valid":
        return {"rule": "acyclic_qf", "code": n, "certificate": result}
    return None


def stack(n: int) -> list[dict] | None:
    if type(n) is not int or n < 0:
        raise ValueError("natural stack code required")
    result = []
    while n:
        head, tail = unpair(n)
        cert = formula(head)
        if cert is None:
            return None
        assert tail < n
        result.append(cert)
        n = tail
    return result


def state(logical: list[int]) -> dict | None:
    if len(logical) != 9 or any(type(n) is not int or n < 0 for n in logical):
        raise ValueError("exactly nine natural logical registers required")
    top, cache, cells = formula(logical[1]), formula(logical[5]), stack(logical[2])
    if top is None or cache is None or cells is None:
        return None
    return {"top": top, "cache": cache, "stack": cells}


def independent_finite_valid(n: int, domain: int) -> bool:
    """Cross-check: complete acyclic relations then all assignments, no partitions."""
    f = decode(n)
    names = sorted(qf_names(f) or [])
    pairs = [(a, b) for a in range(domain) for b in range(domain) if a != b]
    for bits in range(1 << len(pairs)):
        edges = {e for i, e in enumerate(pairs) if (bits >> i) & 1}
        # Independent cycle criterion: transitive closure has no diagonal.
        reach = [[(a, b) in edges for b in range(domain)] for a in range(domain)]
        for k in range(domain):
            for a in range(domain):
                for b in range(domain):
                    reach[a][b] = reach[a][b] or (reach[a][k] and reach[k][b])
        if any(reach[a][a] for a in range(domain)):
            continue
        for values in itertools.product(range(domain), repeat=len(names)):
            if not evaluate_qf(f, dict(zip(names, values)), edges):
                return False
    return True


@lru_cache(maxsize=None)
def free_names_code(n: int) -> frozenset[int]:
    """Free names directly from literal codes, separate from AST traversal."""
    if n == 0:
        return frozenset()
    tag = n % 4
    a, b = unpair(n // 4)
    if tag in (1, 3):
        return frozenset((a, b))
    if tag == 2:
        return free_names_code(b) - {a}
    return free_names_code(a) | free_names_code(b)


def hf_satisfies(n: int, valuation: dict[int, int], domain: tuple[int, ...]) -> bool:
    """Literal-code model evaluator; Ackermann x∈y means bit x of y is one."""
    if n == 0:
        return True
    tag = n % 4
    a, b = unpair(n // 4)
    if tag == 1:
        return bool((valuation[b] >> valuation[a]) & 1)
    if tag == 3:
        return valuation[a] == valuation[b]
    if tag == 0:
        return not hf_satisfies(a, valuation, domain) or hf_satisfies(b, valuation, domain)
    for witness in domain:
        updated = dict(valuation)
        updated[a] = witness
        if not hf_satisfies(b, updated, domain):
            return False
    return True


def check_hf_corpus(codes: list[int]) -> dict:
    # V_3 consists of Ackermann codes 0,1,2,3. It is a finite diagnostic
    # structure, explicitly not a model of ZFC or the original source theory.
    domain = (0, 1, 2, 3)
    valuations = 0
    maximum_free_names = 0
    for n in codes:
        labels = sorted(free_names_code(n))
        maximum_free_names = max(maximum_free_names, len(labels))
        for values in itertools.product(domain, repeat=len(labels)):
            valuations += 1
            assert hf_satisfies(n, dict(zip(labels, values)), domain), (n, labels, values)
    return {"domain": "V_3, Ackermann codes [0,1,2,3]",
            "scope": "finite semantic regression, not a model of ZFC",
            "formula_codes_checked": len(codes), "valuations_checked": valuations,
            "maximum_free_names": maximum_free_names, "all_valid": True}


def run_evidence(limit: int, upstream: Path | None) -> dict:
    old = None
    if upstream:
        spec = importlib.util.spec_from_file_location("upstream_seed254", upstream)
        assert spec and spec.loader
        old = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(old)
    examples = {
        "irreflexivity_at_1": imp(mem(1, 1), 1),
        "membership_asymmetry": imp(mem(0, 1), imp(mem(1, 0), 1)),
        "three_cycle_exclusion": imp(mem(0, 1), imp(mem(1, 2), imp(mem(2, 0), 1))),
        "equality_membership_transport": imp(eq(0, 1), imp(mem(0, 2), mem(1, 2))),
        "false_membership": mem(0, 1),
        "universal_membership_transitivity": imp(mem(0, 1), imp(mem(1, 2), mem(0, 2))),
    }
    positive = {"irreflexivity_at_1", "membership_asymmetry", "three_cycle_exclusion", "equality_membership_transport"}
    for name, n in examples.items():
        assert encode(decode(n)) == n
        assert (formula(n) is not None) == (name in positive)
    assert formula(1) is None and stack(1) is None and stack(60) is None
    assert state([0, 0, 0, 0, 0, 0, 0, 0, 0]) is not None
    assert state([7, examples["membership_asymmetry"], 0, 3, 9, 0, 8, 10, 11]) is not None
    # Resource exhaustion must not be treated as an invalid formula.
    assert semantic_core(examples["membership_asymmetry"], max_names=1)["status"] == "unsupported"
    assert semantic_core(examples["membership_asymmetry"], max_edges=0)["status"] == "unsupported"
    # Explicit finite-set counterassignments, including aliased and distinct names.
    witness_checks = 0
    # Small query template suite, checked against an independent model enumeration.
    atoms = [mem(a, b) for a in range(2) for b in range(2)] + [eq(0, 1), 0]
    probes = sorted(set(atoms + [imp(a, b) for a in atoms for b in atoms]
                        + [examples["membership_asymmetry"], examples["equality_membership_transport"],
                           examples["universal_membership_transitivity"]]))
    for n in probes:
        labels = qf_names(decode(n))
        assert labels is not None
        assert (semantic_core(n)["status"] == "valid") == independent_finite_valid(n, max(1, len(labels)))
        result = semantic_core(n)
        if result["status"] == "acyclic_pattern_counterexample":
            assert not evaluate_hf_witness(n, result["hereditarily_finite_witness"])
            witness_checks += 1
    accepted = extra = old_count = stack_count = old_stack_count = extra_stacks = 0
    accepted_codes = []
    first_extra = []
    first_extra_stacks = []
    for n in range(limit):
        new = formula(n)
        previous = old.formula(n) if old else None
        new_stack = stack(n)
        previous_stack = old.stack(n) if old else None
        assert encode(decode(n)) == n
        accepted += new is not None
        if new is not None:
            accepted_codes.append(n)
        stack_count += new_stack is not None
        old_stack_count += previous_stack is not None
        old_count += previous is not None
        if previous is not None:
            assert new is not None
        if previous_stack is not None:
            assert new_stack is not None
        if new is not None and previous is None:
            extra += 1
            if len(first_extra) < 32:
                first_extra.append({"code": n, "formula": decode(n), "certificate": new})
        if new_stack is not None and previous_stack is None:
            extra_stacks += 1
            if len(first_extra_stacks) < 32:
                first_extra_stacks.append({"code": n, "head_codes": [item["code"] for item in new_stack]})
    return {
        "scope": "exact finite semantic certificates and ordinary ZFC soundness theorem; no binary reduction",
        "formula_census_limit": limit, "accepted_formula_codes": accepted,
        "accepted_stack_codes": stack_count, "upstream_pattern_acceptances": old_count if old else None,
        "upstream_stack_pattern_acceptances": old_stack_count if old else None,
        "additional_formula_codes": extra if old else None,
        "additional_stack_codes": extra_stacks if old else None,
        "first_additional_formula_codes": first_extra if old else [],
        "first_additional_stack_codes": first_extra_stacks if old else [],
        "independent_finite_model_probes": len(probes),
        "explicit_hf_counterassignments_checked_in_probe_suite": witness_checks,
        "resource_limits_return_unknown": True,
        "independent_hf_corpus": check_hf_corpus(accepted_codes + [examples[x] for x in sorted(positive)]),
        "examples": {name: {"code": n, "formula": decode(n), "accepted": formula(n) is not None,
                              "certificate": semantic_core(n)} for name, n in examples.items()},
        "falsity_and_buried_falsity_rejected": True,
    }


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--limit", type=int, default=65536)
    ap.add_argument("--upstream-seed", type=Path)
    ap.add_argument("--output", type=Path)
    args = ap.parse_args()
    if not __debug__:
        raise SystemExit("run with assertions enabled")
    result = run_evidence(args.limit, args.upstream_seed)
    payload = json.dumps(result, indent=2) + "\n"
    if args.output:
        args.output.write_text(payload)
    else:
        print(payload, end="")


if __name__ == "__main__":
    main()
