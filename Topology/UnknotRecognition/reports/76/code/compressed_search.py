"""Exact all-context optimization of binary-compressed disk-patch grammars.

The solver returns abstract-disk results, never native unknot verdicts.
Source rules have uniform width; union branches must have the same span.
Repetition means independent choices in every occurrence, not one chosen
atom repeated W times. Costs may be signed because every language is finite.
"""
from __future__ import annotations
import argparse
from dataclasses import dataclass
import hashlib
import json
from pathlib import Path
from typing import Any, Iterable
from disk_algebra import Morphism, Partition, compose, feature, identity, disk_cap, validate_partition


class ResourceLimit(RuntimeError):
    """Inconclusive: a configured operation/allocation guard was reached."""


def source_digest(source: dict) -> str:
    return hashlib.sha256(json.dumps(source, sort_keys=True, separators=(",", ":")).encode()).hexdigest()


def integer(value: Any, name: str, *, minimum: int | None = None) -> int:
    if type(value) is int:
        ans = value
    elif isinstance(value, str) and value and value.lstrip("-").isdigit():
        ans = int(value)
    else:
        raise ValueError(f"{name} must be an integer or a decimal integer string")
    if minimum is not None and ans < minimum:
        raise ValueError(f"{name} must be at least {minimum}")
    return ans


@dataclass(frozen=True)
class Rule:
    kind: str
    args: tuple
    length: int


@dataclass(frozen=True)
class Program:
    width: int
    charges: int
    rules: tuple[Rule, ...]
    root: int


def compile_grammar(source: dict, *, max_rules: int | None = 100000,
                    max_exponent_bits: int | None = 16384) -> Program:
    """Validate a topologically ordered grammar and lower powers by squaring.

    This small compiler is shared with the checker and is an explicit trust
    boundary. Independent expanded-language audits exercise its semantics.
    """
    width = integer(source.get("width"), "width", minimum=1)
    charges = integer(source.get("charges", 1), "charges", minimum=1)
    if charges & (charges - 1):
        raise ValueError("charges must be a power of two (XOR group)")
    nodes = source.get("nodes")
    if not isinstance(nodes, list) or not nodes:
        raise ValueError("nodes must be a nonempty topologically ordered list")
    rules: list[Rule] = []
    lowered: list[int] = []
    ident: int | None = None

    def add(rule: Rule) -> int:
        if max_rules is not None and len(rules) >= max_rules:
            raise ResourceLimit("compiled rule budget exhausted")
        rules.append(rule)
        return len(rules) - 1

    def get_identity() -> int:
        nonlocal ident
        if ident is None:
            ident = add(Rule("identity", (), 0))
        return ident

    def previous(value: Any) -> int:
        i = integer(value, "child index", minimum=0)
        if i >= len(lowered):
            raise ValueError("children must refer to earlier source nodes")
        return lowered[i]

    for node in nodes:
        if not isinstance(node, dict):
            raise ValueError("each node must be an object")
        kind = node.get("kind")
        if kind == "identity":
            idx = get_identity()
        elif kind == "atoms":
            opts = node.get("options")
            if not isinstance(opts, list):
                raise ValueError("an atoms node needs an explicit options list")
            parsed = []
            for op in opts:
                if not isinstance(op, dict) or not isinstance(op.get("partition"), (list, tuple)):
                    raise ValueError("invalid atom record")
                p = tuple(op["partition"])
                Morphism(width, width, p)
                cost = integer(op.get("cost", 0), "atom cost")
                charge = integer(op.get("charge", 0), "atom charge", minimum=0)
                if charge >= charges:
                    raise ValueError("atom charge outside the supplied group")
                parsed.append((p, cost, charge))
            idx = add(Rule("atoms", tuple(parsed), 1))
        elif kind == "concat":
            a, b = previous(node.get("left")), previous(node.get("right"))
            idx = add(Rule("concat", (a, b), rules[a].length + rules[b].length))
        elif kind == "union":
            cs = node.get("children")
            if not isinstance(cs, list) or not cs:
                raise ValueError("a union needs at least one earlier child")
            children = tuple(previous(c) for c in cs)
            lengths = {rules[c].length for c in children}
            if len(lengths) != 1:
                raise ValueError("union branches must have the same physical span")
            idx = add(Rule("union", children, lengths.pop()))
        elif kind == "power":
            base = previous(node.get("base"))
            exponent = integer(node.get("exponent"), "exponent", minimum=0)
            if max_exponent_bits is not None and exponent.bit_length() > max_exponent_bits:
                raise ResourceLimit("exponent bit-length budget exhausted")
            if not exponent:
                idx = get_identity()
            else:
                acc: int | None = None
                power = base
                while exponent:
                    if exponent & 1:
                        acc = power if acc is None else add(Rule("concat", (acc, power),
                                                                        rules[acc].length + rules[power].length))
                    exponent >>= 1
                    if exponent:
                        power = add(Rule("concat", (power, power), 2 * rules[power].length))
                assert acc is not None
                idx = acc
        else:
            raise ValueError(f"unknown grammar node kind: {kind!r}")
        lowered.append(idx)
    root_source = integer(source.get("root", len(nodes) - 1), "root", minimum=0)
    if root_source >= len(nodes):
        raise ValueError("root is outside the source node list")
    return Program(width, charges, tuple(rules), lowered[root_source])


@dataclass(frozen=True)
class Candidate:
    partition: Partition
    cost: int
    charge: int
    origin: tuple[int, ...]


def reduce_family(candidates: list[Candidate], *, exact: bool = False) -> list[int]:
    """Return original indices, sorted by cost; exact keeps all distinct states."""
    order = sorted(range(len(candidates)), key=lambda i: (candidates[i].cost, i))
    kept = []
    if exact:
        seen = set()
        for i in order:
            key = candidates[i].partition, candidates[i].charge
            if key not in seen:
                kept.append(i)
                seen.add(key)
        return kept
    pivots: dict[tuple[int, int], int] = {}
    for i in order:
        item = candidates[i]
        row = feature(item.partition)
        while row:
            key = item.charge, row.bit_length() - 1
            if key in pivots:
                row ^= pivots[key]
            else:
                pivots[key] = row
                kept.append(i)
                break
    return kept


def generate(rule: Rule, tables: list[list[Candidate]], width: int) -> tuple[list[Candidate], int]:
    if rule.kind == "identity":
        return [Candidate(identity(width).partition, 0, 0, ())], 0
    if rule.kind == "atoms":
        return [Candidate(p, c, h, (i,)) for i, (p, c, h) in enumerate(rule.args)], 0
    if rule.kind == "union":
        return [Candidate(x.partition, x.cost, x.charge, (child, i))
                for child in rule.args for i, x in enumerate(tables[child])], 0
    a, b = rule.args
    answer = []
    for i, x in enumerate(tables[a]):
        first = Morphism(width, width, x.partition)
        for j, y in enumerate(tables[b]):
            out = compose(first, Morphism(width, width, y.partition))
            if out is not None:
                answer.append(Candidate(out.partition, x.cost + y.cost, x.charge ^ y.charge,
                                        (a, i, b, j)))
    return answer, len(tables[a]) * len(tables[b])


@dataclass
class Result:
    program: Program
    tables: list[list[Candidate]]
    selections: list[list[int]]
    digest: str
    metrics: dict[str, int]

    def query(self, cap: Partition, allowed_charges: Iterable[int] | None = None) -> dict:
        validate_partition(cap)
        if len(cap) != 2 * self.program.width:
            raise ValueError("cap has wrong width")
        allowed = None if allowed_charges is None else set(allowed_charges)
        if allowed is not None and any(type(x) is not int or x < 0 or x >= self.program.charges for x in allowed):
            raise ValueError("invalid allowed charge")
        feasible = [(x.cost, i) for i, x in enumerate(self.tables[self.program.root])
                    if (allowed is None or x.charge in allowed) and disk_cap(x.partition, cap)]
        if not feasible:
            return {"status": "NO_DISK_IN_GRAMMAR", "cost": None, "witness": None}
        cost, i = min(feasible)
        return {"status": "FOUND_ABSTRACT_DISK", "cost": cost,
                "witness": [self.program.root, i]}

    def certificate(self) -> dict:
        return {"format": "binary-patch-run-v1", "source_digest": self.digest,
                "selections": self.selections, "root": self.program.root}

    def witness_statistics(self, witness: list[int]) -> dict:
        """Replay additive atom counts on the SLP, never expand the word."""
        root, item = witness
        if root != self.program.root or not 0 <= item < len(self.tables[root]):
            raise ValueError("witness must belong to the output table")
        reachable = set()
        stack = [(root, item)]
        while stack:
            key = stack.pop()
            if key in reachable:
                continue
            reachable.add(key)
            n, j = key
            rule, cand = self.program.rules[n], self.tables[n][j]
            if rule.kind == "concat":
                a, i, b, k = cand.origin
                stack.extend(((a, i), (b, k)))
            elif rule.kind == "union":
                stack.append(tuple(cand.origin))
        counts: dict[tuple[int, int], dict[tuple[int, int], int]] = {}
        for key in sorted(reachable):
            n, j = key
            rule, cand = self.program.rules[n], self.tables[n][j]
            if rule.kind == "identity":
                out = {}
            elif rule.kind == "atoms":
                out = {(n, cand.origin[0]): 1}
            elif rule.kind == "union":
                out = counts[tuple(cand.origin)].copy()
            else:
                a, i, b, k = cand.origin
                out = counts[(a, i)].copy()
                for atom, num in counts[(b, k)].items():
                    out[atom] = out.get(atom, 0) + num
            counts[key] = out
        histogram = counts[(root, item)]
        length = sum(histogram.values())
        cost = sum(num * self.program.rules[n].args[i][1] for (n, i), num in histogram.items())
        charge = 0
        for (n, i), num in histogram.items():
            if num & 1:
                charge ^= self.program.rules[n].args[i][2]
        cand = self.tables[root][item]
        assert (length, cost, charge) == (self.program.rules[root].length, cand.cost, cand.charge)
        return {"reachable_dag_nodes": len(reachable), "expanded_length": length,
                "cost": cost, "charge": charge,
                "atom_counts": [{"rule": n, "option": i, "count": num}
                                for (n, i), num in sorted(histogram.items())]}

    def expand_witness(self, witness: list[int], max_atoms: int = 10000) -> list[tuple[int, int]]:
        n, j = witness
        if self.program.rules[n].length > max_atoms:
            raise ResourceLimit("expanded witness exceeds explicit output budget")
        out = []
        stack = [(n, j)]
        while stack:
            n, j = stack.pop()
            rule, cand = self.program.rules[n], self.tables[n][j]
            if rule.kind == "atoms":
                out.append((n, cand.origin[0]))
            elif rule.kind == "union":
                stack.append(tuple(cand.origin))
            elif rule.kind == "concat":
                a, i, b, k = cand.origin
                stack.extend(((b, k), (a, i)))
        return out


def solve(source: dict, *, exact: bool = False, max_feature_dimension: int | None = 65536,
          max_pairs: int | None = 10000000, max_rules: int | None = 100000) -> Result:
    program = compile_grammar(source, max_rules=max_rules)
    exponent = 2 * program.width - 1
    if max_feature_dimension is not None and (max_feature_dimension < 1 or exponent >= max_feature_dimension.bit_length()):
        raise ResourceLimit("feature dimension exceeds allocation budget")
    dimension = 1 << exponent
    tables: list[list[Candidate]] = []
    selections = []
    metrics = {"compiled_rules": len(program.rules), "composition_pairs": 0,
               "generated_survivors": 0, "retained_total": 0, "peak_table": 0,
               "feature_dimension": dimension, "expanded_length": program.rules[program.root].length}
    for rule in program.rules:
        if rule.kind == "concat":
            a, b = rule.args
            projected = metrics["composition_pairs"] + len(tables[a]) * len(tables[b])
            if max_pairs is not None and projected > max_pairs:
                raise ResourceLimit("composition budget exhausted; no negative conclusion")
        generated, pairs = generate(rule, tables, program.width)
        selection = reduce_family(generated, exact=exact)
        table = [generated[i] for i in selection]
        tables.append(table)
        selections.append(selection)
        metrics["composition_pairs"] += pairs
        metrics["generated_survivors"] += len(generated)
        metrics["retained_total"] += len(table)
        metrics["peak_table"] = max(metrics["peak_table"], len(table))
    return Result(program, tables, selections, source_digest(source), metrics)


def repeated_source(width: int, options: list[dict], repetitions: int, charges: int = 1) -> dict:
    return {"width": width, "charges": charges,
            "nodes": [{"kind": "atoms", "options": options},
                      {"kind": "power", "base": 0, "exponent": str(repetitions)}]}


def sequential(source: dict, repetitions: int, *, exact: bool = False) -> list[Candidate]:
    """Explicit two-sided sequential comparator for a single atom library."""
    prog = compile_grammar(source)
    atom = next(r for r in prog.rules if r.kind == "atoms")
    library, _ = generate(atom, [], prog.width)
    table = [Candidate(identity(prog.width).partition, 0, 0, ())]
    for _ in range(repetitions):
        candidates, _ = generate(Rule("concat", (0, 1), 0), [table, library], prog.width)
        table = [candidates[i] for i in reduce_family(candidates, exact=exact)]
    return table


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("grammar", type=Path)
    parser.add_argument("--certificate", type=Path)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    try:
        source = json.loads(args.grammar.read_text())
        result = solve(source)
        output = {"status": "COMPLETE_ABSTRACT_SUMMARY", "metrics": result.metrics}
        if "query" in source:
            query = source["query"]
            output["query"] = result.query(tuple(query["cap"]), query.get("allowed_charges"))
            if output["query"]["witness"] is not None:
                output["witness_statistics"] = result.witness_statistics(output["query"]["witness"])
        if args.certificate:
            args.certificate.write_text(json.dumps(result.certificate(), indent=2) + "\n")
    except ResourceLimit as exc:
        output = {"status": "UNKNOWN_RESOURCE_LIMIT", "reason": str(exc)}
    text = json.dumps(output, indent=2) + "\n"
    if args.output:
        args.output.write_text(text)
    else:
        print(text, end="")


if __name__ == "__main__":
    main()
