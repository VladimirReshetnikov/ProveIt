"""Fresh, standalone static finite-certificate audit, 2026-10-04.

No author code is imported or executed.  Original JSON and receipts are data.
No trajectory is evolved: periodic checks are simultaneous Boolean equations.
Completeness is derived from the 4-bit de Bruijn graph, using an undirected
spanning tree with mixed edge orientations, rather than a conservation-identity
implementation or the author's leading-/trailing-zero seed construction.

The accompanying AUDIT.md proves the graph criterion used below.
"""

from collections import Counter, deque
import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
INPUT = HERE.parent / "proof-packet" / "appendix"


def require(condition, explanation):
    if not condition:
        raise RuntimeError(explanation)


def digest(data):
    return hashlib.sha256(data).hexdigest()


def manifest():
    answer = []
    for path in sorted(INPUT.iterdir()):
        require(path.is_file(), "unexpected nonfile in frozen appendix")
        stat = path.stat()
        answer.append({
            "name": path.name,
            "size": stat.st_size,
            "mode": oct(stat.st_mode & 0o7777),
            "mtime_ns": stat.st_mtime_ns,
            "sha256": digest(path.read_bytes()),
        })
    return answer


before = manifest()
require(len(before) == 6, "appendix file inventory changed")

# Edge e has word abcde, tail abcd, head bcde, and input center c.
edges = tuple((e >> 1, e & 15, (e >> 2) & 1) for e in range(32))
adjacency = [[] for _ in range(16)]
for edge_id, (tail, head, center) in enumerate(edges):
    if tail != head:
        adjacency[tail].append((edge_id, head, 1))
        adjacency[head].append((edge_id, tail, -1))
for adjacent in adjacency:
    adjacent.sort()

# Breadth-first undirected tree.  Direction +1 follows the graph edge; -1
# traverses it backwards.  An edge label g=f-c determines the potential jump.
seen = {0}
queue = deque([0])
tree = []
while queue:
    parent = queue.popleft()
    for edge_id, child, direction in adjacency[parent]:
        if child not in seen:
            seen.add(child)
            queue.append(child)
            tree.append((parent, child, edge_id, direction))
require(seen == set(range(16)) and len(tree) == 15, "invalid spanning tree")
require(any(row[3] == -1 for row in tree), "tree is not mixed-orientation")

# For every possible 0/1 labeling on the 15 tree edges, compute the unique
# potential with p(0000)=0.  All 32 Boolean outputs are then forced by
# f(abcde)=c+p(bcde)-p(abcd).  Reject a labeling iff an output is not Boolean.
tables = set()
potential_by_table = {}
first_rejection_edge = Counter()
for mask in range(1 << 15):
    potential = [None] * 16
    potential[0] = 0
    for bit_number, (parent, child, edge_id, direction) in enumerate(tree):
        bit = (mask >> bit_number) & 1
        center = edges[edge_id][2]
        potential[child] = potential[parent] + direction * (bit - center)
    values = []
    for edge_id, (tail, head, center) in enumerate(edges):
        value = center + potential[head] - potential[tail]
        if value not in (0, 1):
            first_rejection_edge[edge_id] += 1
            break
        values.append(str(value))
    if len(values) == 32:
        table = "".join(values)
        require(table not in tables, "distinct tree assignments duplicate a table")
        tables.add(table)
        potential_by_table[table] = potential

require(len(tables) == 428, "independent graph enumeration does not give 428")
require(sum(first_rejection_edge.values()) + len(tables) == 32768,
        "enumeration accounting failed")

# Projection at offset j is the corresponding bit of the 5-bit word.
projections = {
    "".join(str((word >> (2 - offset)) & 1) for word in range(32)): offset
    for offset in range(-2, 3)
}
require(len(projections) == 5 and set(projections) <= tables,
        "the five coordinate projections are missing")

certificate = json.loads((INPUT / "radius2_certificate.json").read_text())
require(certificate["count"] == len(tables), "declared count mismatch")
require(len(certificate["certificates"]) == 423, "wrong certificate row count")
certified_tables = set()
witness_counts = Counter()
bit_equations = 0
certificate_period_by_table = {}
collision_rows = []


def word_bit(value, width, index):
    # The input integer uses ordinary most-significant-bit-first word order.
    return (value >> (width - 1 - (index % width))) & 1


def local_index(value, period, position):
    # This constructs only an address into a fixed local truth table.
    return sum(word_bit(value, period, position + offset) << (2 - offset)
               for offset in range(-2, 3))


for row in certificate["certificates"]:
    table = row["table"]
    require(isinstance(table, str) and len(table) == 32 and set(table) <= {"0", "1"},
            "malformed truth table")
    require(table in tables and table not in projections, "bad certified table")
    require(table not in certified_tables, "duplicate certificate table")
    period, a, b, image = (row[key] for key in ("period", "a", "b", "image"))
    require(all(type(value) is int for value in (period, a, b, image)),
            "certificate integers are not integers")
    require(period in (4, 5, 6), "unexpected collision period")
    require(0 <= a < (1 << period) and 0 <= b < (1 << period)
            and 0 <= image < (1 << period) and a != b, "invalid witness words")
    for position in range(period):
        left = int(table[local_index(a, period, position)])
        right = int(table[local_index(b, period, position)])
        claimed = word_bit(image, period, position)
        require(left == right == claimed, "false local collision equality")
        bit_equations += 2
    certified_tables.add(table)
    witness_counts[period] += 1
    certificate_period_by_table[table] = period
    collision_rows.append({"table": table, "period": period,
                           "a": a, "b": b, "image": image})

require(certified_tables.isdisjoint(projections), "projection certified as collision")
require(certified_tables | set(projections) == tables, "certificate does not cover tables")
require(witness_counts == Counter({4: 164, 5: 179, 6: 80}), "period counts differ")
require(certificate["collision_period_counts"] ==
        {str(key): witness_counts[key] for key in sorted(witness_counts)},
        "declared certificate period counts differ")

# Exhaust all simultaneous Boolean local equations at each period 1..6.
# A signature is a tuple of truth-table lookups for one fixed assignment;
# no signature is fed back as a later input, and no temporal loop exists.
minimal_period = {}
signature_assignment_count = 0
signature_lookup_count = 0
noninjective_counts_all_tables = {}
for period in range(1, 7):
    addresses = [tuple(local_index(word, period, i) for i in range(period))
                 for word in range(1 << period)]
    noninjective_count = 0
    for table in sorted(tables):
        signatures = [tuple(table[index] for index in row) for row in addresses]
        signature_assignment_count += len(signatures)
        signature_lookup_count += period * len(signatures)
        if len(set(signatures)) < len(signatures):
            noninjective_count += 1
            minimal_period.setdefault(table, period)
    noninjective_counts_all_tables[period] = noninjective_count
require(minimal_period == certificate_period_by_table,
        "a certificate's claimed first collision period is not minimal")
require(tables - set(minimal_period) == set(projections), "survivor mismatch")

survivors = certificate["survivors"]
require(len(survivors) == 5 and len({row["table"] for row in survivors}) == 5,
        "wrong survivor rows")
for row in survivors:
    table = row["table"]
    require(table in projections and row["shift"] == projections[table],
            "wrong projection coordinate")
    require(row["rule"] == sum(int(bit) << i for i, bit in enumerate(table)),
            "wrong rule integer convention")
require(certificate["tested_max_period"] == max(minimal_period.values()) == 6,
        "wrong maximum period")

receipt = json.loads((INPUT / "radius2-enumeration-receipt.json").read_text())
require(receipt == {key: value for key, value in certificate.items()
                    if key != "certificates"}, "enumeration receipt disagrees with data")
require((INPUT / "radius2-verification-receipt.txt").read_text().strip() ==
        "Independent reversed conservation identity: 428 tables; 423 explicit collisions checked; exactly five projections remain.",
        "unexpected verification receipt text")

canonical_tables = ("\n".join(sorted(tables)) + "\n").encode()
table_path = HERE / "independently-enumerated-tables.txt"
table_path.write_bytes(canonical_tables)
potential_path = HERE / "independent-graph-potentials.json"
potential_path.write_text(json.dumps(potential_by_table, indent=2, sort_keys=True) + "\n")
after = manifest()
require(before == after, "frozen appendix bytes, mode, size, or mtime changed")

report = {
    "status": "PASS",
    "method": "mixed-orientation de Bruijn spanning-tree coboundary enumeration",
    "graph_vertices": 16,
    "graph_edges": 32,
    "tree_edges": [
        {"parent": parent, "child": child, "edge_id": edge_id,
         "edge_word": format(edge_id, "05b"), "direction": direction}
        for parent, child, edge_id, direction in tree
    ],
    "tree_assignments_examined": 32768,
    "tree_assignments_rejected": sum(first_rejection_edge.values()),
    "first_rejection_edge_counts": dict(sorted(first_rejection_edge.items())),
    "distinct_conservative_tables": len(tables),
    "checked_certificate_rows": len(collision_rows),
    "checked_certificate_bit_equalities": bit_equations,
    "distinct_certified_nonprojections": len(certified_tables),
    "minimal_collision_period_counts": dict(sorted(witness_counts.items())),
    "noninjective_table_counts_at_each_period": noninjective_counts_all_tables,
    "exhaustive_signature_assignments": signature_assignment_count,
    "exhaustive_signature_table_lookups": signature_lookup_count,
    "remaining_projection_offsets": sorted(projections.values()),
    "remaining_projections": sorted(survivors, key=lambda row: row["shift"]),
    "original_receipts_consistent": True,
    "original_bytes_modes_mtimes_preserved": before == after,
    "original_manifest": before,
    "checker_sha256": digest(Path(__file__).read_bytes()),
    "canonical_table_set_sha256": digest(canonical_tables),
    "independent_graph_potentials_sha256": digest(potential_path.read_bytes()),
}
(HERE / "audit-result.json").write_text(json.dumps(report, indent=2) + "\n")
print(json.dumps(report, indent=2))
