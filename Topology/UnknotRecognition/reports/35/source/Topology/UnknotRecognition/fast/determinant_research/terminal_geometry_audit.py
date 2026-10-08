"""Test a checkable common-Tait-graph producer on actual scanning matchings.

This research prototype uses report 26's independently verified terminal kernel.
For a fixed suffix, retain the original black regions incident to a remaining
crossing and the signed edges of those crossings. Black regions touching a
frontier edge are terminals. A query is accepted only if completed faces keep
the original colors, each retained original region maps to one completed face,
and every nontrivial fiber consists entirely of terminals. These checks imply
an exact graph quotient by matching edge endpoints, without dense matrix
comparison. The raw phase uses the actual quotient vertex count.

Disconnected completions have zero determinant specialization. Other failed
geometry checks are inconclusive, never a knot verdict. Success on this finite
sample is not a proof of acceptance for every realizable frontier. Production
currently computes each completed determinant directly; reuse is future work.
"""
import sys, random, json, hashlib, argparse
from pathlib import Path
ROOT = Path(__file__).resolve().parents[2]
sys.path[:0] = [str(ROOT / 'fast'), str(ROOT / 'reports/26')]
from fastunknot import Diagram
from fastunknot.scan_fast import FastScan
from detshadow.diagram import Diagram as Ref, complete_matching
from detshadow.linalg import TerminalKernel, signed_laplacian, verify_kernel

def palette(d):
    alpha = d.edge_involution()
    face, cycles = d.faces(alpha)
    color = [None] * len(cycles)
    color[0] = 0
    todo = [0]
    adj = [set() for _ in cycles]
    for dart, a in enumerate(alpha):
        adj[face[dart]].add(face[a])
    for f in todo:
        for g in adj[f]:
            if color[g] is None:
                color[g] = 1 - color[f]
                todo.append(g)
    return (face, color)
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--output', type=Path, required=True)
args = parser.parse_args()
inputs = []
rng = random.Random(2606)
total = split = badcolor = badinterior = accepted = disconnected = 0
maxterm = 0
examples = []
for attempt in range(300):
    strands = rng.randrange(2, 6)
    word = [rng.choice((-1, 1)) * rng.randrange(1, strands) for _ in range(rng.randrange(1, 15))]
    try:
        d = Diagram.from_braid(strands, word)
    except ValueError:
        continue
    orig = Ref(d.pd)
    oldface, color = palette(orig)
    order = list(range(d.crossings))
    rng.shuffle(order)
    scan = FastScan(shape_cache=False)
    inputs.append(dict(strands=strands, word=word, order=order))
    for stage, index in enumerate(order):
        suffix = [d.pd[i] for i in order[stage:]]
        counts = {}
        for row in suffix:
            for a in row:
                counts[a] = counts.get(a, 0) + 1
        edges = []
        active = set()
        term = set()
        B = 0
        for i in order[stage:]:
            ports = [j for j in range(4) if color[oldface[4 * i + j]]]
            u, v = [oldface[4 * i + j] for j in ports]
            active.update((u, v))
            b = int(ports == [0, 2])
            B += b
            edges.append((u, v, -1 if b else 1))
            for j, label in enumerate(d.pd[i]):
                if counts[label] == 1:
                    f = oldface[4 * i + j]
                    g = oldface[4 * i + (j + 1) % 4]
                    term.add(f if color[f] else g)
        ids = {f: i for i, f in enumerate(sorted(active))}
        if not term:
            term = {min(active)}
        assert term <= active, (term, active)
        terminals = [ids[f] for f in sorted(term)]
        lap = signed_laplacian(len(ids), [(ids[u], ids[v], w) for u, v, w in edges])
        kernel = TerminalKernel.build(lap, terminals)
        assert verify_kernel(lap, kernel)
        maxterm = max(maxterm, len(term))
        for m in set(scan.mid) - {None}:
            c = complete_matching(suffix, scan.algebra.pairs[m])
            total += 1
            if c.shadow_components() != 1:
                disconnected += 1
                continue
            newface, _ = c.faces(c.edge_involution())
            mapping = {}
            newcolors = {}
            ok = True
            for k, i in enumerate(order[stage:]):
                for j in range(4):
                    old = oldface[4 * i + j]
                    new = newface[4 * k + j]
                    if new in newcolors and newcolors[new] != color[old]:
                        badcolor += 1
                        ok = False
                        break
                    newcolors[new] = color[old]
                    if color[old]:
                        if old in mapping and mapping[old] != new:
                            split += 1
                            ok = False
                            break
                        mapping[old] = new
                if not ok:
                    break
            if not ok:
                continue
            inv = {}
            for f, g in mapping.items():
                inv.setdefault(g, []).append(f)
            if any((len(fs) > 1 and any((f not in term for f in fs)) for fs in inv.values())):
                badinterior += 1
                continue
            labels = [mapping[f] for f in sorted(term)]
            value = kernel.query(labels)
            phase = (B + len(inv) - 1) % 4
            unit = ((1, 0), (0, -1), (-1, 0), (0, 1))[phase]
            z = (unit[0] * value, unit[1] * value)
            assert z == c.euler_i(), (d.pd, stage, labels, z, c.euler_i())
            accepted += 1
        scan.add_crossing(d.pd[index])
result = dict(seed=2606, attempts=300, validated=len(inputs), total=total, accepted=accepted, disconnected=disconnected, badcolor=badcolor, split=split, badinterior=badinterior, maxterm=maxterm, scope='Research quotient producer with checked geometry; no production dispatch or universal realization claim', inputs=inputs, sources={str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for p in (Path(__file__), ROOT / 'reports/26/detshadow/diagram.py', ROOT / 'reports/26/detshadow/linalg.py', ROOT / 'fast/fastunknot/scan_fast.py', ROOT / 'fast/fastunknot/planar.py')})
args.output.parent.mkdir(parents=True, exist_ok=True)
args.output.write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps({k: v for k, v in result.items() if k not in ('inputs', 'sources')}))
