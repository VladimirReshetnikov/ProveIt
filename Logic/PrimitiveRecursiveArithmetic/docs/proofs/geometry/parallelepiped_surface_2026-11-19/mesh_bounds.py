#!/usr/bin/env python3
"""Certified extrema of the surface metric of a rational-Gram parallelepiped.

Examples:
  python mesh_bounds.py --mode both --gram 4 3 2 1 0 1 --m 8 --n 4 --scale 65536
  python mesh_bounds.py --mode fixed --vertex 101 --gram 1 1 1 0 0 0

All calculations that affect the bounds are exact integer/rational arithmetic.
Coordinates in the JSON are affine cube coordinates, written as fractions.
The antipodal mode uses the antipodal diameter theorem proved in the report.
"""

import argparse
from fractions import Fraction
from functools import lru_cache
import heapq
import json
from math import isqrt, lcm


def square_root_units(numerator, denominator):
    """Return floor and ceiling of sqrt(numerator/denominator)."""
    lower = isqrt(numerator // denominator)
    return lower, lower + int(lower * lower * denominator != numerator)


def grid_surface(divisions, unit):
    """Yield each boundary point of the specified mesh exactly once."""
    step = unit // divisions
    for i in range(divisions + 1):
        for j in range(divisions + 1):
            zs = range(divisions + 1) if i in (0, divisions) or j in (0, divisions) else (0, divisions)
            for k in zs:
                yield (step * i, step * j, step * k)


def chart_ids(point, unit):
    """Face 2*i+b is the boundary chart u_i=b."""
    return tuple(2 * i + int(v == unit) for i, v in enumerate(point) if v in (0, unit))


class Mesh:
    def __init__(self, gram, m, n, scale):
        a, b, c, d, e, f = gram
        det2 = a * b - d * d
        det3 = c * det2 + 2 * d * e * f - a * f * f - b * e * e
        if a <= 0 or det2 <= 0 or det3 <= 0:
            raise ValueError("the Gram matrix must be positive definite")
        self.m, self.n, self.scale = m, n, scale
        self.unit = lcm(m, n)
        gram_den = lcm(*(x.denominator for x in gram))
        self.coefficients = tuple(int(x * gram_den) for x in gram)
        self.chord_den = gram_den * self.unit ** 2
        longest_squared = max(a, b, c)
        _, ceil_edge = square_root_units(scale ** 2 * longest_squared.numerator, longest_squared.denominator)
        self.edge_bound = Fraction(ceil_edge, scale)
        self.edge_nodes = []
        for point in grid_surface(m, self.unit):
            if len(chart_ids(point, self.unit)) >= 2:
                self.edge_nodes.append(point)
        self.node_index = {p: i for i, p in enumerate(self.edge_nodes)}
        self.face_nodes = [[] for _ in range(6)]
        for i, p in enumerate(self.edge_nodes):
            for face in chart_ids(p, self.unit):
                self.face_nodes[face].append(i)
        adjacency = [dict() for _ in self.edge_nodes]
        for indices in self.face_nodes:
            for pos, i in enumerate(indices):
                for j in indices[:pos]:
                    if j not in adjacency[i]:
                        cost = self.chord(self.edge_nodes[i], self.edge_nodes[j])[1]
                        adjacency[i][j] = adjacency[j][i] = cost
        self.adjacency = [tuple(row.items()) for row in adjacency]

    @lru_cache(maxsize=16384)
    def delta_chord(self, x, y, z):
        a, b, c, d, e, f = self.coefficients
        square = a*x*x + b*y*y + c*z*z + 2*(d*x*y + e*x*z + f*y*z)
        return square_root_units(square * self.scale ** 2, self.chord_den)

    def chord(self, p, q):
        return self.delta_chord(p[0]-q[0], p[1]-q[1], p[2]-q[2])

    def neighbors_of(self, p):
        indices = set()
        for face in chart_ids(p, self.unit):
            indices.update(self.face_nodes[face])
        return sorted(indices)

    def from_source(self, source):
        """Dijkstra from a surface point, with each arc rounded upwards."""
        size = len(self.edge_nodes)
        distances = [None] * size
        parents = [None] * size
        if source in self.node_index:
            i = self.node_index[source]
            distances[i] = 0
            queue = [(0, i)]
        else:
            queue = []
            for i in self.neighbors_of(source):
                cost = self.chord(source, self.edge_nodes[i])[1]
                distances[i] = cost
                queue.append((cost, i))
            heapq.heapify(queue)
        while queue:
            cost, i = heapq.heappop(queue)
            if cost != distances[i]:
                continue
            for j, step in self.adjacency[i]:
                candidate = cost + step
                if distances[j] is None or candidate < distances[j]:
                    distances[j] = candidate
                    parents[j] = i
                    heapq.heappush(queue, (candidate, j))
        return distances, parents

    def finish(self, source, target, distances):
        if target in self.node_index:
            i = self.node_index[target]
            return distances[i], i
        cost, anchor = min((distances[i] + self.chord(self.edge_nodes[i], target)[1], i)
                           for i in self.neighbors_of(target))
        if set(chart_ids(source, self.unit)).intersection(chart_ids(target, self.unit)):
            direct = self.chord(source, target)[1]
            if direct <= cost:
                return direct, None
        return cost, anchor

    def route(self, source, target, anchor, parents):
        nodes = []
        while anchor is not None:
            nodes.append(self.edge_nodes[anchor])
            anchor = parents[anchor]
        path = []
        for p in [source, *reversed(nodes), target]:
            if not path or path[-1] != p:
                path.append(p)
        return path

    def coordinates(self, point):
        return [str(Fraction(v, self.unit)) for v in point]

    def extrema(self, mode, vertex):
        free = mode == "antipodal"
        fixed = tuple(b * self.unit for b in vertex)
        fixed_search = None if free else self.from_source(fixed)
        net_error = self.edge_bound * (2 if free else 1) / self.n
        dist_error = 5 * self.edge_bound / self.m + Fraction(6, self.scale)
        best_low = None
        max_up = Fraction(0)
        count = 0
        for p in grid_surface(self.n, self.unit):
            if free:
                source, target = p, tuple(self.unit - z for z in p)
                if source > target:
                    continue
                distances, parents = self.from_source(source)
            else:
                source, target = fixed, p
                distances, parents = fixed_search
            units, anchor = self.finish(source, target, distances)
            upper = Fraction(units, self.scale)
            ambient_lower = Fraction(self.chord(source, target)[0], self.scale)
            lower = max(ambient_lower, upper - dist_error)
            max_up = max(max_up, upper)
            if best_low is None or (lower, upper) > (best_low, best_witness_up):
                best_low, best_witness_up = lower, upper
                best_path = self.route(source, target, anchor, parents)
            count += 1
        steps = []
        for p, q in zip(best_path, best_path[1:]):
            common = sorted(set(chart_ids(p, self.unit)).intersection(chart_ids(q, self.unit)))
            assert common
            steps.append({"face_axis": common[0] // 2 + 1, "face_bit": common[0] % 2,
                          "upper_cost_units": self.chord(p, q)[1]})
        assert sum(s["upper_cost_units"] for s in steps) == best_witness_up * self.scale
        return {
            "mode": mode, "endpoint_pairs_evaluated": count,
            "extremum_interval": [str(best_low), str(max_up + net_error)],
            "endpoint_net_allowance": str(net_error), "metric_mesh_allowance": str(dist_error),
            "witness_x": self.coordinates(best_path[0]), "witness_y": self.coordinates(best_path[-1]),
            "witness_distance_interval": [str(best_low), str(best_witness_up)],
            "witness_surface_route": [self.coordinates(p) for p in best_path],
            "witness_route_steps": steps,
        }


def positive_int(value):
    number = int(value)
    if number < 1:
        raise argparse.ArgumentTypeError("expected a positive integer")
    return number


def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--gram", nargs=6, type=Fraction, required=True,
                        metavar=("G11", "G22", "G33", "G12", "G13", "G23"),
                        help="Gram entries as fractions, integers or finite decimals")
    parser.add_argument("--m", type=positive_int, default=8, help="subintervals per edge for surface routes")
    parser.add_argument("--n", type=positive_int, default=4, help="subintervals per face direction for endpoints")
    parser.add_argument("--scale", type=positive_int, default=65536, help="upward costs in multiples of 1/scale")
    parser.add_argument("--mode", choices=("fixed", "antipodal", "both"), default="both")
    parser.add_argument("--vertex", choices=[format(i, "03b") for i in range(8)], default="000",
                        help="three affine coordinate bits for the fixed source")
    args = parser.parse_args()
    try:
        mesh = Mesh(args.gram, args.m, args.n, args.scale)
    except ValueError as error:
        parser.error(str(error))
    modes = ("fixed", "antipodal") if args.mode == "both" else (args.mode,)
    report = {"gram_order": ["g11", "g22", "g33", "g12", "g13", "g23"],
              "gram": list(map(str, args.gram)), "m": args.m, "n": args.n, "scale": args.scale,
              "longest_edge_upper_bound": str(mesh.edge_bound), "edge_node_count": len(mesh.edge_nodes),
              "results": [mesh.extrema(mode, tuple(map(int, args.vertex))) for mode in modes]}
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
