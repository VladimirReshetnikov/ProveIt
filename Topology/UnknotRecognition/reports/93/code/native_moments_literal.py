"""Small-input, edge-by-edge oracle independent of weighted orbit code."""

from collections import defaultdict


class ParityUnion:
    def __init__(self, n):
        self.parent = list(range(n))
        self.parity = [0] * n

    def find(self, x):
        path = []
        value, current = 0, x
        while self.parent[current] != current:
            path.append(current)
            value ^= self.parity[current]
            current = self.parent[current]
        suffix = value
        for point in path:
            edge = self.parity[point]
            self.parent[point], self.parity[point] = current, suffix
            suffix ^= edge
        return current, value

    def join(self, x, y, flip=0):
        a, left = self.find(x)
        b, right = self.find(y)
        if a == b:
            if left ^ right != flip:
                raise AssertionError('inconsistent literal vertex chart')
        else:
            self.parent[a] = b
            self.parity[a] = left ^ right ^ flip


def literal_gap_lengths(geometry, max_points=100000):
    """Expand free edges once and walk until the next marked occurrence.

    Loop edges retain both incidence flags, and aliases of a corner retain
    their independent fibre chart parity.  This routine does no moment sums.
    """
    n = geometry['corner_points']
    if n > max_points:
        raise ValueError('literal namespace cap exceeded')
    corners = ParityUnion(n)
    for link in geometry['gluings']:
        polygons = [geometry['polygons'][link[side]] for side in ('left', 'right')]
        for rank in range(link['rank_start'], link['rank_stop']):
            for endpoint in (0, 1):
                points = []
                for side, polygon in zip(('left', 'right'), polygons):
                    end = endpoint if side == 'left' else endpoint ^ int(link['ends_reverse'])
                    slot = (link[side + '_edge'] + end) % len(polygon['vertices'])
                    slope, offset = link[side + '_map']
                    points.append(polygon['corner_starts'][slot] + slope * rank + offset - polygon['start'])
                corners.join(*points, int(link['fibre_flip']))
    edges, incidence, tokens = [], defaultdict(list), {}
    for free in geometry['free_edges']:
        polygon = geometry['polygons'][free['polygon']]
        for rank in range(free['rank_start'], free['rank_stop']):
            points = [polygon['corner_starts'][(free['edge'] + end) % len(polygon['vertices'])] + rank - 1
                      for end in (0, 1)]
            port = None if free['original_boundary'] else free['port']
            index = len(edges)
            edges.append((points, port))
            for end in (0, 1):
                vertex, _ = corners.find(points[end])
                incidence[vertex].append((index, end))
                if port is not None:
                    tokens[2 * port + end] = (index, end)
    if any(len(flags) != 2 for flags in incidence.values()):
        raise AssertionError('literal boundary fails degree two')
    gaps = []
    for token, (initial_edge, initial_end) in sorted(tokens.items()):
        vertex, transport = corners.find(edges[initial_edge][0][initial_end])
        previous = (initial_edge, initial_end)
        length, visited = 0, set()
        while True:
            flag = next(flag for flag in incidence[vertex] if flag != previous)
            index, end = flag
            points, port = edges[index]
            if port is not None:
                target = 2 * port + end
                _, final_chart = corners.find(points[end])
                twist = bool(transport ^ final_chart)
                break
            if index in visited:
                raise AssertionError('active path failed to reach next port')
            visited.add(index)
            length += 1
            _, entry = corners.find(points[end])
            vertex, exit_chart = corners.find(points[1 - end])
            transport ^= entry ^ exit_chart
            previous = (index, 1 - end)
        if token < target:
            gaps.append(dict(id=len(gaps), ends=[token, target],
                             old_boundary_present=length > 0, fibre_flip=twist,
                             unmarked_edges=length))
    loops = sum(corners.find(points[0])[0] == corners.find(points[1])[0]
                for points, _ in edges)
    return dict(gaps=gaps, free_edge_count=len(edges), loop_edges=loops,
                positive_gaps=sum(gap['unmarked_edges'] > 0 for gap in gaps),
                point_gaps=sum(gap['unmarked_edges'] == 0 for gap in gaps))
