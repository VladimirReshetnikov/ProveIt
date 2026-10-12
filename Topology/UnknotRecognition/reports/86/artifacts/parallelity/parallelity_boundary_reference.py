"""Finite geometric oracle: explicitly walk the actual boundary cellulation."""

from collections import defaultdict


class ParityUnion:
    def __init__(self, size):
        self.parent = list(range(size))
        self.parity = [0]*size

    def root(self, point):
        current, parity = point, 0
        while self.parent[current] != current:
            parity ^= self.parity[current]
            current = self.parent[current]
        return current, parity

    def join(self, first, last, flip):
        a, x = self.root(first)
        b, y = self.root(last)
        if a == b:
            if x ^ y != flip:
                raise ValueError('fibre charts disagree around a quotient vertex')
        else:
            self.parent[a] = b
            self.parity[a] = x ^ y ^ flip


def literal_boundary_interface(geometry, *, max_corners=100000):
    """Expand corners and boundary sides, then walk every marked boundary circle.

    This deliberately does not construct or query interval-orbit systems.
    The cap is essential: this finite oracle must never expand a large packet.
    """
    size = geometry['corner_points']
    if size > max_corners:
        raise ValueError('literal boundary expansion exceeds its cap')
    vertices = ParityUnion(size)
    polygons = geometry['polygons']
    for link in geometry['gluings']:
        p, q = polygons[link['left']], polygons[link['right']]
        for rank in range(link['rank_start'], link['rank_stop']):
            left_point = link['left_map'][0]*rank+link['left_map'][1]-p['start']
            right_point = link['right_map'][0]*rank+link['right_map'][1]-q['start']
            for end in (0, 1):
                a = p['corner_starts'][(link['left_edge']+end) % len(p['vertices'])]
                target_end = (1-end) if link['ends_reverse'] else end
                b = q['corner_starts'][(link['right_edge']+target_end)
                                       % len(q['vertices'])]
                vertices.join(a+left_point, b+right_point, int(link['fibre_flip']))
    adjacency = defaultdict(list)
    edges, port_edge, endpoint_point = [], {}, {}
    for free in geometry['free_edges']:
        p = polygons[free['polygon']]
        a = p['corner_starts'][free['edge']]
        b = p['corner_starts'][(free['edge']+1) % len(p['vertices'])]
        for rank in range(free['rank_start'], free['rank_stop']):
            points = [a+rank-1, b+rank-1]
            index = len(edges)
            port = None if free['original_boundary'] else free['port']
            edges.append(dict(points=points, port=port))
            for end, point in enumerate(points):
                adjacency[vertices.root(point)[0]].append((index, end))
                if port is not None:
                    endpoint_point[2*port+end] = point
            if port is not None:
                if port in port_edge:
                    raise ValueError('port occurs several times')
                port_edge[port] = index
    if any(len(incidences) != 2 for incidences in adjacency.values()):
        raise ValueError('boundary vertex does not have degree two')
    vertex_groups = defaultdict(list)
    for endpoint, point in endpoint_point.items():
        vertex_groups[vertices.root(point)[0]].append(endpoint)
    grouped_vertices = sorted(sorted(group) for group in vertex_groups.values())
    count = len(geometry['ports'])
    used, gaps, circles = set(), {}, []
    for start_port in range(count):
        if start_port in used:
            continue
        start = current = (start_port, 0)
        word, gap_count, holonomy = [], 0, False
        while True:
            port, entry = current
            if port in used:
                raise ValueError('literal boundary revisits a port')
            used.add(port)
            current_edge, outgoing = port_edge[port], 1-entry
            previous_point = edges[current_edge]['points'][outgoing]
            flip, old_sides = 0, 0
            for _ in range(2*len(edges)+1):
                vertex, first_parity = vertices.root(previous_point)
                incidence = (current_edge, outgoing)
                alternatives = [flag for flag in adjacency[vertex] if flag != incidence]
                if len(alternatives) != 1:
                    raise ValueError('boundary continuation is ambiguous')
                following_edge, incoming = alternatives[0]
                point = edges[following_edge]['points'][incoming]
                target_vertex, last_parity = vertices.root(point)
                if target_vertex != vertex:
                    raise ValueError('boundary incidence changes vertex')
                flip ^= first_parity ^ last_parity
                following_port = edges[following_edge]['port']
                if following_port is not None:
                    following = (following_port, incoming)
                    break
                old_sides += 1
                current_edge, outgoing = following_edge, 1-incoming
                previous_point = edges[current_edge]['points'][outgoing]
            else:
                raise ValueError('marked boundary walk failed to terminate')
            a, b = sorted((2*port+1-entry, 2*following[0]+following[1]))
            gap = dict(ends=[a, b], zero_length=old_sides == 0, fibre_flip=bool(flip))
            if (a, b) in gaps and gaps[a, b] != gap:
                raise ValueError('opposite gap traversals disagree')
            gaps[a, b] = gap
            gap_count += old_sides != 0
            holonomy ^= bool(flip)
            word.append(dict(port=port, entry_end=entry,
                             next_port=following[0], next_entry_end=following[1],
                             gap_zero_length=old_sides == 0, gap_fibre_flip=bool(flip)))
            current = following
            if current == start:
                break
        if holonomy:
            raise ValueError('source total interval bundle is not orientable')
        circles.append(dict(ports=word, full_core_circle=gap_count == 0,
                            core_interval_components=gap_count, fibre_holonomy=False))
    if len(gaps) != count:
        raise ValueError('boundary gap matching is incomplete')
    return dict(port_count=count, endpoint_vertices=grouped_vertices,
                gaps=[gaps[key] for key in sorted(gaps)], boundary_cycles=circles,
                marked_boundary_components=len(circles),
                core_attachment_vertices=len(grouped_vertices),
                attachment_euler_characteristic=len(grouped_vertices)-count,
                fibre_transport_checked=True)
