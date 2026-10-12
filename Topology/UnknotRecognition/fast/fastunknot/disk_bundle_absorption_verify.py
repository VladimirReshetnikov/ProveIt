"""Independent reconstruction of disk-bundle 2-handles from authenticated sources.

Returns reconstructed charts only after comparing every absorption record.
The enclosing verifier must first authenticate the geometry, profiles and
ordered interface. This module imports no absorption or cancellation producer.
"""

from .integer_codec import certificate_equal


def replay_disk_bundle_absorption(g, summary, skeleton, certificate, *, primitive_bases=frozenset(), check=lambda: None):
    # The enclosing checker must independently certify primitive_bases first.
    check()
    profiles = summary['base_profiles']
    owners = {port: i for i, p in enumerate(profiles) for port in p['core_ports']}
    taken, records, extra = set(), [], []
    for a, attachment in enumerate(skeleton['attachment_components']):
        check()
        if attachment['kind'] == 'interval':
            continue
        if attachment['kind'] != 'circle' or not attachment['word']:
            return None
        ports = [abs(x) - 1 for x in attachment['word']]
        base = owners[ports[0]]
        if base in primitive_bases:
            continue
        p = profiles[base]
        if (base in taken or any(owners[i] != base for i in ports) or
                sorted(ports) != sorted(p['core_ports']) or
                (p['euler_characteristic'], p['boundary_components'], p['multiplicity']) != (1, 1, 1) or
                p['orientable'] is not True or p['product'] is not True):
            return None
        taken.add(base)
        vertices, edges, records_here = [], [], []
        for letter, port_id in zip(attachment['word'], ports):
            check()
            port = g['ports'][port_id]
            number = port['core_handle']
            if port['core_dimension'] == 0:
                start = stop = number
            elif port['core_dimension'] == 1:
                poly = g['polygons'][port['polygon']]
                slot = port['edge']
                if poly['kind'] != 'edge_cap' or poly['edges'][slot]['kind'] != 'face_sector':
                    return None
                h = g['core']['handles1'][number]
                lookup = {(h['tetrahedron'], h['face']): 0,
                          (h['target_tetrahedron'], h['target_face']): 1}
                if len(lookup) != 2:
                    return None
                flags = [poly['vertices'][(slot + j) % len(poly['vertices'])] for j in (0, 1)]
                directions = [lookup.get((v['tetrahedron'], v['face'])) for v in flags]
                if sorted(d for d in directions if d is not None) != [0, 1]:
                    return None
                if letter < 0:
                    directions.reverse()
                start, stop = [h['ends'][d] for d in directions]
                sign = 1 if directions[0] == 0 else -1
                edges.append((start, number))
                records_here.append(dict(port=port_id, handle=number, sign=sign,
                                         start=start, stop=stop))
            else:
                return None
            vertices.append((start, stop))
        for j, (_, stop) in enumerate(vertices):
            if stop != vertices[(j + 1) % len(vertices)][0]:
                return None
        cycle = [flag for v, e in edges for flag in
                 (dict(dimension=0, handle=v), dict(dimension=1, handle=e))]
        number = len(g['core']['handles2']) + len(extra)
        extra.append(dict(id=number, cycle=cycle))
        records.append(dict(attachment=a, base_profile=base, two_handle=number,
                            crossings=records_here))
    expected = dict(schema='disk-bundle-absorption-v1', components=records)
    if not certificate_equal(certificate, expected):
        return None
    check()
    return dict(g['core'], handles2=g['core']['handles2'] + extra), taken
