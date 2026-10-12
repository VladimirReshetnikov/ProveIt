"""Absorb source disk bundles along their entire vertical boundary as 2-handles.

Inputs must already be authenticated by the source-parallelity and marked
boundary checkers. No group-word reduction or homological test is used.
"""


def absorb_disk_bundles(geometry, summary, skeleton, *, primitive_bases=frozenset(), check=lambda: None):
    """Absorb disks; primitive_bases must be separately source-certified."""
    check()
    profiles = summary['base_profiles']
    by_port = {port: i for i, p in enumerate(profiles) for port in p['core_ports']}
    core = geometry['core']
    added, records, absorbed = [], [], set()
    for index, attachment in enumerate(skeleton['attachment_components']):
        check()
        if attachment['kind'] != 'circle':
            continue
        word = attachment['word']
        bases = {by_port[abs(letter) - 1] for letter in word}
        if len(bases) != 1:
            raise ArithmeticError('circle crosses base components')
        base = bases.pop()
        if base in primitive_bases:
            continue
        p = profiles[base]
        if (p['euler_characteristic'] != 1 or p['boundary_components'] != 1 or
                not p['orientable'] or not p['product'] or p['multiplicity'] != 1):
            return None
        if base in absorbed or set(p['core_ports']) != {abs(x) - 1 for x in word}:
            raise ArithmeticError('disk circle does not exhaust its component')
        absorbed.add(base)
        paths, crossings = [], []
        for letter in word:
            check()
            port = geometry['ports'][abs(letter) - 1]
            h = port['core_handle']
            if port['core_dimension'] == 0:
                paths.append((h, h))
                continue
            polygon = geometry['polygons'][port['polygon']]
            edge = port['edge']
            if (port['core_dimension'] != 1 or polygon['kind'] != 'edge_cap' or
                    polygon['edges'][edge]['kind'] != 'face_sector'):
                raise ArithmeticError('non-face-sector one-handle port')
            handle = core['handles1'][h]
            ends = [(handle['tetrahedron'], handle['face']),
                    (handle['target_tetrahedron'], handle['target_face'])]
            flags = [(polygon['vertices'][(edge + j) % len(polygon['vertices'])]['tetrahedron'],
                      polygon['vertices'][(edge + j) % len(polygon['vertices'])]['face'])
                     for j in (0, 1)]
            if flags == ends:
                sign = 1
            elif flags == ends[::-1]:
                sign = -1
            else:
                raise ArithmeticError('face-sector endpoint flags do not match')
            sign *= 1 if letter > 0 else -1
            start, stop = handle['ends'][::sign]
            paths.append((start, stop))
            crossings.append(dict(port=abs(letter) - 1, handle=h, sign=sign,
                                  start=start, stop=stop))
        if any(paths[j][1] != paths[(j + 1) % len(paths)][0] for j in range(len(paths))):
            raise ArithmeticError('absorbed midpoint circle is not a closed core path')
        cycle = []
        for crossing in crossings:
            cycle.extend([dict(dimension=0, handle=crossing['start']),
                          dict(dimension=1, handle=crossing['handle'])])
        number = len(core['handles2']) + len(added)
        added.append(dict(id=number, cycle=cycle))
        records.append(dict(attachment=index, base_profile=base, two_handle=number,
                            crossings=crossings))
    augmented = dict(core, handles2=core['handles2'] + added)
    proof = dict(schema='disk-bundle-absorption-v1', components=records)
    check()
    return augmented, proof, absorbed
