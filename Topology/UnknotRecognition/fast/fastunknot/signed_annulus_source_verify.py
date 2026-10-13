"""Independent signed source reconstruction; no producer or word reducer import.

The enclosing verifier authenticates the parallelity charts, marked boundary,
absorbed disk bundles, and successful geometric core proof.  This checker
rebuilds the corresponding signed words, including self-loop orientations,
and authenticates the source packet consumed by later algebraic replay.
"""

from .disk_bundle_absorption_verify import reconstruct_core_circle
from .integer_codec import certificate_equal


def verify_signed_annulus_source(g, summary, skeleton, augmented, core_proof,
                                  certificate, *, check=lambda: None):
    """Replay a signed source packet conditional on enclosing authentication."""
    check()
    callback_failed = False
    def callback():
        nonlocal callback_failed
        try:
            check()
        except BaseException:
            callback_failed = True
            raise
    try:
        return _verify(g, summary, skeleton, augmented, core_proof, certificate, callback)
    except (ArithmeticError, IndexError, KeyError, TypeError, ValueError):
        if callback_failed:
            raise
        return False


def _verify(g, summary, skeleton, augmented, proof, certificate, check):
    fields = {'schema', 'method', 'forest', 'active', 'passive', 'components',
              'cancellations'}
    if type(certificate) is not dict or set(certificate) != fields:
        return False
    if ((proof['schema'], proof['method']) not in (
            ('normal-core-handlebody-v1', 'leaf'),
            ('normal-core-handlebody-v2', 'column_leaf'))):
        return False
    core = g['core']
    if core['handles3'] or augmented['handles3']:
        return False
    for k in ('handles0', 'handles1', 'handles3'):
        if not certificate_equal(core[k], augmented[k]):
            return False
    n = len(core['handles2'])
    if not certificate_equal(core['handles2'], augmented['handles2'][:n]):
        return False
    labels = {}
    for component in proof['components']:
        for vertex in component['zero_handles']:
            if vertex in labels:
                return False
            labels[vertex] = component['id']
    forest = set(proof['forest'])

    # This table uses the oriented source face, not either endpoint vertex.
    directions = {}
    for h in core['handles1']:
        check()
        left = (h['id'], h['tetrahedron'], h['face'])
        right = (h['id'], h['target_tetrahedron'], h['target_face'])
        if left == right:
            return False
        directions[left], directions[right] = h['id'] + 1, -h['id'] - 1
    relations = []
    for h in core['handles2']:
        check()
        vertices = [x['handle'] for x in h['cycle'] if x['dimension'] == 0]
        if not vertices or len({labels[v] for v in vertices}) != 1:
            return False
        letters = []
        for flag in h['cycle']:
            check()
            if flag['dimension'] == 1:
                value = directions[(flag['handle'], flag['tetrahedron'], flag['face'])]
                if flag['handle'] not in forest:
                    letters.append(value)
        relations.append(dict(two_handle=h['id'], core_component=labels[vertices[0]],
                              word=letters))

    boundary_profiles = summary['base_profiles']
    port_profiles = {}
    for i, p in enumerate(boundary_profiles):
        for port in p['core_ports']:
            if port in port_profiles:
                return False
            port_profiles[port] = i
    passengers, absorbed_rows, absorbed_bases = [], [], set()
    for i, a in enumerate(skeleton['attachment_components']):
        check()
        if a['kind'] == 'interval':
            continue
        if a['kind'] != 'circle' or not a['word']:
            return False
        ports = [abs(letter) - 1 for letter in a['word']]
        base = port_profiles[ports[0]]
        if any(port_profiles[port] != base for port in ports):
            return False
        pieces = []
        for port_id in ports:
            port = g['ports'][port_id]
            if port['core_dimension'] == 0:
                pieces.append(labels[port['core_handle']])
            elif port['core_dimension'] == 1:
                edge = core['handles1'][port['core_handle']]
                pieces.extend(labels[v] for v in edge['ends'])
            else:
                return False
        if len(set(pieces)) != 1:
            return False
        component = pieces[0]
        reconstructed = reconstruct_core_circle(g, a, check=check)
        if reconstructed is None:
            return False
        crossings, cycle = reconstructed
        letters = []
        for x in crossings:
            check()
            if x['handle'] not in forest:
                letters.append((x['handle'] + 1) * x['sign'])
        p = boundary_profiles[base]
        if (p['euler_characteristic'], p['boundary_components']) == (1, 1):
            if (base in absorbed_bases or p['multiplicity'] != 1 or
                    not p['orientable'] or not p['product'] or
                    set(p['core_ports']) != set(ports)):
                return False
            absorbed_bases.add(base)
            row = n + len(absorbed_rows)
            absorbed_rows.append(dict(id=row, cycle=cycle))
            relations.append(dict(two_handle=row, core_component=component, word=letters))
        else:
            if p['multiplicity'] != 1 or p['boundary_components'] < 1:
                return False
            passengers.append(dict(attachment=i, base_profile=base,
                                   core_component=component, word=letters))
    if not certificate_equal(augmented['handles2'][n:], absorbed_rows):
        return False

    component_records = []
    for c in proof['components']:
        check()
        generators = []
        for h in core['handles1']:
            if h['id'] not in forest and labels[h['ends'][0]] == c['id']:
                generators.append(h['id'] + 1)
        component_records.append(dict(id=c['id'], generators=generators,
                                      surviving_generators=[h + 1 for h in
                                                            c['remaining_one_handles']]))
    expected = dict(schema='signed-core-annulus-source-v1', method=proof['method'],
                    forest=proof['forest'], active=relations, passive=passengers,
                    components=component_records,
                    cancellations=[[r, h + 1] for r, h in proof['cancellations']])
    check()
    return certificate_equal(certificate, expected)
