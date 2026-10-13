"""Signed source words for passive annuli on an authenticated handlebody core.

This adapter makes no topological conclusion and does no word reduction.
The enclosing caller must authenticate the parallelity geometry, boundary
skeleton, disk absorption, and successful core proof.  In particular, signs
come from oriented source face flags, not from endpoint order: a one-handle
can have equal endpoints and still has two distinct oriented face flags.
"""

from .disk_bundle_absorption import source_core_circle
from .integer_codec import certificate_equal


def signed_annulus_source(g, summary, skeleton, augmented, core_proof, *,
                          check=lambda: None):
    """Return a raw signed source packet, or None for an unsupported input.

    Letters are ``sign * (one_handle_id + 1)``.  A forest crossing contributes
    the empty word.  Both active relators and passive annular curves retain
    their cyclic starting point and orientation; no free or cyclic reduction
    occurs here.  Only leaf and column-leaf core proofs are supported.  All
    supplied inputs are conditional on the enclosing source authentication.
    """
    check()
    if ((core_proof.get('schema'), core_proof.get('method')) not in (
            ('normal-core-handlebody-v1', 'leaf'),
            ('normal-core-handlebody-v2', 'column_leaf'))):
        return None
    core = g['core']
    if core['handles3'] or augmented['handles3']:
        return None
    tree = set(core_proof['forest'])
    owner = {v: c['id'] for c in core_proof['components']
             for v in c['zero_handles']}
    profiles = summary['base_profiles']
    base_owner = {port: i for i, p in enumerate(profiles)
                  for port in p['core_ports']}
    for dimension in (0, 1, 3):
        if not certificate_equal(augmented[f'handles{dimension}'],
                                 core[f'handles{dimension}']):
            return None
    original_count = len(core['handles2'])
    if not certificate_equal(augmented['handles2'][:original_count],
                             core['handles2']):
        return None

    active = []
    for row in core['handles2']:
        check()
        word = []
        component = owner[row['cycle'][0]['handle']]
        for flag in row['cycle']:
            check()
            if flag['dimension'] != 1:
                if owner[flag['handle']] != component:
                    return None
                continue
            h = core['handles1'][flag['handle']]
            source = (h['tetrahedron'], h['face'])
            target = (h['target_tetrahedron'], h['target_face'])
            occurrence = (flag['tetrahedron'], flag['face'])
            if source == target:
                return None
            if occurrence == source:
                sign = 1
            elif occurrence == target:
                sign = -1
            else:
                return None
            if h['id'] not in tree:
                word.append(sign * (h['id'] + 1))
        active.append(dict(two_handle=row['id'], core_component=component,
                           word=word))

    passive, added, absorbed = [], [], set()
    for index, attachment in enumerate(skeleton['attachment_components']):
        check()
        if attachment['kind'] == 'interval':
            continue
        if attachment['kind'] != 'circle' or not attachment['word']:
            return None
        ports = [abs(x) - 1 for x in attachment['word']]
        bases = {base_owner[p] for p in ports}
        if len(bases) != 1:
            return None
        base = bases.pop()
        profile = profiles[base]
        components = set()
        for p in ports:
            port = g['ports'][p]
            vertex = (port['core_handle'] if port['core_dimension'] == 0 else
                      core['handles1'][port['core_handle']]['ends'][0])
            components.add(owner[vertex])
        if len(components) != 1:
            return None
        component = components.pop()
        crossings, cycle = source_core_circle(g, attachment['word'], check=check)
        word = [x['sign'] * (x['handle'] + 1) for x in crossings
                if x['handle'] not in tree]
        if (profile['euler_characteristic'], profile['boundary_components']) == (1, 1):
            if (base in absorbed or profile['multiplicity'] != 1 or not profile['orientable'] or
                    not profile['product'] or set(profile['core_ports']) != set(ports)):
                return None
            absorbed.add(base)
            number = original_count + len(added)
            added.append(dict(id=number, cycle=cycle))
            active.append(dict(two_handle=number, core_component=component,
                               word=word))
        else:
            if profile['multiplicity'] != 1 or profile['boundary_components'] < 1:
                return None
            passive.append(dict(attachment=index, base_profile=base,
                                core_component=component, word=word))
    if not certificate_equal(augmented['handles2'][original_count:], added):
        return None

    components = []
    for c in core_proof['components']:
        check()
        generators = [h['id'] + 1 for h in core['handles1']
                      if h['id'] not in tree and owner[h['ends'][0]] == c['id']]
        components.append(dict(id=c['id'], generators=generators,
                               surviving_generators=[h + 1 for h in
                                                     c['remaining_one_handles']]))
    return dict(schema='signed-core-annulus-source-v1',
                method=core_proof['method'], forest=list(core_proof['forest']),
                active=active, passive=passive, components=components,
                cancellations=[[r, h + 1] for r, h in core_proof['cancellations']])
