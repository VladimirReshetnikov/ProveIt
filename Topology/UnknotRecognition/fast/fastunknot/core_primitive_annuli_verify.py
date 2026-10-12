"""Independent source reconstruction and dense passive-incidence replay.

The enclosing verifier first authenticates geometry and the augmented core
cancellation proof. This module imports no curve or matrix producer.
"""

from .disk_bundle_absorption_verify import reconstruct_core_circle
from .integer_codec import certificate_equal


def replay_core_primitive_annuli(g, summary, skeleton, augmented, core_proof, certificate, *, check=lambda: None):
    check()
    profiles = summary['base_profiles']
    owner = {v: c['id'] for c in core_proof['components'] for v in c['zero_handles']}
    base_owner = {p: i for i, b in enumerate(profiles) for p in b['core_ports']}
    columns = len(augmented['handles1'])
    live = set(range(columns)) - set(core_proof['forest'])
    matrix = []
    for handle in augmented['handles2']:
        check()
        row = [0] * columns
        for flag in handle['cycle']:
            if flag['dimension'] == 1 and flag['handle'] in live:
                h = flag['handle']
                row[h] = min(2, row[h] + 1)
        matrix.append(row)
    pending, curves, attachment_ids, components = [], [], [], {}
    for index, a in enumerate(skeleton['attachment_components']):
        check()
        if a['kind'] == 'interval':
            continue
        if a['kind'] != 'circle' or not a['word']:
            return None
        ports = [abs(x) - 1 for x in a['word']]
        base = base_owner[ports[0]]
        if any(base_owner[p] != base for p in ports):
            return None
        p = profiles[base]
        if (p['euler_characteristic'], p['boundary_components']) == (1, 1):
            continue
        if p['multiplicity'] != 1 or p['boundary_components'] < 1:
            return None
        traced = reconstruct_core_circle(g, a, check=check)
        if traced is None or not traced[0]:
            return None
        crossings, _ = traced
        component = owner[crossings[0]['start']]
        if any(owner[c['start']] != component for c in crossings):
            return None
        row = [0] * columns
        for c in crossings:
            h = c['handle']
            if h in live:
                row[h] = min(2, row[h] + 1)
        pending.append(row)
        attachment_ids.append(index)
        components[index] = component
        curves.append(dict(attachment=index, base_profile=base, crossings=crossings))
    active = set(range(len(matrix)))
    for r, h in core_proof['cancellations']:
        check()
        if r not in active or h not in live or matrix[r][h] != 1:
            return None
        active.remove(r)
        live.remove(h)
        for row in [matrix[i] for i in sorted(active)] + pending:
            check()
            count = row[h]
            for j in live:
                row[j] = min(2, row[j] + count * matrix[r][j])
            row[h] = 0
    if active:
        return None
    witnesses, final_rows = [], []
    for i, (index, row) in enumerate(zip(attachment_ids, pending)):
        check()
        choices = [h for h in sorted(live) if row[h] == 1 and
                   all(other[h] == 0 for j, other in enumerate(pending) if j != i)]
        if not choices:
            return None
        h = choices[0]
        if owner[augmented['handles1'][h]['ends'][0]] != components[index]:
            return None
        witnesses.append(dict(attachment=index, core_component=components[index], one_handle=h))
        final_rows.append(dict(attachment=index, counts=[[h, row[h]] for h in sorted(live) if row[h]]))
    expected = dict(schema='core-primitive-annuli-v1', curves=curves,
                    final_rows=final_rows, witnesses=witnesses)
    if not certificate_equal(certificate, expected):
        return None
    check()
    return components
