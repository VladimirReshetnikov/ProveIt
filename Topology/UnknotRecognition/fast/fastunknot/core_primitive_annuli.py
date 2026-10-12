"""Source annular curves transported through certified geometric core pivots.

Private surviving cocores certify a simultaneous primitive family on the
core side. Counts remain unsigned and saturated; no free reduction is used.
The inputs require authenticated source charts and a successful core proof.
"""

from .core_handlebody import _occurrences
from .disk_bundle_absorption import source_core_circle


def core_primitive_annuli(geometry, summary, skeleton, augmented, core_proof, *, check=lambda: None):
    check()
    profiles = summary['base_profiles']
    by_port = {p: i for i, b in enumerate(profiles) for p in b['core_ports']}
    owner = {v: c['id'] for c in core_proof['components'] for v in c['zero_handles']}
    tree = set(core_proof['forest'])
    active = _occurrences(augmented, tree, check)
    passive, records, component = {}, [], {}
    for index, attachment in enumerate(skeleton['attachment_components']):
        check()
        if attachment['kind'] != 'circle':
            continue
        bases = {by_port[abs(x) - 1] for x in attachment['word']}
        if len(bases) != 1:
            raise ArithmeticError('annular circle has multiple base owners')
        base = bases.pop()
        p = profiles[base]
        if (p['euler_characteristic'], p['boundary_components']) == (1, 1):
            continue
        if p['multiplicity'] != 1 or p['boundary_components'] < 1:
            return None
        crossings, _ = source_core_circle(geometry, attachment['word'], check=check)
        row = {}
        for crossing in crossings:
            h = crossing['handle']
            if h not in tree:
                row[h] = min(2, row.get(h, 0) + 1)
        if not crossings:
            return None
        component[index] = owner[crossings[0]['start']]
        if any(owner[c['start']] != component[index] for c in crossings):
            raise ArithmeticError('annulus crosses disconnected cores')
        passive[index] = row
        records.append(dict(attachment=index, base_profile=base, crossings=crossings))
    updates = 0
    for r, h in core_proof['cancellations']:
        check()
        donor = active.pop(r)
        if donor.pop(h, 0) != 1:
            raise ArithmeticError('uncertified core pivot')
        for row in list(active.values()) + list(passive.values()):
            check()
            count = row.pop(h, 0)
            if count:
                for v, n in donor.items():
                    row[v] = min(2, row.get(v, 0) + count * n)
                    updates += 1
    if active:
        raise ArithmeticError('core proof leaves active two-handles')
    frequencies = {}
    for row in passive.values():
        for h in row:
            frequencies[h] = frequencies.get(h, 0) + 1
    witnesses, final_rows = [], []
    for index, row in sorted(passive.items()):
        check()
        private = [h for h, n in row.items() if n == 1 and frequencies[h] == 1]
        if not private:
            return None
        h = min(private)
        if owner[augmented['handles1'][h]['ends'][0]] != component[index]:
            raise ArithmeticError('private cocore has wrong component')
        witnesses.append(dict(attachment=index, core_component=component[index], one_handle=h))
        final_rows.append(dict(attachment=index, counts=[[h, n] for h, n in sorted(row.items())]))
    check()
    return dict(schema='core-primitive-annuli-v1', curves=records,
                final_rows=final_rows, witnesses=witnesses), component, dict(entry_updates=updates)
