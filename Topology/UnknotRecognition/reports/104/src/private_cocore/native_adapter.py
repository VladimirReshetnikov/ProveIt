"""Narrow proposed adapter for already-authenticated native source records.

Caller obligations are explicit: authenticate raw cut, forest, augmented
handle structure, source annulus midpoint curves and their disjointness.
This module intentionally does not register a new whole-cut proof schema.
"""
from .core import produce_certificate
from .verify import verify_certificate


def source_matrices(augmented, core_proof, curves):
    """Extract exactly the unsigned counts used by the maintained v1 replay.

    curves are independently reconstructed records with 'attachment' and
    'crossings'; each crossing has 'handle' and 'start'. Forest columns are
    kept as zero columns, preserving original one-handle labels.
    """
    n = len(augmented['handles1'])
    forest = set(core_proof['forest'])
    if any(type(h) is not int or not 0 <= h < n for h in forest):
        raise ValueError('invalid forest column')
    owner = {}
    for component in core_proof['components']:
        for v in component['zero_handles']:
            if v in owner:
                raise ValueError('repeated zero-handle owner')
            owner[v] = component['id']
    real, passive, components = [], [], []
    for handle in augmented['handles2']:
        row = {}
        for f in handle['cycle']:
            if f['dimension'] == 1 and f['handle'] not in forest:
                h = f['handle']; row[h] = row.get(h, 0) + 1
        real.append(row)
    used_attachments = set()
    for curve in curves:
        if curve['attachment'] in used_attachments or not curve['crossings']:
            raise ValueError('repeated attachment or empty source curve')
        used_attachments.add(curve['attachment'])
        ids = {owner[c['start']] for c in curve['crossings']}
        if len(ids) != 1:
            raise ValueError('source curve crosses core components')
        components.append(next(iter(ids)))
        row = {}
        for crossing in curve['crossings']:
            h = crossing['handle']
            if h not in forest:
                row[h] = row.get(h, 0) + 1
        passive.append(row)
    return real, n, passive, components, owner


def query_authenticated_curves(augmented, core_proof, curves):
    """Produce and independently replay the matrix query; raise on nonzero fill.

    A returned missing witness is INCONCLUSIVE for the topological caller.
    Legacy nonzero-fill schedules must use the established dense replay.
    """
    real, n, passive, components, owner = source_matrices(augmented, core_proof, curves)
    cert = produce_certificate(real, n, passive, core_proof['cancellations'])
    if not verify_certificate(real, n, passive, cert):
        raise AssertionError('internal independent replay failure')
    witnesses = []
    for i, h in enumerate(cert['least_private']):
        if h == -1:
            continue
        if owner[augmented['handles1'][h]['ends'][0]] != components[i]:
            raise ValueError('private cocore has wrong source component')
        witnesses.append({'attachment': curves[i]['attachment'],
                          'core_component': components[i], 'one_handle': h})
    return {'query_schema': 'private-cocore-native-query-v1', 'matrix_proof': cert,
            'witnesses': witnesses, 'all_private': len(witnesses) == len(curves)}
