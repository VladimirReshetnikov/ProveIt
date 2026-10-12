"""Opt-in source adapter for the incoming marked-parallelity implementation.

Requires that package's fastunknot modules on PYTHONPATH. It does not replace
the maintained recognizer, assume a core is a ball, or infer geometry from a
bare finite model. The certificates retain all established source proofs.
"""

from .finite import decode, encode, make_certificate
from .replay import verify_certificate


def _model(geometry, summary, skeleton, components, check):
    owner = {v: c['id'] for c in components for v in c['zero_handles']}
    profiles = summary['base_profiles']
    by_port = {}
    for index, profile in enumerate(profiles):
        for port in profile['core_ports']:
            if port in by_port:
                raise ArithmeticError('two bases claim one source port')
            by_port[port] = index
    core_port = {}
    for port in geometry['ports']:
        check()
        dimension, handle = port['core_dimension'], port['core_handle']
        if dimension == 0:
            vertex = handle
        elif dimension == 1:
            vertex = geometry['core']['handles1'][handle]['ends'][0]
        else:
            raise ArithmeticError('invalid core-facing dimension')
        core_port[port['id']] = owner[vertex]
    if set(by_port) != set(core_port):
        raise ArithmeticError('base and core port inventories differ')
    model = dict(cores=[dict(id=c['id'], genus=c['genus']) for c in components],
        bases=[dict(id=i, chi=p['euler_characteristic'],
                    boundary=p['boundary_components'], orientable=p['orientable'],
                    multiplicity=p['multiplicity']) for i, p in enumerate(profiles)],
        attachments=[])
    seen_ports = set()
    for index, attachment in enumerate(skeleton['attachment_components']):
        check()
        ports = [abs(letter) - 1 for letter in attachment['word']]
        if not ports or any(p in seen_ports for p in ports) or len(set(ports)) != len(ports):
            raise ArithmeticError('attachment words do not partition source ports')
        seen_ports.update(ports)
        choices = {(by_port[p], core_port[p]) for p in ports}
        if len(choices) != 1:
            raise ArithmeticError('connected attachment has inconsistent source owners')
        base, core = choices.pop()
        model['attachments'].append(dict(id=index, base=base, core=core,
                                         kind=attachment['kind']))
    if seen_ports != set(by_port):
        raise ArithmeticError('incomplete source attachment inventory')
    return model


def normal_cut_unsaturated_handlebodies(triangulation, coordinates, *,
        max_cycles=None, record_certificate=False, check=lambda: None):
    """Exact source-bound census, now allowing every unsaturated annular base."""
    from fastunknot.normal_parallelity import normal_cut_parallelity
    from fastunknot.core_handlebody import core_handlebody_certificate
    from fastunknot.parallelity_boundary_words import normal_parallelity_boundary_words

    check()
    if type(record_certificate) is not bool:
        raise ValueError('record_certificate must be bool')
    if max_cycles is not None and (type(max_cycles) is not int or max_cycles < 0):
        raise ValueError('invalid orbit budget')
    result = dict(status='INCONCLUSIVE', stats={},
                  trust='source-bound unmarked cut census; no standalone knot verdict')
    parallelity = normal_cut_parallelity(triangulation, coordinates,
        max_cycles=max_cycles, record_certificate=record_certificate, check=check)
    result['stats']['parallelity'] = parallelity['stats']
    if parallelity['status'] != 'COMPLETE':
        result['reason'] = 'parallelity_budget_exhausted'
        return result
    core = core_handlebody_certificate(parallelity['geometry']['core'], check=check)
    result['stats']['core'] = core.get('stats', {})
    if core['status'] != 'COMPLETE':
        result['reason'] = core['reason']
        return result
    remaining = max_cycles
    if remaining is not None:
        remaining -= sum(s['orbit_cycles'] for s in parallelity['stats'].values())
    boundary = normal_parallelity_boundary_words(triangulation, coordinates,
        max_cycles=remaining, record_certificate=record_certificate, check=check)
    result['stats']['boundary'] = boundary['stats']
    if boundary['status'] != 'COMPLETE':
        result['reason'] = 'boundary_budget_exhausted'
        return result
    model = _model(parallelity['geometry'], parallelity['summary'],
                   boundary['skeleton'], core['components'], check)
    reduced = make_certificate(model, check=check)
    if reduced['status'] != 'COMPLETE':
        result.update(reason=reduced['reason'], bases=reduced.get('bases', []))
        return result
    census = reduced['census']
    summary = parallelity['summary']
    expected = (summary['core_euler_characteristic']
                + summary['bundle_euler_characteristic']
                - summary['attachment_euler_characteristic'])
    if census['euler_characteristic'] != expected:
        raise ArithmeticError('native source Euler value disagrees')
    result.update(status='COMPLETE', census=census)
    if record_certificate:
        result['certificate'] = dict(schema='normal-cut-unsaturated-handlebodies-v1',
            parallelity=parallelity['certificate'], boundary=boundary['certificate'],
            core=core['certificate'], reduction=reduced['certificate'])
    return result


def verify_normal_cut_unsaturated_handlebodies(triangulation, coordinates,
        certificate, *, max_operations=None, check=lambda: None):
    """Replay source proofs, authenticate owners, then use the independent census."""
    from fastunknot.core_handlebody_verify import verify_core_handlebody_certificate
    from fastunknot.normal_parallelity_verify import verify_normal_cut_parallelity
    from fastunknot.parallelity_boundary_words_verify import verify_parallelity_boundary_words

    check()
    if max_operations is not None and (type(max_operations) is not int or max_operations < 0):
        raise ValueError('invalid verification operation budget')
    try:
        if type(certificate) is not dict or set(certificate) != {
                'schema', 'parallelity', 'boundary', 'core', 'reduction'}:
            return False
        if certificate['schema'] != 'normal-cut-unsaturated-handlebodies-v1':
            return False
        p, b, c = certificate['parallelity'], certificate['boundary'], certificate['core']
        if max_operations is not None:
            operations = 0
            for name in ('vertex_selector', 'boundary_selector', 'polygon_weights', 'fibre_cover'):
                proof = p[name]
                if name.endswith('selector'):
                    proof = proof['weighted_certificate']
                operations += len(proof['orbit_proof']['operations'])
            for name in ('vertex_partition', 'gap_cover'):
                if b[name] is not None:
                    operations += len(b[name]['orbit_proof']['operations'])
            if operations > max_operations:
                return False
        if not verify_normal_cut_parallelity(triangulation, coordinates, p, check=check):
            return False
        if not verify_parallelity_boundary_words(triangulation, coordinates, b, check=check):
            return False
        geometry, summary, skeleton = decode(p['geometry']), decode(p['summary']), decode(b['skeleton'])
        if not verify_core_handlebody_certificate(geometry['core'], c, check=check):
            return False
        # Decode the core component labels only after its independent verifier.
        components = decode(c['components'])
        model = _model(geometry, summary, skeleton, components, check)
        if not verify_certificate(model, certificate['reduction'], check=check):
            return False
        claimed = decode(certificate['reduction']['census'])
        expected = (summary['core_euler_characteristic']
                    + summary['bundle_euler_characteristic']
                    - summary['attachment_euler_characteristic'])
        return encode(claimed['euler_characteristic']) == encode(expected)
    except (KeyError, TypeError, ValueError, ArithmeticError, IndexError):
        return False
