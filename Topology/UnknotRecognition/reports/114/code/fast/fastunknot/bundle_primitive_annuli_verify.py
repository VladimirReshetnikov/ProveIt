"""Independent primitive-family replay from source-authenticated interfaces."""

from .integer_codec import certificate_equal


def replay_primitive_bundle_annuli(summary, skeleton, certificate, *, check=lambda: None):
    check()
    # Authenticate ownership for every port on each complete attaching circle.
    by_port = {}
    for i, profile in enumerate(summary['base_profiles']):
        for port in profile['core_ports']:
            by_port[port] = i
    families = {}
    for j, a in enumerate(skeleton['attachment_components']):
        check()
        if a['kind'] == 'interval':
            continue
        if a['kind'] != 'circle' or not a['word']:
            return None
        ports = [abs(x) - 1 for x in a['word']]
        base = by_port[ports[0]]
        if any(by_port[p] != base for p in ports):
            return None
        families.setdefault(base, []).append(j)
    expected, deductions = [], {}
    for base in sorted(families):
        check()
        p = summary['base_profiles'][base]
        if (p['euler_characteristic'], p['boundary_components']) == (1, 1):
            continue
        attachments = families[base]
        spare = p['boundary_components'] - len(attachments)
        genus = 1 - p['euler_characteristic'] - len(attachments)
        if spare < 1 or genus < 0 or p['multiplicity'] != 1:
            return None
        expected.append(dict(base_profile=base, annular_attachments=attachments,
                             spare_boundary_components=spare, reduced_genus=genus))
        deductions[base] = len(attachments)
    if not certificate_equal(certificate,
            dict(schema='bundle-primitive-annuli-v1', components=expected)):
        return None
    check()
    return deductions
