"""Primitive annulus families certified by an unused base boundary component.

Inputs are authenticated source base profiles and marked boundary words.
Disjoint base arcs to a remaining boundary lift to disjoint dual disks;
their endpoints can avoid all proper interval attachments. This is an
existence certificate for whole-cut topology, not explicit pattern transport.
"""


def primitive_bundle_annuli(summary, skeleton, *, check=lambda: None):
    check()
    profiles = summary['base_profiles']
    owner = {p: i for i, profile in enumerate(profiles) for p in profile['core_ports']}
    circles = {}
    for index, attachment in enumerate(skeleton['attachment_components']):
        check()
        if attachment['kind'] != 'circle':
            continue
        owners = {owner[abs(x) - 1] for x in attachment['word']}
        if len(owners) != 1:
            raise ArithmeticError('one circle has multiple base owners')
        base = owners.pop()
        circles.setdefault(base, []).append(index)
    components, counts = [], {}
    for base, attachments in sorted(circles.items()):
        check()
        p = profiles[base]
        chi, boundary = p['euler_characteristic'], p['boundary_components']
        if chi == 1 and boundary == 1:
            continue  # Disk absorption authenticates and consumes this case.
        count = len(attachments)
        if boundary <= count or p['multiplicity'] != 1 or 1 - chi < count:
            return None
        counts[base] = count
        components.append(dict(base_profile=base, annular_attachments=attachments,
                               spare_boundary_components=boundary - count,
                               reduced_genus=1 - chi - count))
    check()
    return dict(schema='bundle-primitive-annuli-v1', components=components), counts
