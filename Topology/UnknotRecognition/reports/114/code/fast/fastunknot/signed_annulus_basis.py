"""Basis certificates for authenticated passive annuli after core cancellation.

The source compiler supplies signed words.  No coordinate multiplicity or
expanded substituted word is allocated.  The new terminal argument is Gordon's
simultaneous primitive-multicurve theorem, conditional on the existing source
geometry and geometric core certificate.
"""

from .compressed_words import CompressedLimit, WordArena
from .cyclic_basis import concatenate, cyclic_basis_blocks
from .signed_annulus_source import signed_annulus_source


def compile_signed_quotient(arena, packet):
    """Compile a column-private or row-leaf cancellation into a shared map.

    The input packet is conditional on authenticated geometry and a complete
    geometric core proof.  Extra algebraic checks here also protect standalone
    experiments from a false triangular schedule.
    """
    rows = {r['two_handle']: r['word'] for r in packet['active']}
    generators = sorted(g for c in packet['components'] for g in c['generators'])
    surviving = sorted(g for c in packet['components']
                       for g in c['surviving_generators'])
    schedule = packet['cancellations']
    if (len(rows) != len(packet['active']) or len(schedule) != len(rows) or
            {r for r, _ in schedule} != set(rows) or
            len({g for _, g in schedule}) != len(schedule) or
            set(generators) != set(surviving) | {g for _, g in schedule} or
            set(surviving) & {g for _, g in schedule}):
        raise ValueError('invalid complete signed cancellation schedule')
    images = {g: arena.letter(g) for g in surviving}
    images.update({-g: arena.inverse(images[g]) for g in surviving})
    if packet['method'] == 'leaf':
        removed = set()
        for row, g in schedule:
            arena.tick()
            word = rows[row]
            if (sum(abs(x) == g for x in word) != 1 or
                    any(abs(x) != g and abs(x) not in removed for x in word)):
                raise ValueError('false source row-leaf schedule')
            removed.add(g)
            images[g] = images[-g] = 0
    elif packet['method'] == 'column_leaf':
        for row, g in reversed(schedule):
            arena.tick()
            word = rows[row]
            positions = [i for i, letter in enumerate(word) if abs(letter) == g]
            if len(positions) != 1:
                raise ValueError('source donor does not have a unique pivot')
            pos = positions[0]
            donor = word[pos + 1:] + word[:pos]
            if any(letter not in images for letter in donor):
                raise ValueError('source dependencies are not triangular')
            value = concatenate(arena, (images[letter] for letter in donor))
            if word[pos] > 0:
                value = arena.inverse(value)
            images[g], images[-g] = value, arena.inverse(value)
    else:
        raise ValueError('unsupported signed cancellation method')
    if set(images) != set(generators) | {-g for g in generators}:
        raise ValueError('incomplete source quotient map')
    roots = [concatenate(arena, (images[x] for x in row['word']))
             for row in packet['passive']]
    return roots


def signed_annulus_basis(g, summary, skeleton, augmented, core_proof, *,
                         max_nodes=1000000, max_work=10000000, check=lambda: None):
    """Return (evidence, attachment owners, stats), or None on method refusal."""
    packet = signed_annulus_source(g, summary, skeleton, augmented, core_proof,
                                   check=check)
    if packet is None:
        return None
    arena = WordArena(max_nodes=max_nodes, max_work=max_work, check=check)
    try:
        roots = compile_signed_quotient(arena, packet)
        records, owners = [], {}
        for component in packet['components']:
            arena.tick()
            slots = [i for i, row in enumerate(packet['passive'])
                     if row['core_component'] == component['id']]
            chosen = [roots[i] for i in slots]
            result = cyclic_basis_blocks(arena, chosen, component['surviving_generators'])
            if result['status'] != 'COMPLETE':
                return None
            records.append(dict(core_component=component['id'], slots=slots,
                                basis=result['certificate']))
            for i in slots:
                owners[packet['passive'][i]['attachment']] = component['id']
        certificate = dict(schema='signed-primitive-annuli-v1', source=packet,
                           components=records)
        stats = dict(arena.stats, grammar_nodes=len(arena.rules) - 1,
                     source_letters=sum(len(r['word']) for r in packet['active'] +
                                        packet['passive']),
                     annuli=len(packet['passive']),
                     nielsen_moves=sum(len(c['basis']['moves']) for c in records))
        return certificate, owners, stats
    except CompressedLimit:
        return None
