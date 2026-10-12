"""Independent signed-source, quotient, and common-basis replay for annuli."""

from .compressed_words import CompressedLimit, WordArena
from .cyclic_basis_verify import verify_cyclic_basis
from .signed_annulus_source_verify import verify_signed_annulus_source


def _quotient_words(arena, packet):
    """Independent source-recursion evaluation; do not import the producer."""
    rows = {item['two_handle']: item['word'] for item in packet['active']}
    moves = packet['cancellations']
    if len(rows) != len(packet['active']) or len(moves) != len(rows):
        return None
    eliminated = [g for _, g in moves]
    if len(set(eliminated)) != len(eliminated) or {r for r, _ in moves} != set(rows):
        return None
    alive = [g for c in packet['components'] for g in c['surviving_generators']]
    all_labels = [g for c in packet['components'] for g in c['generators']]
    if (len(set(all_labels)) != len(all_labels) or set(alive) & set(eliminated) or
            set(all_labels) != set(alive) | set(eliminated)):
        return None
    substitution = {g: arena.letter(g) for g in alive}
    if packet['method'] == 'leaf':
        dead = set()
        for row, g in moves:
            word = rows[row]
            if (sum(abs(x) == g for x in word) != 1 or
                    any(abs(x) not in dead | {g} for x in word)):
                return None
            substitution[g] = 0
            dead.add(g)
    elif packet['method'] == 'column_leaf':
        # A pivot may occur only in rows removed no later than its own row.
        # Scan incidences once instead of scanning all rows for every pivot.
        deleted_at = {r: i for i, (r, _) in enumerate(moves)}
        pivot_at = {g: i for i, (_, g) in enumerate(moves)}
        for row, word in rows.items():
            arena.tick()
            for letter in word:
                arena.tick()
                time = pivot_at.get(abs(letter))
                if time is not None and deleted_at[row] > time:
                    return None
        for row, g in moves:
            if sum(abs(x) == g for x in rows[row]) != 1:
                return None
        for row, g in moves[::-1]:
            word = rows[row]
            location = next(i for i, letter in enumerate(word) if abs(letter) == g)
            letters = word[location + 1:] + word[:location]
            if word[location] > 0:
                letters = [-x for x in reversed(letters)]
            value = 0
            for letter in letters:
                if abs(letter) not in substitution:
                    return None
                piece = substitution[abs(letter)]
                if letter < 0:
                    piece = arena.inverse(piece)
                value = arena.concat(value, piece)
            substitution[g] = value
    else:
        return None
    roots = []
    for record in packet['passive']:
        value = 0
        for letter in record['word']:
            if abs(letter) not in substitution:
                return None
            piece = substitution[abs(letter)]
            value = arena.concat(value, piece if letter > 0 else arena.inverse(piece))
        roots.append(value)
    return roots


def replay_signed_annulus_basis(g, summary, skeleton, augmented, core_proof,
                                certificate, *, max_nodes=1000000,
                                max_work=10000000, check=lambda: None):
    """Return the reconstructed attachment owners, or None on failed replay.

    Source geometry, disk absorption, and the geometric core certificate must
    already have been authenticated by the enclosing whole-cut verifier.
    """
    try:
        if (type(certificate) is not dict or set(certificate) !=
                {'schema', 'source', 'components'} or
                certificate['schema'] != 'signed-primitive-annuli-v1' or
                type(certificate['components']) is not list):
            return None
        packet = certificate['source']
        if not verify_signed_annulus_source(g, summary, skeleton, augmented,
                                            core_proof, packet, check=check):
            return None
        arena = WordArena(max_nodes=max_nodes, max_work=max_work, check=check)
        roots = _quotient_words(arena, packet)
        if roots is None or len(certificate['components']) != len(packet['components']):
            return None
        owners = {}
        for component, proof in zip(packet['components'], certificate['components']):
            if (type(proof) is not dict or set(proof) !=
                    {'core_component', 'slots', 'basis'} or
                    type(proof['core_component']) is not int or
                    proof['core_component'] != component['id']):
                return None
            slots = [i for i, row in enumerate(packet['passive'])
                     if row['core_component'] == component['id']]
            if (type(proof['slots']) is not list or
                    any(type(i) is not int for i in proof['slots']) or proof['slots'] != slots):
                return None
            if not verify_cyclic_basis(arena, [roots[i] for i in slots],
                                        component['surviving_generators'], proof['basis']):
                return None
            for i in slots:
                row = packet['passive'][i]
                owners[row['attachment']] = component['id']
        return owners
    except (KeyError, TypeError, ValueError, IndexError, CompressedLimit):
        return None
