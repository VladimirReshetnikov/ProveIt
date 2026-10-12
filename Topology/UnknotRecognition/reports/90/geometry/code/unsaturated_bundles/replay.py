"""Independent graph traversal and relative-one-handle certificate replay.

The producer's union-find traversal and genus computation are not called.
Shared routines only validate the finite schema and encode exact integers.
"""

from collections import Counter

from .finite import decode, digest, encode, validate_model


def verify_certificate(model, certificate, *, check=lambda: None):
    check()
    try:
        proof = decode(certificate)
        if type(proof) is not dict or set(proof) != {'schema', 'input_sha256', 'census'}:
            return False
        if proof['schema'] != 'unsaturated-bundles-v1' or proof['input_sha256'] != digest(model):
            return False
        cores, bases, attached = validate_model(model)
        if any(base['boundary'] == 0 for base in bases.values()):
            return False
        reductions = []
        for key, edges in sorted(attached.items()):
            if not edges:
                continue
            circles = sum(e['kind'] == 'circle' for e in edges)
            intervals = len(edges) - circles
            if circles >= bases[key]['boundary']:
                return False
            reductions.append(dict(base=key, intervals=intervals, circles=circles,
                one_handles=intervals - bases[key]['chi'],
                residual_rank=1 - bases[key]['chi'] - circles))
        neighbors = {key: set() for key in cores}
        # Each connected attached base joins its incident core components.
        for edges in attached.values():
            owners = sorted({e['core'] for e in edges})
            if owners:
                for owner in owners[1:]:
                    neighbors[owners[0]].add(owner)
                    neighbors[owner].add(owners[0])
        unseen = set(cores)
        joined, histogram = [], Counter()
        while unseen:
            check()
            todo, seen = [min(unseen)], set()
            while todo:
                current = todo.pop()
                if current not in seen:
                    seen.add(current)
                    todo.extend(neighbors[current] - seen)
            unseen -= seen
            base_ids = sorted(key for key, edges in attached.items()
                              if edges and edges[0]['core'] in seen)
            ids = sorted(e['id'] for key in base_ids for e in attached[key])
            bands = sum(sum(e['kind'] == 'interval' for e in attached[key])
                        - bases[key]['chi'] for key in base_ids)
            genus = sum(cores[key]['genus'] for key in seen) + bands - len(seen) + 1
            beta = len(ids) - len(seen) - len(base_ids) + 1
            residual = bands - sum(len(attached[key]) - 1 for key in base_ids)
            if min(genus, beta, residual) < 0:
                return False
            joined.append(dict(cores=sorted(seen), bases=base_ids, attachments=ids,
                               cycle_rank=beta, residual_rank=residual, genus=genus))
            histogram[genus] += 1
        # Producer sorts by ('base', smallest id), then isolated core nodes.
        joined.sort(key=lambda item: ('base', item['bases'][0]) if item['bases']
                    else ('core', item['cores'][0]))
        isolated = []
        for key, base in sorted(bases.items()):
            if not attached[key]:
                g, m = 1 - base['chi'], base['multiplicity']
                isolated.append(dict(base=key, genus=g, multiplicity=m))
                histogram[g] += m
        total = sum(histogram.values())
        euler = sum(1 - core['genus'] for core in cores.values())
        euler += sum(b['chi'] * b['multiplicity'] for b in bases.values())
        euler -= sum(e['kind'] == 'interval' for e in model['attachments'])
        expected = dict(histogram=[dict(genus=g, multiplicity=m)
                                  for g, m in sorted(histogram.items())],
            components=total, ball_components=histogram[0],
            one_ball=(total == 1 and histogram[0] == 1),
            euler_characteristic=euler, joined=joined, isolated=isolated,
            reductions=reductions)
        # Exact typed comparison: True must not masquerade as integer 1.
        return encode(proof['census']) == encode(expected)
    except (KeyError, TypeError, ValueError, IndexError):
        return False
