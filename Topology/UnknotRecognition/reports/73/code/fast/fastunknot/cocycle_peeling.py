"""Dynamic vertex-link-peeled scoring along certified cocycle collapses.

The geometric batch producer validates every committed change.  Stable
corner identities bridge its canonical renumbering; a separate dynamic
index stores just the ordered triangle records.  Scores are not disc or
unknot certificates, and the code performs no global cocycle regauging.
"""
from copy import deepcopy

from .corner_minima import CornerMinimumIndex
from .cocycle_transport import _integer_heights, _region_heights, bipyramid_cocycle_score
from .normal_cocycle import local_coordinates
from .normal_surface_geometry import _prepare, _coordinates


_NEW = ((0, 1, 2, 3), (0, 1, 2, 4))


class CocyclePeelingState:
    """A private validated geometric state with dynamically maintained minima.

    Repeated all-candidate queries retain the vertex summaries.  The census
    still scans/validates the current triangulation.  Thus the update theorem
    concerns the minima index, not the complete geometric search cost.
    """

    def __init__(self, triangulation, heights, *, check=lambda: None):
        self.check = check
        self._valid = True
        self.triangulation = deepcopy(triangulation)
        prepared = _prepare(self.triangulation, check)
        self.heights = _integer_heights(prepared, heights, check)
        coordinates = [local_coordinates(row) for row in self.heights]
        self._vertices = [prepared['vertex_roots'][4*t:4*t+4]
                          for t in range(len(coordinates))]
        self._corners = [[4*t+v for v in range(4)] for t in range(len(coordinates))]
        boundary = {prepared['vertex_roots'][4*t+v]
                    for t, f in prepared['boundary_faces'] for v in range(4) if v != f}
        link_euler = {v: 1 if v in boundary else 2 for v in prepared['vertex_roots']}
        records = [(self._vertices[t][v], self._corners[t][v], row[v])
                   for t, row in enumerate(coordinates) for v in range(4)]
        self.index = CornerMinimumIndex(records, link_euler, check=check)
        self._fresh = 4*len(coordinates)
        self.stats = dict(batches=0, moves=0, scored_candidates=0)

    def _ensure_valid(self):
        if not self._valid:
            raise RuntimeError('an interrupted commit invalidated this peeling state')

    def _plan(self, regions):
        removed_tets = set()
        removed, added, new_vertices, new_corners = [], [], [], []
        raw_gain = raw_saving = 0
        fresh = self._fresh
        for record in regions:
            self.check()
            region = {item['tetrahedron']: item['vertices'] for item in record}
            if len(region) != 3 or not removed_tets.isdisjoint(region):
                raise ValueError('a batch requires disjoint three-tetrahedron regions')
            removed_tets.update(region)
            formal_vertices = {}
            for t, labels in region.items():
                for v, label in enumerate(labels):
                    actual = self._vertices[t][v]
                    if label in formal_vertices and formal_vertices[label] != actual:
                        raise ValueError('formal vertices disagree with the current vertex classes')
                    formal_vertices[label] = actual
                    removed.append(self._corners[t][v])
            five = _region_heights(region, self.heights, self.check)
            local = bipyramid_cocycle_score(five)
            raw_gain += local['euler_loss']
            raw_saving += local['normal_disc_increase']
            for labels in _NEW:
                values = local_coordinates([five[v] for v in labels])
                vertices = [formal_vertices[v] for v in labels]
                corners = list(range(fresh, fresh+4))
                fresh += 4
                added.extend((vertex, identity, value)
                             for vertex, identity, value in zip(vertices, corners, values[:4]))
                new_vertices.append(vertices)
                new_corners.append(corners)
        summary = self.index.score_edit(removed, added)
        summary.update(raw_euler_gain=raw_gain, raw_piece_saving=raw_saving,
            peeled_euler_gain=raw_gain-summary['link_euler_delta'],
            peeled_piece_saving=raw_saving+summary['link_piece_delta'])
        return dict(removed_tets=removed_tets, removals=removed, additions=added,
                    new_vertices=new_vertices, new_corners=new_corners,
                    fresh=fresh, summary=summary)

    def score_candidates(self):
        """Return exact raw and peeled scores in a single current census.

        The geometric candidate generator validates the current cocycle.
        The twelve-delete/eight-insert minima query uses thirteen cached
        records per affected vertex.  Candidate scores are independently
        compared with full geometric replay by the research audit.
        """
        from .pachner_batch import pachner_32_regions
        self._ensure_valid()
        result = pachner_32_regions(self.triangulation, self.heights, check=self.check)
        for candidate in result['candidates']:
            self.check()
            candidate['peeling'] = self._plan([candidate['region']])['summary']
        self.stats['scored_candidates'] += len(result['candidates'])
        result['stats']['dynamic_prefix_capacity'] = 13
        return result

    def score_candidate_batch(self, candidates):
        """Collective score of an unmodified subset of the current census.

        This method does not independently validate externally edited
        candidate records.  ``apply_batch`` always validates actual moves
        before updating the state.  The score alone has no topology meaning.
        """
        self._ensure_valid()
        regions = sorted((c['region'] for c in candidates),
                         key=lambda r: min(item['tetrahedron'] for item in r))
        return self._plan(regions)['summary']

    def apply_batch(self, sites):
        """Commit a simultaneously certified batch, then update stable records.

        Interruption during the cache mutation invalidates the object; the
        caller must rebuild instead of reusing partially updated summaries.
        No unsafe partial object is returned after callback cancellation.
        """
        from .pachner_batch import pachner_32_batch
        self._ensure_valid()
        result = pachner_32_batch(self.triangulation, sites, self.heights, check=self.check)
        plan = self._plan(result['certificate']['regions'])
        proof = result['certificate']['cocycle']
        if (plan['summary']['raw_euler_gain'] != proof['euler_jump']
                or -plan['summary']['raw_piece_saving'] != proof['normal_disc_jump']):
            raise ArithmeticError('dynamic raw score disagrees with the geometric certificate')
        survivors = [t for t in range(len(self._vertices)) if t not in plan['removed_tets']]
        vertices = [self._vertices[t] for t in survivors] + plan['new_vertices']
        corners = [self._corners[t] for t in survivors] + plan['new_corners']
        self._valid = False
        self.index.commit_edit(plan['removals'], plan['additions'])
        self._vertices, self._corners, self._fresh = vertices, corners, plan['fresh']
        self.triangulation = deepcopy(result['triangulation'])
        self.heights = deepcopy(result['heights'])
        self.stats['batches'] += 1
        self.stats['moves'] += len(result['certificate']['regions'])
        self._valid = True
        result['peeling'] = plan['summary']
        fields = ('raw_euler_gain', 'raw_piece_saving', 'link_euler_delta',
                  'link_piece_delta', 'peeled_euler_gain', 'peeled_piece_saving')
        result['peeling_certificate'] = dict(schema='pachner-peeled-score-v1',
            **{key: plan['summary'][key] for key in fields})
        return result

    def optimal_subbatch(self, candidates):
        """Maximise peeled Euler gain on a supplied disjoint current census.

        Among equally good subsets, retain the largest number of moves.
        At most two rewarded interior vertices use the exact linear-time
        standard-library selector. General instances use an optional matching
        dependency. Chosen moves remain geometrically verified by ``apply_batch``.
        This does not optimise over mutually overlapping move candidates.
        """
        from .peeled_batch_selection import solve_two_endpoint_rewards
        self._ensure_valid()
        ordered = sorted(candidates, key=lambda c: min(
            item['tetrahedron'] for item in c['region']))
        plan = self._plan([candidate['region'] for candidate in ordered])
        gamma = {v['vertex']: v['minimum_after'] for v in plan['summary']['vertices']}
        items = []
        for candidate in ordered:
            self.check()
            region = {item['tetrahedron']: item['vertices'] for item in candidate['region']}
            local_minima = {}
            for t in region:
                for vertex, identity in zip(self._vertices[t], self._corners[t]):
                    value = self.index.records[identity][1]
                    local_minima[vertex] = min(local_minima.get(vertex, value), value)
            five = _region_heights(region, self.heights, self.check)
            cost = bipyramid_cocycle_score(five)['euler_loss']
            rewards = [[vertex, self.index.link_euler[vertex]*(gamma[vertex]-minimum)]
                       for vertex, minimum in sorted(local_minima.items())
                       if gamma[vertex] > minimum]
            if len(rewards) > 2 or any(value > cost for _, value in rewards):
                raise ArithmeticError('coherent-apex reward bound failed')
            items.append(dict(cost=cost, rewards=rewards))
        rewarded_interior = {vertex for item in items for vertex, value in item['rewards']
                             if value > 0 and self.index.link_euler[vertex] == 2}
        cover = sorted(rewarded_interior) if len(rewarded_interior) <= 2 else None
        selection = solve_two_endpoint_rewards(items, cover_vertices=cover, check=self.check)
        retained = [ordered[i] for i in selection['retained_indices']]
        predicted = plan['summary']['peeled_euler_gain']+selection['objective']
        actual = self.score_candidate_batch(retained)['peeled_euler_gain']
        if predicted != actual:
            raise ArithmeticError('matching objective disagrees with collective minima')
        interior = sum(value == 2 for value in self.index.link_euler.values())
        if len(selection['omitted_indices']) > len(rewarded_interior):
            raise ArithmeticError('optimal omission count exceeds the interior-vertex bound')
        return dict(sites=[dict(tetrahedron=c['tetrahedron'], vertices=c['vertices']) for c in retained],
            selection=selection, items=items, ground_set_size=len(ordered),
            retained_moves=len(retained), interior_vertices=interior,
            rewarded_interior_vertices=len(rewarded_interior),
            full_batch_peeled_euler_gain=plan['summary']['peeled_euler_gain'],
            optimal_peeled_euler_gain=predicted,
            trust='optimality uses the matching implementation; move correctness is independently replayed')

    def full_summary(self):
        """Independent full rescan for diagnostics; not used to score candidates."""
        self._ensure_valid()
        prepared = _prepare(self.triangulation, self.check)
        rows = [local_coordinates(row) for row in self.heights]
        analysed = _coordinates(prepared, rows, self.check)
        minima, counts = {}, {}
        boundary = {prepared['vertex_roots'][4*t+v]
                    for t, f in prepared['boundary_faces'] for v in range(4) if v != f}
        for t, row in enumerate(rows):
            self.check()
            for v in range(4):
                root = prepared['vertex_roots'][4*t+v]
                minima[root] = min(minima.get(root, row[v]), row[v])
                counts[root] = counts.get(root, 0)+1
        penalty = sum((1 if v in boundary else 2)*m for v, m in minima.items())
        pieces = sum(counts[v]*m for v, m in minima.items())
        return dict(raw_euler=analysed['euler_characteristic'],
                    peeled_euler=analysed['euler_characteristic']-penalty,
                    raw_pieces=analysed['normal_disks'],
                    peeled_pieces=analysed['normal_disks']-pieces,
                    link_euler=penalty, link_pieces=pieces)

    def audit_index(self):
        """Check all current stable records against freshly computed coordinates."""
        self._ensure_valid()
        self.index.verify_invariants()
        prepared = _prepare(self.triangulation, self.check)
        boundary = {prepared['vertex_roots'][4*t+v]
                    for t, f in prepared['boundary_faces'] for v in range(4) if v != f}
        stable_to_current, current_to_stable = {}, {}
        expected = {}
        for t, row in enumerate(self.heights):
            coordinates = local_coordinates(row)
            for v in range(4):
                stable = self._vertices[t][v]
                current = prepared['vertex_roots'][4*t+v]
                if (stable_to_current.setdefault(stable, current) != current
                        or current_to_stable.setdefault(current, stable) != stable
                        or self.index.link_euler[stable] != (1 if current in boundary else 2)):
                    raise ArithmeticError('stable vertices differ from freshly reconstructed links')
                expected[self._corners[t][v]] = (stable, coordinates[v])
        if expected != self.index.records:
            raise ArithmeticError('the dynamic record index differs from current coordinates')
        return True
