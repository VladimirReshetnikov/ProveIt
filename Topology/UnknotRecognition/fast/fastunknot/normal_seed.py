"""Bounded native search for a source-certified cocycle unknot witness.

Try the primitive integral cocycle, then a bounded prelude of alternative
tree gauges, then optional span minimization and any requested later trees.
Finally try bounded extrema in the certified minimum-span face. Source-bound
connectedness witnesses avoid orbit searches for these restricted families.
Failure of the tested seeds says nothing about knottedness.
Primitive connected annuli can be capped on the exterior boundary; their
certificates distinguish them from normal discs.
"""
from .diagram import Diagram
from .diagram_exterior import diagram_exterior
from .normal_cocycle import _rank_one_cocycle_seed_details, _height_summary, _Budget, CocycleLimit
from .cocycle_span import minimize_cocycle_span
from .cocycle_trees import _prepared_tree_candidates
from .cocycle_face import cocycle_face_candidates
from .normal_cocycle_verify import inspect_cocycle_certificate
from .normal_surface_geometry import NormalOrbitError, _coordinates


def normal_seed_decide(diagram, *, optimize=True, annulus=True, planar=False, shellings=False, edge_span=False, max_work=2000000,
                       max_cycles=None, tree_trials=4, face_roots=0, check=lambda: None):
    """Return UNKNOT with a source-bound disc or capping proof, or INCONCLUSIVE.

    The shared work allowance covers construction, cocycle extraction, all
    tree and optimal-face trials, connectedness/Euler checks and span
    optimization. It is a deterministic guard-count allowance, not a count
    of bit operations or a time limit.
    Disc and annulus certificates require no interval-orbit cycles. Optional
    planar queries share max_cycles across all candidate boundary censuses.
    Their independent positive replay also shares the work allowance.
    shellings optionally removes embedded boundary tetrahedra before searching;
    its trace is replayed from the canonical source for every positive proof.
    It defaults to False and need not preserve the original candidate coverage.
    face_roots defaults to zero: optional face discovery adds coverage but
    was slower than the existing complete fallback on measured cases.
    """
    if type(optimize) is not bool:
        raise ValueError('optimize must be bool')
    if type(annulus) is not bool:
        raise ValueError('annulus must be bool')
    if type(shellings) is not bool:
        raise ValueError('shellings must be bool')
    if type(planar) is not bool:
        raise ValueError('planar must be bool')
    if type(edge_span) is not bool:
        raise ValueError('edge_span must be bool')
    if max_cycles is not None and (type(max_cycles) is not int or max_cycles < 0):
        raise ValueError('max_cycles must be a nonnegative integer or None')
    if type(tree_trials) is not int or tree_trials < 0:
        raise ValueError('tree_trials must be a nonnegative integer')
    if type(face_roots) is not int or face_roots < 0:
        raise ValueError('face_roots must be a nonnegative integer')
    budget = _Budget(check, max_work)
    stats, stages = {}, []
    boundary_cycles = 0
    planar_basis = None
    try:
        budget.tick()
        source = Diagram.from_pd(diagram.pd)
        raw = diagram_exterior(source, check=budget.tick)
        if shellings:
            from .boundary_shellings import shell_boundary
            from .normal_shelling_verify import inspect_shelling_cocycle, inspect_shelling_planar
            original = raw
            reduction = shell_boundary(raw, check=budget.tick)
            raw = reduction['triangulation']
            stats['shellings'] = reduction['stats']
        def wrap(surface):
            if not shellings:return surface
            return dict(schema='diagram-shelling-witness-v1', source_triangulation=original,
                        shellings=reduction['moves'], surface_certificate=surface)
        seed, prepared = _rank_one_cocycle_seed_details(raw, check=budget.tick)
        stats['cocycle'] = seed['stats']
        def evaluate(stage, heights, coordinates, span=None, candidate=None):
            nonlocal boundary_cycles, planar_basis
            budget.tick()
            certificate = dict(schema='diagram-cocycle-disc-v1', input_pd=[list(row) for row in source.pd],
                               triangulation=raw, heights=heights, coordinates=coordinates,
                               span_certificate=span)
            analysed = None
            if candidate is None:
                potential = None if span is None else dict(zip(span['vertex_ids'], span['potential']))
                candidate_summary = _height_summary(prepared, heights, potential=potential, check=budget.tick)
                euler, pieces = candidate_summary['euler_characteristic'], candidate_summary['normal_pieces']
            else:
                euler, pieces = candidate['euler_characteristic'], candidate['normal_pieces']
            # Candidate construction proves the family invariants. A miss is
            # not a negative knot certificate. Only potential positive proofs
            # pay for independent source/class/connectivity reconstruction.
            answer = dict(components=1, orientable_components=1,
                          euler_characteristic=euler, normal_pieces=pieces,
                          compressing_discs=0,
                          connectivity='minimum-span' if span is not None else 'zero-tree')
            if euler == 1 or (annulus and euler == 0):
                answer = (inspect_shelling_cocycle(source, wrap(certificate), check=budget.tick) if shellings
                          else inspect_cocycle_certificate(source, certificate, check=budget.tick))
                if answer is None:
                    raise ArithmeticError('source-bound cocycle connectivity replay failed')
            entry = dict(stage=stage, status='COMPLETE', **answer)
            if candidate is not None:
                keys = ('root_trial', 'root', 'direction') if stage == 'face' else ('trial', 'root', 'randomized')
                entry.update({k: candidate[k] for k in keys})
            stages.append(entry)
            capped_annulus = annulus and answer['euler_characteristic'] == 0
            if capped_annulus:
                # The independent inspection above establishes every
                # annulus-cap hypothesis. Only the witness tag changes;
                # compressing_discs remains zero for the stored surface.
                certificate['schema'] = 'diagram-cocycle-annulus-v1'
                entry['unknot_witness'] = 'annulus-cap'
            if answer['compressing_discs'] or capped_annulus:
                budget.tick()
                return dict(status='UNKNOT', method='native-normal-cocycle', certificate=wrap(certificate),
                            stats=stats, stages=stages, work=budget.work)
            if planar:
                from .normal_planar import _planar_cap_candidate
                from .normal_component_geometry import boundary_homology_basis
                from .normal_planar_verify import inspect_planar_certificate
                remaining = None if max_cycles is None else max_cycles-boundary_cycles
                if planar_basis is None:
                    planar_basis = boundary_homology_basis(prepared, budget.tick)
                if analysed is None:
                    analysed = _coordinates(prepared, coordinates, budget.tick)
                query = _planar_cap_candidate(certificate, prepared, analysed,
                    basis=planar_basis, max_cycles=remaining, check=budget.tick)
                boundary_cycles += query['stats']['orbit_cycles']
                entry['planar_query'] = {k: v for k, v in query.items() if k != 'certificate'}
                stats['boundary_cycles'] = boundary_cycles
                if 'certificate' in query:
                    proof = query['certificate']
                    summary = (inspect_shelling_planar(source, wrap(proof), check=budget.tick) if shellings
                               else inspect_planar_certificate(source, proof, check=budget.tick))
                    if summary is None:
                        raise ArithmeticError('source-bound planar capping replay failed')
                    entry.update(summary)
                    budget.tick()
                    return dict(status='UNKNOT', method='native-normal-cocycle', certificate=wrap(proof),
                                stats=stats, stages=stages, work=budget.work)
            return None

        result = evaluate('raw', seed['heights'], seed['coordinates'])
        if result is not None:
            return result
        candidates = iter(_prepared_tree_candidates(prepared, seed['heights'], trials=tree_trials, check=budget.tick))
        tree_stats = dict(attempts=0, duplicates=0, candidates=0)
        if tree_trials:
            stats['tree_search'] = tree_stats

        def tree_attempt():
            candidate = next(candidates)
            tree_stats['attempts'] += 1
            if candidate['duplicate']:
                tree_stats['duplicates'] += 1
                return None
            tree_stats['candidates'] += 1
            return evaluate('tree', candidate['heights'], candidate['coordinates'], candidate=candidate)

        # Bound the cheap prelude. Additional requested trees run only after
        # the exact span solver has had its chance, sharing the same budget.
        for _ in range(min(4, tree_trials)):
            result = tree_attempt()
            if result is not None:
                return result
        if optimize:
            optimized = minimize_cocycle_span(seed['vertices'], seed['heights'], check=budget.tick)
            stats['optimization'] = optimized['stats']
            result = evaluate('optimized', seed['heights'], optimized['coordinates'], optimized['certificate'])
            if result is not None:
                return result
        if edge_span:
            from .cocycle_lex import _prepared_minimize_edge_span
            from .cocycle_lex_verify import inspect_lex_cocycle_certificate
            selected=_prepared_minimize_edge_span(prepared,seed['heights'],
                optimized['certificate'] if optimize else None,budget.tick)
            stats['edge_span']=selected['stats']
            chi=selected['euler_characteristic']
            entry=dict(stage='edge-span',status='COMPLETE',euler_characteristic=chi,
                normal_pieces=selected['normal_pieces'],components=1,orientable_components=1,
                compressing_discs=0,connectivity='edge-then-span')
            if chi==1 or (annulus and chi==0):
                proof=dict(schema='diagram-cocycle-lex-v1',input_pd=[list(row) for row in source.pd],
                    triangulation=raw,heights=seed['heights'],coordinates=selected['coordinates'],
                    optimality_certificate=selected['certificate'])
                summary=(inspect_shelling_cocycle(source,wrap(proof),check=budget.tick) if shellings
                         else inspect_lex_cocycle_certificate(source,proof,check=budget.tick))
                if summary is None:raise ArithmeticError('edge/span primitive source replay failed')
                entry.update(summary);entry['unknot_witness']='annulus-cap' if chi==0 else 'disc'
                stages.append(entry)
                return dict(status='UNKNOT',method='native-normal-cocycle',certificate=wrap(proof),
                    stats=stats,stages=stages,work=budget.work)
            stages.append(entry)
        for _ in range(4, tree_trials):
            result = tree_attempt()
            if result is not None:
                return result
        if optimize and face_roots:
            face_stats = dict(candidates=0)
            stats['face_search'] = face_stats
            for candidate in cocycle_face_candidates(seed['vertices'], seed['heights'],
                    optimized['certificate'], roots=face_roots, check=budget.tick):
                face_stats['candidates'] += 1
                analysed = _coordinates(prepared, candidate['coordinates'], budget.tick)
                candidate.update(euler_characteristic=analysed['euler_characteristic'],
                                 normal_pieces=analysed['normal_disks'])
                result = evaluate('face', seed['heights'], candidate['coordinates'],
                                  candidate['certificate'], candidate)
                if result is not None:
                    return result
        reason = 'the tested cocycle seeds contain no certified compressing disc'
    except (CocycleLimit, NormalOrbitError) as exc:
        reason = str(exc)
    return dict(status='INCONCLUSIVE', method='native-normal-cocycle', reason=reason,
                stats=stats, stages=stages, work=budget.work)
