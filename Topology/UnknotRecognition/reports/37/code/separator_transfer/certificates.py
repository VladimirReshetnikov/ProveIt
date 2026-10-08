"""Portable, small-input braid certificates with a dense independent verifier.

Certificates are tied to a reconstructed reduced Khovanov cube. In particular,
user-supplied graph dimensions alone are NEVER interpreted as a knot proof.
"""
from __future__ import annotations
import hashlib, json
from dataclasses import asdict
from .core import (CutCertificate, minimum_vertex_cut, verify_cut_certificate,
                   dense_transfer, binary_basis, factor_at_cut, F2)
from .cube import reduced_cube, closure_components, acyclic_matching, morse_graphs
from .budgets import sharp_rank_budget

def _fingerprint(c):
    data = dict(degrees=c.degrees,quantum=c.quantum,edges=c.edges)
    return hashlib.sha256(json.dumps(data,separators=(',',':')).encode()).hexdigest()

def make_braid_certificate(strands,word,matching_edge_limit=None):
    if closure_components(strands,word) != 1: raise ValueError("this certificate format requires a knot")
    c = reduced_cube(strands,word); pairs = acyclic_matching(c,matching_edge_limit)
    counts,graphs = morse_graphs(c,pairs); caps = {}; ranks = {}; records = []
    for key,g in sorted(graphs.items()):
        cut = minimum_vertex_cut(g); rank = factor_at_cut(g,cut.cut,F2()).binary_rank()
        caps[key] = cut.capacity; ranks[key] = rank
        records.append(dict(degree=list(key),cut=asdict(cut),rank=rank))
    total_rank = sum(counts.values())-2*sum(ranks.values())
    if total_rank < 1: raise ArithmeticError("invalid knot rank")
    return dict(format='unknot-first-hit-certificate-v1',strands=strands,word=list(word),
                cube_sha256=_fingerprint(c),matching=[list(e) for e in pairs],maps=records,
                sharp_lower=sharp_rank_budget(counts,caps)['homology_lower'],
                reduced_rank=total_rank,verdict='UNKNOT' if total_rank == 1 else 'KNOTTED')

def verify_braid_certificate(cert):
    """Rebuild cube, verify acyclicity and cut flows, use DENSE path transfer.

    Does not call the matching search, min-cut optimizer, or factorized rank.
    This independence costs exponential reference-cube and dense-matrix work.
    """
    try:
        if cert['format'] != 'unknot-first-hit-certificate-v1': return False
        s,word = cert['strands'],cert['word']
        if closure_components(s,word) != 1: return False
        c = reduced_cube(s,word)
        if _fingerprint(c) != cert['cube_sha256']: return False
        counts,graphs = morse_graphs(c,tuple(map(tuple,cert['matching'])))
        records = {}
        for rec in cert['maps']:
            key = tuple(rec['degree'])
            if key in records: return False
            records[key] = rec
        if set(records) != set(graphs): return False
        ranks = {}; caps = {}
        for key,g in graphs.items():
            rec = records[key]; raw = rec['cut']
            cut = CutCertificate(tuple(raw['cut']),raw['capacity'],tuple(raw['flows']))
            if not verify_cut_certificate(g,[1]*g.n,cut): return False
            rows,_ = dense_transfer(g,F2())
            rank = len(binary_basis([sum(row[j] << i for i,row in enumerate(rows))
                                    for j in range(len(g.sources))]))
            if type(rec['rank']) is not int or rank != rec['rank'] or rank > cut.capacity: return False
            ranks[key] = rank; caps[key] = cut.capacity
        total = sum(counts.values())-2*sum(ranks.values())
        verdict = 'UNKNOT' if total == 1 else 'KNOTTED'
        return (total >= 1 and type(cert['reduced_rank']) is int and total == cert['reduced_rank']
                and verdict == cert['verdict']
                and sharp_rank_budget(counts,caps)['homology_lower'] == cert['sharp_lower'])
    except (KeyError,TypeError,ValueError,IndexError,ArithmeticError): return False
