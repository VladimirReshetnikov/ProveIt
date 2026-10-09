"""Offline, input-bound exposure-to-overlap experiment; not runtime dispatch.

Load the immutable delivery from git, reconstruct its residual by replaying
its recorded moves, apply one maintained overlap, then hand off to maintained
compressed search. Search, reconstruction and continuation share work and time;
final verification has the same separate work allowance as group_decide.
"""
from collections import Counter
from hashlib import sha256
from io import BytesIO
import json
from pathlib import Path, PurePosixPath
import subprocess
import sys
from tempfile import TemporaryDirectory
from time import monotonic
import zipfile

FAST=Path(__file__).resolve().parents[1]
REPO=FAST.parents[2]
ARRIVAL='613bec60c3aa2d7bacba247732cf323adae08017'
ARCHIVE='docs/incoming/unknot_whitehead_exposure_20261008.zip'
ARCHIVE_SHA='52f91e8e3e1c50f334fedd42243c449b7ef7cd8e8044660887084c5b49102a17'
sys.path.insert(0,str(FAST))
from fastunknot import Diagram
from fastunknot.group_certificate import (
    _Budget,_presentation,_reduce,_image,_certificate_version,
    verify_group_certificate,GroupLimit)
from fastunknot.relator_overlap import overlap_move,apply_overlap
from fastunknot.compressed_search import _continue_compressed


def load_delivery():
    """Return the temporary-directory owner; keep it alive while using imports."""
    blob=subprocess.check_output(['git','show',ARRIVAL+':'+ARCHIVE],cwd=REPO)
    assert sha256(blob).hexdigest()==ARCHIVE_SHA
    tmp=TemporaryDirectory(prefix='exposure-residual-')
    with zipfile.ZipFile(BytesIO(blob)) as archive:
        assert sum(i.file_size for i in archive.infolist())<100000000
        for i in archive.infolist():
            p=PurePosixPath(i.filename)
            assert not p.is_absolute() and '..' not in p.parts
            assert i.external_attr>>16 & 0o170000 != 0o120000
        archive.extractall(tmp.name)
    root=Path(tmp.name)/'unknot_whitehead_exposure_20261008'
    lines=(root/'MANIFEST.sha256').read_text().splitlines()
    assert len(lines)==44
    for line in lines:
        h,n=line.split(None,1)
        assert sha256((root/n.lstrip('*')).read_bytes()).hexdigest()==h
    sys.path.insert(0,str(root/'src'))
    return tmp


def replay_prefix(words,alive,moves,budget):
    """Reconstruct the intermediate state; the full verifier remains separate."""
    words=[list(w) for w in words]
    for move in moves:
        if move['kind']=='whitehead':
            a=move['multiplier'];shore=set(move['subset'])
            assert abs(a) in alive and a in shore and -a not in shore
            assert all(abs(x) in alive for x in shore)
            # The delivery permits one 3M Whitehead workspace before a rank drop.
            assert 3*sum(map(len,words))<=3*budget.max_letters
            words=[_reduce((y for x in w for y in _image(x,a,shore)),budget) for w in words]
        elif move['kind']=='eliminate':
            index,g=move['relation'],move['generator'];assert g in alive
            target=words[index]
            positions=[i for i,x in enumerate(target) if abs(x)==g]
            assert len(positions)==1
            p=positions[0];rest=target[p+1:]+target[:p]
            replacement=[-x for x in reversed(rest)] if target[p]>0 else rest
            inverse=[-x for x in reversed(replacement)]
            words[index]=[]
            words=[_reduce((x for h in w for x in
                (replacement if h==g else inverse if h==-g else (h,))),budget) for w in words]
            alive.remove(g)
            budget.size(sum(map(len,words)))
        else:raise AssertionError('unexpected delivered move')
    return words


def residual_probe(pd, *, seconds=15, max_work=20000000,max_letters=200000,max_nodes=100000,
                   check=lambda:None):
    from whitehead_exposure.engine import search_presentation
    from whitehead_exposure.algebra import word_graph
    from whitehead_exposure.selector import unit_bridges
    start=monotonic();expires=start+seconds
    stats={};moves=[]
    def tick():
        check()
        if monotonic()>=expires:raise GroupLimit('residual experiment wall allowance exhausted')
    try:
        tick();diagram=Diagram.from_pd(pd);tick()
        budget=_Budget(tick,max_letters,max_work)
        alive,words=_presentation(diagram,budget)
        initial_alive=alive.copy()
        stage=search_presentation(words,alive,max_letters=max_letters,max_work=budget.left,check=tick)
        budget.tick(stage['work'])
        moves=list(stage['moves'])
        stats['exposure_events']=sum(t['kind']=='exposure' for t in stage['trace'])
        stats['prefix_reason']=stage['reason']
        stats['prefix_moves']=len(moves)
        stats['prefix_work']=stage['work']
        words=replay_prefix(words,initial_alive,moves,budget);alive=initial_alive
        stats['residual_rank']=len(alive);stats['residual_letters']=sum(map(len,words))
        vertices=tuple(sorted(alive|{-g for g in alive}))
        def bridge_counts():
            budget.tick(sum(map(len,words))+len(alive))
            return sum(len(unit_bridges(word_graph(w),vertices)) for w in words)
        stats['unit_bridges_before']=bridge_counts()
        stats['singletons_before']=sum(v==1 for w in words for v in Counter(map(abs,w)).values())
        if len(alive)>1:
            overlap=overlap_move(words,budget)
            stats['first_overlap']=overlap
            if overlap is not None:
                apply_overlap(words,overlap,budget,_reduce);moves.append(overlap)
            stats['after_overlap_letters']=sum(map(len,words))
            stats['unit_bridges_after']=bridge_counts()
            stats['singletons_after']=sum(v==1 for w in words for v in Counter(map(abs,w)).values())
            completed=_continue_compressed(words,alive,moves,budget,max_nodes,True,stats)
        else:completed=not any(words)
        stats['search_work']=max_work-budget.left
        stats['moves']=len(moves)
        if not completed:
            return dict(status='INCONCLUSIVE',reason='maintained continuation stalled',stats=stats,
                        seconds=monotonic()-start)
        cert=dict(version=_certificate_version(moves),method='wirtinger-cyclic-group',status='UNKNOT',
            input_pd=[list(row) for row in diagram.pd],moves=moves,remaining_generator=next(iter(alive)))
        for compressed in (False,True):
            if not verify_group_certificate(diagram,cert,compressed=compressed,check=tick,
                max_letters=3*max_letters,max_work=max_work,max_nodes=max_nodes):
                raise ArithmeticError('independent full-source replay failed')
        tick()
        return dict(status='UNKNOT',certificate=cert,stats=stats,seconds=monotonic()-start)
    except GroupLimit as error:
        check()
        return dict(status='INCONCLUSIVE',reason=str(error),stats=stats,seconds=monotonic()-start)
