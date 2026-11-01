#!/usr/bin/env python3
"""Inventory helpers for the score-coding v3 direct-dependency replay."""
import hashlib
import os
from pathlib import Path

SUFFIXES=('.olean','.olean.private','.olean.server','.ir','.ilean',
          '.olean.hash','.olean.private.hash','.olean.server.hash','.ir.hash','.ilean.hash')
CHECKS=('import DiophantineConsistency.AdaptiveGap85ScoreCoding\n'
        '#print axioms DiophantineConsistency.AdaptiveGap85ScoreCoding.zeroScore_definable\n'
        '#print axioms DiophantineConsistency.AdaptiveGap85ScoreCoding.exists_minimizing_zero\n'
        '#print axioms DiophantineConsistency.AdaptiveGap85ScoreCoding.exists_minimal_blocked_unconditional\n'
        '#check DiophantineConsistency.AdaptiveGap85ScoreCoding.exists_minimal_blocked_unconditional\n').encode()
def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()
def describe(path):
    p=Path(path)
    if not os.path.lexists(p):return None
    if p.is_symlink():
        if not p.exists():raise RuntimeError(('broken symlink',str(p)))
        value={'kind':'symlink','target':os.readlink(p),'resolved':str(p.resolve())}
        if p.is_file():value['sha256']=sha(p)
        elif not p.is_dir():raise RuntimeError(('unsupported symlink',str(p)))
        return value
    if p.is_file():return {'kind':'file','resolved':str(p.resolve()),'sha256':sha(p)}
    if p.is_dir():return {'kind':'directory','resolved':str(p.resolve())}
    raise RuntimeError(('unsupported entry',str(p)))
def direct_entries(directory):
    return {p.name:describe(p) for p in sorted(Path(directory).iterdir())}
def companion_candidates(roots,modules):
    return {str(Path(root)/(module.replace('.','/')+suffix)):describe(Path(root)/(module.replace('.','/')+suffix))
            for root in roots for module in modules for suffix in SUFFIXES}
def verify_candidates(candidates):
    for path,expected in candidates.items():
        if describe(path)!=expected:raise RuntimeError(('candidate changed',path))
def private_inventory(root):
    root=Path(root);result={}
    def walk(directory):
        for p in sorted(directory.iterdir()):
            rel=str(p.relative_to(root));info=describe(p);result[rel]=info
            if info['kind']=='directory':walk(p)
    walk(root)
    return result
