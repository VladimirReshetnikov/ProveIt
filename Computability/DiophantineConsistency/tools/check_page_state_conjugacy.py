#!/usr/bin/env python3
"""Check the entire native language and compact modes after state renaming.

Uses inert transition data and explicit finite constructors, not an archived
emitter. The rejected old initializer is a regression control for the gap
corrected in the compressed pages. Universal language equivalence follows
by applying the two color bijections to every edge of a tiled rectangle.
"""
import argparse
import hashlib
import json
from pathlib import Path

import research_seed_compression54 as compression
import verify_one_page_tuple54 as tuple54

ROOT = Path(__file__).resolve().parents[1]


def need(ok, message):
    if not ok:
        raise ValueError(message)


def language(actions):
    right_states = sorted({t for q,b,v,m,t in actions if m == 1})
    left_states = sorted({t for q,b,v,m,t in actions if m == -1})
    need((len(right_states),len(left_states)) == (199,45), "target populations")
    right = {q:6+j for j,q in enumerate(right_states)}
    left = {q:205+j for j,q in enumerate(left_states)}
    head = lambda q,b: 2*(q+1)+b
    tiles = {(0,head(q,b),right[t],v) if m == 1
             else (left[t],head(q,b),0,v) for q,b,v,m,t in actions}
    tiles.update((0,head(215,b),0,head(215,b)) for b in (0,1))
    tiles.update((0,b,0,b) for b in (0,1))
    tiles.update((right[q],b,0,head(q,b)) for q in right for b in (0,1))
    tiles.update((0,b,left[q],head(q,b)) for q in left for b in (0,1))
    tiles.update((0,c,0,438) for c in (0,1,432,433))
    initializer = (3,436,4,head(actions[0][4],0))
    tiles.update([(2,434,2,0),(2,435,3,1),initializer,(4,436,4,0)])
    tiles.update((1,438,1,c) for c in (434,435,436))
    tiles.update((a,437,b,437) for a in (0,1,4) for b in (0,1,2))
    tiles.add((5,0,0,0))
    start,forbidden = (2,435,3,1),(5,0,0,0)
    ordered = [start,forbidden]+sorted(tiles-{start,forbidden})
    need(len(ordered) == 943, "whole native language")
    return ordered,right,left,initializer


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--output",type=Path)
    args = ap.parse_args()
    seed_path = ROOT/"candidates/one-page/COMPACT54_SEED.txt"
    seed = int(seed_path.read_text())
    original = [compression.digit(seed,1024,j) for j in range(430)]
    _,renamed,_,pi,_ = compression.encode_bfs(original)
    _,old_actions,_,_ = tuple54.construct(seed)
    _,new_actions,_,_ = tuple54.construct(compression.row_seed(renamed))
    source = ROOT/"con-zfc-diophantine-forms/36-small-tuple/coefficients/k215_transitions.json"
    need(old_actions == json.loads(source.read_text())["transitions"], "original action identity")
    old,orr,oll,old_init = language(old_actions)
    new,nrr,nll,new_init = language(new_actions)
    hm = {c:c for c in range(6)}
    hm.update({orr[q]:nrr[pi[q]] for q in orr})
    hm.update({oll[q]:nll[pi[q]] for q in oll})
    vm = {0:0,1:1,**{c:c for c in range(434,439)}}
    vm.update({2*(q+1)+b:2*(pi[q]+1)+b for q in range(216) for b in (0,1)})
    need(len(set(hm.values())) == len(hm) and len(set(vm.values())) == len(vm), "color bijections")
    image = {(hm[w],vm[n],hm[e],vm[s]) for w,n,e,s in old}
    need(image == set(new), "all943 native tiles conjugate")
    old_raw = (json.dumps(old,separators=(",",":"))+"\n").encode()
    need(hashlib.sha256(old_raw).hexdigest() ==
         "66b55f1d11fca9fefc93b12fcfc8b4cabb75b08e9fd03311f9e894a1c5e5e81f",
         "authentic original full language")
    broken = set(new)-{new_init}|{old_init}
    need(image != broken, "old hardcoded initializer must fail full conjugacy")
    result = dict(status="PASS",all430_transitions_conjugate=True,
                  all943_native_tiles_conjugate=True,
                  all457_compact_modes=compression.check_mode_conjugacy(original,renamed,pi,tuple54),
                  horizontal_color_bijection_size=len(hm),vertical_color_bijection_size=len(vm),
                  old_native_initializer=list(old_init),new_native_initializer=list(new_init),
                  omitted_initializer_renaming_rejected=True,
                  original_language_sha256=hashlib.sha256(old_raw).hexdigest(),
                  first_action_old=old_actions[0],first_action_new=new_actions[0],
                  source_transition_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),
                  scope="Exact finite premises for ordinary edge-color language conjugacy; no Lean or new native/internal-ZFC theorem.")
    text = json.dumps(result,indent=2,sort_keys=True)+"\n"
    if args.output:
        args.output.write_text(text)
    print(text,end="")


if __name__ == "__main__":
    main()
