"""Delete one state and independently rewrite each incoming binary row.

This extends edge_redirect_search.py by allowing write and direction changes.
A certificate matches the original from the predecessor (including its edge
into removed p) against a replacement row and subsequent unchanged transitions.
Both sides make positive progress, and a match requires identical retained
state, relative head and whole known window. Replacement prefixes stop before
any further row targeting p, so choices for separate incoming edges compose.
All local contexts come from the conservative blank-window abstraction.
"""
from __future__ import annotations
import argparse, hashlib, json, time
from pathlib import Path
from upstream_audit_tm import parse_table, window_reachable


def trace(machine, start, head, pattern, radius, bound, forbidden=None):
    out = [(start, head, pattern)]
    q = start
    for _ in range(bound):
        if q == machine.halt or not -radius <= head <= radius:
            break
        pos = head + radius
        e = machine.rows[q, (pattern >> pos) & 1]
        if e.target == forbidden:
            break
        pattern = (pattern & ~(1 << pos)) | (e.write << pos)
        head += e.move
        q = e.target
        out.append((q, head, pattern))
    return out


def targets(machine, p, edge, pattern, radius, bound):
    out = {}
    for i, (q, head, tape) in enumerate(trace(machine, edge[0], 0, pattern, radius, bound)):
        if i and q != p:
            key = ('halt',) if q == machine.halt else (q, head, tape)
            out.setdefault(key, i)
    return out


def certify(machine, p, replacement, patterns, radius, bound, originals):
    write, move, q = replacement
    cert = []
    for pattern in patterns:
        tape = (pattern & ~(1 << radius)) | (write << radius)
        for j, (state, head, after) in enumerate(trace(machine, q, move, tape, radius,
                                                    bound - 1, forbidden=p), 1):
            key = ('halt',) if state == machine.halt else (state, head, after)
            if key in originals[pattern]:
                cert.append([pattern, originals[pattern][key], j])
                break
        else:
            return None
    return cert


def search(machine, radius, bound):
    t0 = time.monotonic()
    windows = window_reachable(machine, radius)
    rows = {(q,b): [w for w in ps if ((w >> radius)&1)==b]
            for q,ps in windows.items() if q != machine.halt for b in (0,1)}
    records, candidates, checks = [], [], 0
    for p in machine.states:
        incoming = [key for key,e in machine.rows.items() if e.target==p and key[0]!=p]
        incoming.sort(key=lambda key: -len(rows[key]))
        edges, complete = [], True
        for edge in incoming:
            patterns = rows[edge]
            originals = {w:targets(machine,p,edge,w,radius,bound) for w in patterns}
            accepted = []
            for q in machine.states:
                if q == p:
                    continue
                for write in (0,1):
                    for move in (-1,1):
                        checks += 1
                        c = certify(machine,p,(write,move,q),patterns,radius,bound,originals)
                        if c is not None:
                            accepted.append({'row':[write,'R' if move==1 else 'L',q],
                                             'certificate':c})
            edges.append({'edge':list(edge),'windows':len(patterns),'replacements':accepted})
            if not accepted:
                complete = False
                break
        # A removed initial state also needs an initial-state certificate. No
        # candidate that reaches here may be accepted without such a check.
        if complete and p == machine.start:
            raise RuntimeError('Initial-state survivor needs explicit blank-start certificate')
        rec={'deleted':p,'incoming_edges':len(incoming),'checked_edges':edges,
             'all_edges_certified':complete}
        records.append(rec)
        if complete:
            candidates.append(rec)
    return {'method':__doc__,'radius':radius,'bound':bound,
            'abstract_configurations':sum(map(len,windows.values())),
            'row_replacement_attempts':checks,'states':records,'candidates':candidates,
            'elapsed_seconds':time.monotonic()-t0}


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('table',type=Path)
    ap.add_argument('--radius',type=int,default=6)
    ap.add_argument('--bound',type=int,default=64)
    ap.add_argument('--output',type=Path,required=True)
    args=ap.parse_args()
    data=args.table.read_bytes();m=parse_table(data.decode())
    out=search(m,args.radius,args.bound)
    out['input']={'sha256':hashlib.sha256(data).hexdigest(),'working_states':len(m.states),
                  'start':m.start,'halt':m.halt}
    out['script_sha256']=hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    args.output.write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps({k:v for k,v in out.items() if k not in ('method','states','candidates')}))
    print('candidates:',[c['deleted'] for c in out['candidates']])


if __name__=='__main__':
    main()
