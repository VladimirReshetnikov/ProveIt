#!/usr/bin/env python3
"""Independently replay the eight-state restoring scanner positive control."""
import argparse
import json
from pathlib import Path

def verify(path):
    record = json.loads(Path(path).read_text())
    if record['status'] != 'sat' or record['states'] != 8:
        raise ValueError('Expected the eight-state SAT positive-control table.')
    table = {(q,b):(w, -1 if d=='L' else 1, t)
             for q,b,w,d,t in record['rows']}
    if len(table) != 16:
        raise ValueError('Expected sixteen binary transition rows.')
    runs=[]
    for k in range(1,9):
        original = {1} | ({-k} if k<8 else set())
        ones=original.copy(); q=0; head=0; visited=[]
        goalstate=0 if k<8 else 8
        goalhead=-k-1 if k<8 else -8
        for tick in range(33):
            if tick and (q,head,ones)==(goalstate,goalhead,original):
                runs.append(dict(run_length=k, steps=tick,
                    read_min=min(visited), read_max=max(visited),
                    final_head=head, entire_tape_restored=True))
                break
            lower=-k if k<8 else -7
            if not lower <= head <= 1:
                raise ValueError(('Read outside the prescribed input window',k,tick,head))
            if (q,int(head in ones)) not in table:
                raise ValueError(('Premature exit',k,tick,q,head))
            visited.append(head)
            write,move,q=table[q,int(head in ones)]
            if write:ones.add(head)
            else:ones.discard(head)
            head+=move
        else:
            raise ValueError(('Bound exceeded',k))
    return dict(status='PASS', cases=8, runs=runs,
        scope='Literal finite cases with no reads outside the known input; '
              'arbitrary external contexts are untouched, and the long case '
              'extends to the infinite zero ray.')

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('table',type=Path)
    ap.add_argument('--output',type=Path)
    args=ap.parse_args(); result=verify(args.table)
    text=json.dumps(result,indent=2)+'\n'
    if args.output:args.output.write_text(text)
    print(text,end='')

if __name__=='__main__':main()
