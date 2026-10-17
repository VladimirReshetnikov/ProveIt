"""Find single-transition shortcuts with whole-window block certificates.

For every abstractly reachable window at an edited row, its proposed write,
move and target must equal an original positive finite block's exact resulting
whole window, head and control. The original block cannot read outside the
window. Thus one candidate step matches >=1 original steps, which preserves
blank-tape halting under deterministic iteration. Every window may use a
different original block length. Failed bounded search is not a lower bound.
"""
from __future__ import annotations
import argparse, hashlib, json, time
from pathlib import Path
from upstream_audit_tm import Machine, Edge, parse_table, window_reachable, graph_reachable
from incoming_row_search import trace


def options(machine,q,pattern,radius,bound):
    opts={}
    initial_other=pattern & ~(1<<radius)
    for i,(state,head,tape) in enumerate(trace(machine,q,0,pattern,radius,bound)):
        if i and head in (-1,1) and tape & ~(1<<radius)==initial_other:
            key=((tape>>radius)&1,head,state)
            opts.setdefault(key,i)
    return opts


def search(machine,radius,bound):
    t0=time.monotonic()
    windows=window_reachable(machine,radius)
    candidates=[]
    for q,patterns in windows.items():
        if q==machine.halt:
            continue
        for bit in (0,1):
            ps=[p for p in patterns if ((p>>radius)&1)==bit]
            if not ps:
                continue
            old=machine.rows[q,bit]
            choices=options(machine,q,ps[0],radius,bound)
            choices.pop((old.write,old.move,old.target),None)
            certificates={c:[[ps[0],n]] for c,n in choices.items()}
            for p in ps[1:]:
                if not choices:
                    break
                opts=options(machine,q,p,radius,bound)
                for c in list(choices):
                    if c not in opts:
                        choices.pop(c)
                        certificates.pop(c)
                    else:
                        certificates[c].append([p,opts[c]])
            for (w,d,s),cert in certificates.items():
                rows=dict(machine.rows);rows[q,bit]=Edge(w,d,s)
                reduced=Machine(machine.start,machine.halt,rows)
                reachable=graph_reachable(reduced)
                candidates.append({'edge':[q,bit], 'old':[old.write,old.move,old.target],
                                   'row':[w,d,s], 'certificate':cert,
                                   'unreachable_working_states':sorted(set(machine.states)-reachable)})
    return {'method':__doc__,'radius':radius,'bound':bound,
            'abstract_configurations':sum(map(len,windows.values())),
            'candidates':candidates,'elapsed_seconds':time.monotonic()-t0}


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('table',type=Path)
    ap.add_argument('--radius',type=int,default=6)
    ap.add_argument('--bound',type=int,default=64)
    ap.add_argument('--output',type=Path,required=True)
    args=ap.parse_args();data=args.table.read_bytes();m=parse_table(data.decode())
    out=search(m,args.radius,args.bound)
    out['input']={'sha256':hashlib.sha256(data).hexdigest(),'working_states':len(m.states),
                  'start':m.start,'halt':m.halt}
    out['script_sha256']=hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    args.output.write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps({k:v for k,v in out.items() if k not in ('method','candidates')}))
    print('candidates:',[(c['edge'],c['row'],c['unreachable_working_states']) for c in out['candidates']])


if __name__=='__main__':main()
