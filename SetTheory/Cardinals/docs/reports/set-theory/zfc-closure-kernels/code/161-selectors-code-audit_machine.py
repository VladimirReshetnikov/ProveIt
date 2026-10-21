#!/usr/bin/env python3
"""Literal canonical-table audit and reproducible typeset transition table."""
from pathlib import Path
import argparse, hashlib, json

def need(ok, message):
    if not ok: raise ValueError(message)

def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()

def parse(p):
    t={}
    for no,line in enumerate(p.read_text().splitlines(),1):
        if not line or line.startswith('#'): continue
        cells=line.split();need(len(cells)==5,f'Bad row {no}')
        q,b,w,d,z=cells;q,b,w,z=map(int,(q,b,w,z))
        need(b in (0,1) and w in (0,1) and d in ('L','R'),'Invalid action')
        need((q,b) not in t,'Duplicate row')
        t[q,b]=(w,d,z)
    return t

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--machine',type=Path,required=True)
    ap.add_argument('--trace',type=Path,required=True)
    ap.add_argument('--out',type=Path,required=True)
    a=ap.parse_args();a.out.mkdir(parents=True,exist_ok=True)
    np=a.machine/'k215.native.tm';cp=a.machine/'k215.tm'
    n,c=parse(np),parse(cp)
    mapping=json.loads((a.machine/'canonicalization.json').read_text())
    m={int(q):v for q,v in mapping['native_to_canonical'].items()}
    Q={q for q,b in n}
    need(len(Q)==215 and len(n)==430,'Native census')
    need(set(n)=={(q,b) for q in Q for b in (0,1)},'Native totality')
    need(set(m)==Q|{254} and set(m.values())==set(range(216)),'Total bijection')
    need(m[0]==0 and m[254]==215,'Canonical start/halt')
    need(set(c)=={(q,b) for q in range(215) for b in (0,1)},'Canonical totality')
    need(c=={(m[q],b):(w,d,m[z]) for (q,b),(w,d,z) in n.items()},'Literal conjugacy')
    need({z for w,d,z in c.values()}-set(range(215))=={215},'Canonical halt target')
    reached={0};todo=[0]
    for q in todo:
        for b in (0,1):
            z=c[q,b][2]
            if z!=215 and z not in reached:reached.add(z);todo.append(z)
    need(reached==set(range(215)),'Graph reachability')
    # Fresh canonical execution uses a finite-support set on the whole integer tape.
    saved=json.loads(a.trace.read_text());ones=set();q=h=0
    for i,(nq,nh,b,w,d,nz) in enumerate(saved['trace']):
        need(q==m[nq] and h==nh and int(h in ones)==b,f'Canonical prefix {i}')
        cw,cd,cz=c[q,b]
        need((cw,cd,cz)==(w,'R' if d==1 else 'L',m[nz]),'Canonical action')
        if cw:ones.add(h)
        else:ones.discard(h)
        h+=1 if cd=='R' else -1;q=cz
    need(q==m[84] and h==-8 and sorted(ones)==saved['one_cells'],'Canonical whole endpoint')
    def action(q,b):
        w,d,z=c[q,b]
        return f'{w}{d}'+('H' if z==215 else str(z))
    lines=[r'\begin{longtable}{rll@{\hspace{12mm}}rll}',
           r'\toprule State & Read 0 & Read 1 & State & Read 0 & Read 1\\',
           r'\midrule\endfirsthead',
           r'\toprule State & Read 0 & Read 1 & State & Read 0 & Read 1\\',
           r'\midrule\endhead',r'\bottomrule\endfoot']
    for q in range(108):
        first=f'{q} & {action(q,0)} & {action(q,1)}'
        z=q+108
        second=f'{z} & {action(z,0)} & {action(z,1)}' if z<215 else ' & & '
        lines.append(first+' & '+second+r'\\')
    lines.append(r'\end{longtable}')
    (a.out/'full_table.tex').write_text('\n'.join(lines)+'\n')
    result={'status':'PASS_CANONICAL_LITERAL_MACHINE','native_sha256':sha(np),
        'canonical_sha256':sha(cp),'working_states':215,'transition_rows':430,
        'canonical_start':0,'canonical_halt':215,'canonical_dispatcher':m[84],
        'all_working_states_graph_reachable':True,'canonical_prefix_steps':len(saved['trace']),
        'canonical_entire_tape_matches_native':True,'table_tex_sha256':sha(a.out/'full_table.tex'),
        'scope':'Finite table, bijective renaming, exact blank prefix, and literal table rendering.'}
    (a.out/'canonical-check.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))
if __name__=='__main__':main()
