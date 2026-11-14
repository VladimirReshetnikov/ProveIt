#!/usr/bin/env python3
"""Exact graph comparison with all current 193/194 literal frontier tables.

Allows arbitrary state renaming, every graph-spanning root, whole-tape
reflection, global symbol complementation, and ignores the write/move made
on a terminal halt edge. This enlarged equivalence is conservative for
novelty; complementing bits alone need not preserve zero-blank semantics.
"""
from pathlib import Path
import argparse,hashlib,json

def parse(path):
    rows={}
    for line in Path(path).read_text().splitlines():
        line=line.split('#',1)[0].strip()
        if not line:continue
        q,b,w,d,n=line.split();q,b,w,n=map(int,(q,b,w,n))
        if b not in (0,1) or w not in (0,1) or d not in ('L','R') or (q,b) in rows:
            raise ValueError('invalid row')
        rows[q,b]=(w,d,n)
    states={q for q,b in rows}
    if not states or any((q,b) not in rows for q in states for b in (0,1)):
        raise ValueError('incomplete binary table')
    halts={n for w,d,n in rows.values()}-states
    if len(halts)!=1:raise ValueError('requires exactly one rowless halt label')
    return rows,states

def canonical(rows,states):
    best=None
    for flip in (0,1):
        for mirror in (0,1):
            for root in sorted(states):
                seen={root:0};todo=[root];out=[]
                for q in todo:
                    for bit in (0,1):
                        w,d,n=rows[q,bit^flip]
                        if n not in states:
                            out.append((-1,-1,-1))
                        else:
                            if n not in seen:
                                seen[n]=len(seen);todo.append(n)
                            out.append((w^flip,int(d=='R')^mirror,seen[n]))
                if len(seen)==len(states):
                    key=tuple(out)
                    if best is None or key<best:best=key
    return best

def freeze(base):
    classes=json.loads((base/'table_classes.json').read_text())
    out=[]
    for row in classes:
        if row['states'] not in (193,194) or not row['has_graph_spanning_root']:continue
        file=base/'frontier_tables'/(row['table_class']+'.tm')
        parsed=parse(file);key=canonical(*parsed)
        if key is None:raise RuntimeError(file)
        out.append({'table_class':row['table_class'],'states':row['states'],
                    'source':row['representative'],'file':'frontier_tables/'+file.name,
                    'raw_sha256':hashlib.sha256(file.read_bytes()).hexdigest(),
                    'canonical_sha256':hashlib.sha256(json.dumps(key,separators=(',',':')).encode()).hexdigest(),
                    'canonical_tuple':key})
    (base/'novelty_corpus.json').write_text(json.dumps({'source_revision':'2337ce611a26e308697ccbddb2a1636f989f01c3','graphs':out},separators=(',',':'))+'\n')
    print(json.dumps({'frozen_graphs':len(out),'by_states':{n:sum(r['states']==n for r in out) for n in (193,194)}},indent=2))

def check(candidate,base):
    rows,states=parse(candidate);key=canonical(rows,states)
    if key is None:raise ValueError('candidate does not admit a graph-spanning root')
    corpus=json.loads((base/'novelty_corpus.json').read_text())
    matches=[];compared=0
    for row in corpus['graphs']:
        if row['states']!=len(states):continue
        file=base/row['file']
        if hashlib.sha256(file.read_bytes()).hexdigest()!=row['raw_sha256']:
            raise ValueError('frozen corpus table bytes changed: '+str(file))
        old=tuple(tuple(a) for a in row['canonical_tuple'])
        if hashlib.sha256(json.dumps(old,separators=(',',':')).encode()).hexdigest()!=row['canonical_sha256']:
            raise ValueError('frozen canonical tuple changed')
        compared+=1
        if old==key:matches.append({'table_class':row['table_class'],'source':row['source']})
    result={'candidate':str(candidate),'working_states':len(states),'transition_rows':len(rows),
        'raw_sha256':hashlib.sha256(Path(candidate).read_bytes()).hexdigest(),'reference_revision':corpus['source_revision'],
        'graphs_compared':compared,'exact_tuple_matches':matches,'structurally_new_in_recognized_corpus':not matches,
        'equivalences':'control renaming; any spanning root; reflection; bit complement; ignored halt-edge action',
        'limitations':'Finite graph novelty only. No state lower bound, no global priority claim, no consistency proof, no claim about unmaterialized parameter generators.'}
    print(json.dumps(result,indent=2));return result

if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('candidate',nargs='?',type=Path)
    ap.add_argument('--base',type=Path,default=Path(__file__).parent);ap.add_argument('--freeze',action='store_true')
    args=ap.parse_args()
    if args.freeze:freeze(args.base)
    elif args.candidate is not None:check(args.candidate,args.base)
    else:ap.error('provide candidate or --freeze')
