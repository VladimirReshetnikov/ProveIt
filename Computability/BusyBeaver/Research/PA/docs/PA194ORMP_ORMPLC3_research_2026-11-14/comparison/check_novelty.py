#!/usr/bin/env python3
"""Replay exact structural novelty against the pinned complete194-class index.

Example:
  python3 -B check_novelty.py ../machines/PA194ORMP/machine.tm \
    ../machines/PA194ORMPLC3/machine.tm --output novelty.json

Only Python's standard library is used. The compressed index contains the
complete transition triples of every recognized spanning194 graph plus the
two nonspanning diagnostic tables. Every possible corpus root and all four
global reflection/bit orientations are checked. Final write/move actions are
ignored. These enlarged symmetries test structural distinctness; global bit
exchange is not asserted to preserve zero-blank behavior.

No table hash is used as an isomorphism decision. Comparison stops on a literal
tuple mismatch and declares a match only after every transition is equal.
This script proves no semantic or arithmetic calibration theorem.
"""
from pathlib import Path
import argparse, gzip, hashlib, json

def require(p,message):
    if not p:raise ValueError(message)

def parse_file(path):
    rows={}
    for line in path.read_text().splitlines():
        if not line.strip() or line.lstrip().startswith('#'):continue
        q,b,w,d,t=line.split();q,b,w,t=map(int,(q,b,w,t))
        require(b in (0,1) and w in (0,1) and d in ('L','R') and (q,b) not in rows,'invalid transition')
        rows[q,b]=(w,d,t)
    states={q for q,b in rows};terminal={t for w,d,t in rows.values()}-states
    require(len(rows)==2*len(states) and all((q,b) in rows for q in states for b in (0,1)),'incomplete table')
    require(len(terminal)==1,'expected a unique terminal control')
    return rows,states,next(iter(terminal))

def from_index(triples):
    require(len(triples)==388,'index table does not contain194 complete controls')
    rows={}
    for i,action in enumerate(triples):
        require(len(action)==3,'invalid index action')
        w,d,t=action
        require(w in (0,1) and d in ('L','R') and isinstance(t,int) and -1<=t<194,'invalid indexed transition')
        rows[i//2,i%2]=(w,d,t)
    return rows,set(range(194)),-1

def form(data,root,mirror=False,flip=False,loose=True):
    rows,states,halt=data;index={root:0};order=[root];out=[]
    for q in order:
        for b in (0,1):
            w,d,t=rows[q,b ^ int(flip)]
            if t==halt:
                out.append((0,'R',-1) if loose else (w ^ int(flip),('L' if d=='R' else 'R') if mirror else d,-1));continue
            if t not in index:index[t]=len(order);order.append(t)
            out.append((w ^ int(flip),('L' if d=='R' else 'R') if mirror else d,index[t]))
    return tuple(out),len(order)

def equals_root(data,root,expected):
    rows,states,halt=data;index={root:0};order=[root];pos=0
    for q in order:
        for b in (0,1):
            w,d,t=rows[q,b]
            if t==halt:triple=(0,'R',-1)
            else:
                if t not in index:index[t]=len(order);order.append(t)
                triple=(w,d,index[t])
            if pos==len(expected) or triple!=expected[pos]:return False
            pos+=1
    return pos==len(expected)

def orientations(data):
    out=[]
    for mirror in (False,True):
        for flip in (False,True):
            f,n=form(data,0,mirror,flip)
            require(n==len(data[1]),'candidate start0 does not reach every working control')
            out.append((mirror,flip,f))
    return out

def positive_controls(data,forms):
    labels={q:1000+7*q for q in data[1]};result=[]
    for mirror,flip,expected in forms:
        transformed={}
        for (q,b),(w,d,t) in data[0].items():
            if t==data[2]:a=(1,'L',999999)
            else:a=(w ^ int(flip),('L' if d=='R' else 'R') if mirror else d,labels[t])
            transformed[labels[q],b ^ int(flip)]=a
        require(equals_root((transformed,set(labels.values()),999999),labels[0],expected),'renamed oriented positive control failed')
        result.append({'mirror':mirror,'bit_exchange':flip,'renamed':True,'terminal_decoration_changed':True,'pass':True})
    return result

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('candidates',nargs='+',type=Path)
    ap.add_argument('--index',type=Path,default=Path(__file__).with_name('frontier194_index.json.gz'))
    ap.add_argument('--output',type=Path,required=True)
    args=ap.parse_args()
    index_bytes=args.index.read_bytes();index=json.loads(gzip.decompress(index_bytes))
    corpus=[]
    for c in index['classes']:
        d=from_index(c['rows']);f,n=form(d,0,loose=False)
        require(n==194,'indexed class has no spanning root0')
        h=hashlib.sha256(json.dumps(f,separators=(',',':')).encode()).hexdigest()
        require(h==c['action_graph_sha256'],'indexed class tuple binding failed')
        corpus.append((c,d))
    require(len(corpus)==index['source_census_summary']['spanning_classes_by_states']['194'],'corpus count mismatch')
    require(len({c['action_graph_sha256'] for c,d in corpus})==len(corpus),'duplicate corpus identity')
    for c in index['nonspanning194']:
        d=from_index(c['rows'])
        require(all(form(d,q)[1]<194 for q in d[1]),'alleged nonspanning diagnostic has a spanning root')
    cases=[];models=[]
    for p in args.candidates:
        d=parse_file(p);require(d[1]==set(range(194)),'expected dense controls0..193')
        forms=orientations(d);controls=positive_controls(d,forms)
        matches=[];attempts=0
        for c,prior in corpus:
            for root in prior[1]:
                for mirror,flip,expected in forms:
                    attempts+=1
                    if equals_root(prior,root,expected):matches.append({'action_graph_sha256':c['action_graph_sha256'],'root':root,'mirror':mirror,'bit_exchange':flip,'source':c['source']})
        cases.append({'candidate':str(p),'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'working_states':194,'terminal':d[2],
          'exact_root_orientation_comparisons':attempts,'positive_controls':controls,'matches':matches,'distinct_from_index':not matches})
        models.append((str(p),d,forms))
    pairs=[]
    for i,(name,left,forms) in enumerate(models):
        for other,right,_ in models[i+1:]:
            matches=[];attempts=0
            for root in right[1]:
                for mirror,flip,expected in forms:
                    attempts+=1
                    if equals_root(right,root,expected):matches.append({'root':root,'mirror':mirror,'bit_exchange':flip})
            pairs.append({'left':name,'right':other,'exact_root_orientation_comparisons':attempts,'matches':matches,'distinct':not matches})
    result={'commit':index['commit'],'index_sha256':hashlib.sha256(index_bytes).hexdigest(),'spanning194_classes':len(corpus),
      'nonspanning194_diagnostics_checked':len(index['nonspanning194']),'comparison':'exact full transition tuples under all roots, control renaming, reflection, bit exchange, and ignored final write/move',
      'candidates':cases,'pairwise':pairs,'all_new_and_pairwise_distinct':all(c['distinct_from_index'] for c in cases) and all(p['distinct'] for p in pairs),
      'scope':'Current explicit-table corpus only; unexecuted generators and prose-only machines excluded. No consistency theorem inferred.'}
    args.output.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
    if not result['all_new_and_pairwise_distinct']:raise SystemExit(1)

if __name__=='__main__':main()
