#!/usr/bin/env python3
"""Offline audit replay: 10,036 blank starts and exact graph novelty.

Only Python's standard library and the files bundled beside this script are
needed. No Git checkout, network, symbolic runtime, or proof assistant is used.
The logical coefficient-three counterexample is attributed, not replayed here.
"""
from pathlib import Path
from collections import Counter
import argparse, csv, hashlib, json, time

BASE=Path(__file__).resolve().parent
CANDIDATE_SHA256='9933fe380b5242981255a0b75da6b305fc88df7031e753411a51efaf7dbe0dab'

def sha(raw):return hashlib.sha256(raw).hexdigest()

def parse(raw):
    rows={}
    for line in raw.decode('ascii').splitlines():
        s=line.strip()
        if not s or s.startswith(('#','//',';')):continue
        parts=s.split();assert len(parts)==5,s
        q,b,w,d,t=parts;q,b,w,t=map(int,(q,b,w,t))
        assert q>=0 and t>=0 and b in (0,1) and w in (0,1) and d in ('L','R')
        assert (q,b) not in rows
        rows[q,b]=(w,d,t)
    states={q for q,b in rows}
    assert states and set(rows)=={(q,b) for q in states for b in (0,1)}
    halts={t for w,d,t in rows.values()}-states;assert len(halts)==1
    return rows,states,next(iter(halts))

def canonical(data,cosmetic=False):
    """Return an exact tuple, minimizing over every spanning initial root.

    The optional cosmetic mode also permits reflection, bit complement and
    arbitrary final write/move. Prefix pruning discards a root only when its
    already computed tuple prefix exceeds the best complete tuple.
    """
    rows,states,halt=data;best=None;witness=None
    symmetries=((False,False),(True,False),(False,True),(True,True)) if cosmetic else ((False,False),)
    for reflect,complement in symmetries:
        for root in sorted(states):
            labels={root:0};todo=[root];out=[];relation=0;pruned=False
            for q in todo:
                pair=[]
                for b in (0,1):
                    w,d,t=rows[q,b^complement]
                    if t==halt:
                        pair.append((0,'R',-1) if cosmetic else (w,d,-1))
                    else:
                        if t not in labels:labels[t]=len(todo);todo.append(t)
                        pair.append((w^complement,('R' if d=='L' else 'L') if reflect else d,labels[t]))
                row=tuple(pair);i=len(out);out.append(row)
                if best is not None and relation==0:
                    if row>best[i]:pruned=True;break
                    if row<best[i]:relation=-1
            if pruned or len(todo)!=len(states):continue
            result=tuple(out)
            if best is None or result<best:best=result;witness=(root,reflect,complement)
    assert best is not None,'Table has no spanning root.'
    return best,witness

def run(data,start,bound=200000):
    rows,states,halt=data;q=start;h=0;ones=set();exact={};blanks={}
    for k in range(bound+1):
        if q==halt:return dict(status='HALT',steps=k,state=q,head=h,ones=sorted(ones))
        if not ones and q in blanks:
            previous,old_h=blanks[q]
            return dict(status='BLANK_TRANSLATION_CYCLE',steps=k,state=q,head=h,first_step=previous,translation=h-old_h)
        if not ones:blanks[q]=(k,h)
        key=(q,h,tuple(sorted(ones)))
        if key in exact:return dict(status='EXACT_LOOP',steps=k,state=q,head=h,first_step=exact[key])
        exact[key]=k
        b=int(h in ones);w,d,t=rows[q,b]
        if b==0 and t==q and (not ones or (d=='R' and h>max(ones)) or (d=='L' and h<min(ones))):
            return dict(status='OUTWARD_RAY',steps=k,state=q,head=h,ones=sorted(ones),direction=d,written=w)
        if k==bound:return dict(status='OPEN',steps=k,state=q,head=h,one_count=len(ones))
        if w:ones.add(h)
        else:ones.discard(h)
        q=t;h+=1 if d=='R' else -1
    raise AssertionError

def main():
    if not __debug__:raise SystemExit('Do not use Python -O: assertions are verification checks.')
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--candidate',type=Path,default=BASE/'candidate.tm')
    ap.add_argument('--receipt',type=Path)
    args=ap.parse_args();begin=time.monotonic()
    tables=BASE/'current_census/frontier_tables'
    corpus=json.loads((BASE/'current_census/summary.json').read_text())
    assert corpus['snapshot']=='4be5c6e3a10292a7466f5d3687e3b39615ff049b'
    ledger193=list(csv.DictReader((BASE/'frontier193_current.csv').open()))
    assert len(ledger193)==53
    tuples193=set();counts=Counter();replayed=0;logical=0;maximum=0
    for item in ledger193:
        g=item['graph_class_sha256'];raw=(tables/(g+'.tm')).read_bytes();data=parse(raw)
        assert len(data[1])==193
        exact,_=canonical(data)
        assert sha(repr(exact).encode())==g
        assert exact not in tuples193;tuples193.add(exact)
        frozen=json.loads((BASE/item['certificate']).read_text())
        assert sha(raw)==frozen['table_sha256']
        if item['status']=='logical rejection':
            logical+=1;assert not frozen['starts'];continue
        fresh=[dict(start=s,**run(data,s)) for s in sorted(data[1])]
        assert fresh==frozen['starts'],g
        local=Counter(r['status'] for r in fresh)
        assert dict(local)==frozen['counts'] and not local['OPEN']
        counts.update(local);maximum=max(maximum,max(r['steps'] for r in fresh));replayed+=1
    assert logical==1 and replayed==52
    assert counts=={'HALT':106,'OUTWARD_RAY':9930} and maximum==117
    print('Blank starts: PASS; 52 physical classes, 10036 starts, 106 halts, 9930 certified outward rays, no OPEN cases.',flush=True)

    raw=args.candidate.read_bytes();assert sha(raw)==CANDIDATE_SHA256
    candidate=parse(raw)
    assert candidate[1]==set(range(194)) and candidate[2]==194 and len(candidate[0])==388
    cand,witness=canonical(candidate,True)
    frontier=list(csv.DictReader((BASE/'frontier194_current.csv').open()))
    assert len(frontier)==82
    tuples194=set();cosmetic_classes=set();matches=[]
    for item in frontier:
        g=item['graph_class_sha256'];data=parse((tables/(g+'.tm')).read_bytes())
        assert len(data[1])==194
        exact,_=canonical(data)
        assert sha(repr(exact).encode())==g
        assert exact not in tuples194;tuples194.add(exact)
        other,_=canonical(data,True);cosmetic_classes.add(other)
        if other==cand:matches.append(g)
    assert not matches
    old=json.loads((BASE/'ax11q6_novelty.json').read_text())
    assert old['candidate_sha256']==CANDIDATE_SHA256
    assert old['candidate_cosmetic_fingerprint']==sha(repr(cand).encode())
    assert old['compared_classes']==82 and not old['matches']
    print('Exact novelty: PASS; complete canonical tuples compared against all 82 historical 194-state classes.',flush=True)
    receipt={'status':'PASS','snapshot':corpus['snapshot'],
      'blank_starts':{'physical_classes':replayed,'initial_states':sum(counts.values()),'outcomes':dict(counts),'open':0,'maximum_steps_to_certificate':maximum,'comparison':'Exact complete per-start records, not digest-only.'},
      'coefficient_three':{'classes':logical,'scope':'Historical logical refutation attributed; not replayed by this script.'},
      'candidate':{'sha256':CANDIDATE_SHA256,'working_states':194,'rows':388,'start':0,'halt':194},
      'novelty':{'comparison':'Exact full canonical tuple equality. Hashes identify files and bind provenance only.','historical_classes':82,'cosmetic_historical_classes':len(cosmetic_classes),'matches':matches,'candidate_witness':witness,'transformations':['all spanning roots','arbitrary state renaming','reflection','global bit complement','arbitrary terminal write/move']},
      'limits':'Fixed supplied tables only. No general state lower bound and no inference of divergence from a fuel cutoff.',
      'elapsed_seconds':round(time.monotonic()-begin,3)}
    if args.receipt:
        args.receipt.parent.mkdir(parents=True,exist_ok=True)
        args.receipt.write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps(receipt,indent=2))

if __name__=='__main__':main()
