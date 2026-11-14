#!/usr/bin/env python3
"""Independent blank-run certificate replay for the current 193-state corpus.

A certified outward self-loop or exact/blank translational cycle proves
its infinite continuation. A fuel bound is reported OPEN and proves none.
The coefficient-three calculus counterexample is attributed separately.
"""
from pathlib import Path
from collections import Counter
import csv, hashlib, json, re, sys
BASE=Path(__file__).resolve().parent
sys.path.insert(0,str(BASE/'scanner'))
from literal_inventory import parse_table

def run(data,start,bound=200000):
    rows,states,halt=data
    q=start; h=0; ones=set(); exact={}; blanks={}
    for k in range(bound+1):
        if q==halt:
            return {'status':'HALT','steps':k,'state':q,'head':h,'ones':sorted(ones)}
        if not ones and q in blanks:
            previous,old_h=blanks[q]
            return {'status':'BLANK_TRANSLATION_CYCLE','steps':k,'state':q,'head':h,'first_step':previous,'translation':h-old_h}
        if not ones:blanks[q]=(k,h)
        key=(q,h,tuple(sorted(ones)))
        if key in exact:
            return {'status':'EXACT_LOOP','steps':k,'state':q,'head':h,'first_step':exact[key]}
        exact[key]=k
        b=int(h in ones);w,d,t=rows[q,b]
        if b==0 and t==q and (not ones or (d=='R' and h>max(ones)) or (d=='L' and h<min(ones))):
            return {'status':'OUTWARD_RAY','steps':k,'state':q,'head':h,'ones':sorted(ones),'direction':d,'written':w}
        if k==bound:
            return {'status':'OPEN','steps':k,'state':q,'head':h,'one_count':len(ones)}
        if w:ones.add(h)
        else:ones.discard(h)
        q=t;h+=1 if d=='R' else -1
    raise AssertionError

def main():
    census=json.loads((BASE/'current_census/census.json').read_text())
    groups=[g for g in census['classes'] if g['states']==193]
    assert len(groups)==53
    variants={r['name']:r for r in json.loads((BASE/'variant193_manifest.json').read_text())}
    out=BASE/'rejections193';out.mkdir(exist_ok=True)
    ledger=[];totals=Counter()
    for g in groups:
        gh=g['graph_hash'];sources=sorted({o['path'] for o in g['occurrences']})
        p=BASE/'current_census/frontier_tables'/(gh+'.tm');raw=p.read_bytes();data=parse_table(raw)
        assert data and len(data[1])==193
        vnames=sorted({m.group(1) for s in sources if (m:=re.search(r'/variant193/(variant\d+)\.tm$',s))})
        old_sources=' | '.join(variants[v]['source'] for v in vnames)
        if any('/search/rejected193/' in s for s in sources):
            name='Coefficient-three rejected calculus'
            role='logical rejection'
            evidence='Inherited primitive refutation of code one from the coefficient-three unchanged-head calculus; no blank-run claim inferred from a bound.'
            receipt={'scope':'Logical rejection attributed to source packet; primitive proof not rerun by this blank-run checker.','starts':[]}
            counts=Counter()
        else:
            if any('ax11_runtime193.native.tm' in s for s in sources):name='AX11 runtime193 composition'
            elif any('relay193.native.tm' in s for s in sources):name='ZFC-style marker relay193'
            elif any('qn6_runtime193.native.tm' in s for s in sources):name='QN6 runtime193 quotient'
            elif 'variant025' in vnames:name='Append-zero runtime193 (variant025)'
            elif 'variant041' in vnames:name='Original runtime193 (variant041)'
            else:name=', '.join(vnames) or 'Other runtime193 research table'
            records=[dict(start=s,**run(data,s)) for s in sorted(data[1])]
            counts=Counter(r['status'] for r in records);totals.update(counts)
            role='blank starts rejected by finite certificates' if not counts['OPEN'] else 'partly unresolved blank-start experiments'
            evidence='Fresh independent deterministic replay from every working control on all-zero tape; statuses and complete final ray supports are in the JSON certificate.'
            receipt={'scope':'Every one of 193 controls as blank initial state; head zero. OUTWARD_RAY and cycle statuses certify continuation; OPEN means unresolved beyond 200000 steps.','starts':records}
        receipt.update(graph_class_sha256=gh,table_sha256=hashlib.sha256(raw).hexdigest(),table=str(p.relative_to(BASE)),counts=dict(counts),source_locators=sources)
        (out/(gh+'.json')).write_text(json.dumps(receipt,indent=2)+'\n')
        ledger.append({'graph_class_sha256':gh,'working_states':193,'name':name,'status':role,'original_variant_sources':old_sources,'halts':counts.get('HALT',0),'outward_rays':counts.get('OUTWARD_RAY',0),'exact_loops':counts.get('EXACT_LOOP',0),'blank_translation_cycles':counts.get('BLANK_TRANSLATION_CYCLE',0),'open_at_bound':counts.get('OPEN',0),'fresh_replay_max_steps':max((r['steps'] for r in receipt['starts']),default=0),'evidence':evidence,'source_locators':' | '.join(sources),'certificate':'rejections193/'+gh+'.json'})
        print(name,dict(counts),flush=True)
    with (BASE/'frontier193_current.csv').open('w',newline='') as f:
        w=csv.DictWriter(f,fieldnames=list(ledger[0]));w.writeheader();w.writerows(ledger)
    (BASE/'frontier193_current.json').write_text(json.dumps(ledger,indent=2)+'\n')
    summary={'snapshot':census['summary']['snapshot'],'classes':len(ledger),'logical_rejection_classes':1,'physical_classes_replayed':52,'blank_initial_states_tested':sum(totals.values()),'fresh_replay_totals':dict(totals),'unresolved_bounded_runs':totals['OPEN'],'max_steps_to_certificate':max(r['fresh_replay_max_steps'] for r in ledger),'limitations':'Only the fixed supplied tables and blank starts are covered. This is not a bound on possible repairs, other encodings, or all consistency machines. Logical rejection is attributed rather than freshly replayed.'}
    (BASE/'rejections193_summary.json').write_text(json.dumps(summary,indent=2)+'\n')
    print(json.dumps(summary,indent=2))

if __name__=='__main__':main()
