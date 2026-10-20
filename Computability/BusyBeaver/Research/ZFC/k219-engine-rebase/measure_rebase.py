#!/usr/bin/env python3
"""Bounded equality-source allocation on exact 219/220 and explicit hybrid engines.

This checks source/decoder binding and graph counts only. New CI entries and
hybrid return actions require separate unbounded primitive/runtime validation.
"""
from pathlib import Path
import argparse, hashlib, json, sys, time

HERE = Path(__file__).resolve().parent
BASE = HERE.parent
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def need(x, m):
    if not x: raise ValueError(m)
def dump(p,x): p.write_text(json.dumps(x,indent=2)+'\n')
def reachable(table):
    seen={0}; todo=[0]
    for q in todo:
        for bit in (0,1):
            z=table[q,bit][2]
            if z!=254 and z not in seen: seen.add(z);todo.append(z)
    return {k:v for k,v in table.items() if k[0] in seen}
def incoming(table,q):
    return [[a,bit,list(v)] for (a,bit),v in sorted(table.items()) if v[2]==q]

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--out',type=Path,required=True);a=ap.parse_args()
    need(__debug__ and not sys.flags.optimize,'Assertions must be enabled')
    need(not a.out.exists(),'Output must be fresh')
    pins=json.loads((HERE/'inputs.json').read_text())
    need(all(sha(Path(p))==h for p,h in pins.items()),'Pinned input drift')
    sys.dont_write_bytecode=True;sys.path.insert(0,str(HERE/'code'))
    import source_language as s,build221 as b,allocator
    backends={}; identities=[]
    for n in (219,220):
        p=BASE/f'candidate-k{n}'; table=b.read_table((p/f'k{n}.native.tm').read_bytes())
        tree=s.tree(json.loads((p/f'sites{n}.json').read_text()))
        for protected in (False,True):
            control,metrics=allocator.compile_tree(s,b,table,tree,tree,protected=protected)
            need(control==table and metrics['working_states']==n,('Identity failure',n,protected))
            identities.append(dict(backend=n,protected=protected,metrics=metrics))
        backends[f'native{n}']=(table,tree,[])
    base,tree,_=backends['native219']
    # These are two exact historically used K220 increment rows.
    rebase={(113,0):(0,-1,40),(198,0):(1,-1,198)}
    variants={
        '219_increment220':rebase,
        # An additional, separately unverified return substitution. Its prefix
        # still uses the K219 shared108; graph pruning alone cannot certify it.
        '219_increment220_b1generic':{**rebase,(103,1):(0,-1,40)},
    }
    for name,changes in variants.items():
        table=dict(base);table.update(changes);table=reachable(table)
        b.read_table(b.table_bytes(table));b.decoder_map(table,tree)
        backends[name]=(table,tree,[dict(state=q,bit=bit,before=list(base[q,bit]),after=list(row)) for (q,bit),row in changes.items()])
    a.out.mkdir(parents=True)
    dump(a.out/'identity-controls.json',identities)
    results=[]
    for backend,(table,old,changes) in backends.items():
        d=a.out/backend;d.mkdir();(d/'backend.native.tm').write_bytes(b.table_bytes(table))
        dump(d/'backend.json',dict(changes=changes,graph_states=len(table)//2,helper302_incoming=incoming(table,302),shared108_rows=[table.get((108,i)) for i in (0,1)],scope='Exact input or unverified explicit hybrid; decoder prefix checked.'))
        for hit in (0,1,2,3,12):
            source=BASE/f'k219-source-search/candidates/hit{hit:02}.sites.json'
            rows=json.loads(source.read_text());new=s.tree(rows)
            need(s.sites(new)==rows and s.graph_arithmetic(rows)[0]==s.graph_intervals(rows),'Source/CFG identity')
            need(not any(path.endswith('1') and op=='CD' for path,op,arg in rows),'Unexpected right decrement')
            for protected in (False,True):
                for hypothetical in (False,True):
                    name=f'hit{hit:02}-'+('protected' if protected else 'origins')+('-entry-hypothesis' if hypothetical else '-strict')
                    row=dict(backend=backend,hit=hit,protected=protected,hypothetical_entries=hypothetical,source_sha256=sha(source),source_metrics=s.metrics(new),source_changes=changes)
                    started=time.monotonic()
                    try:
                        tt,metrics=allocator.compile_tree(s,b,table,old,new,protected=protected,hypothetical_entries=hypothetical)
                        raw=b.table_bytes(tt);need(b.read_table(raw)==tt,'Raw roundtrip');need(reachable(tt)==tt,'Graph pruning')
                        (d/(name+'.tm')).write_bytes(raw)
                        row.update(status='SOURCE_DECODER_BINDING_PASS',metrics=metrics,raw_sha256=hashlib.sha256(raw).hexdigest(),helper302_incoming=incoming(tt,302),retained108=108 in {q for q,bit in tt},retained302=302 in {q for q,bit in tt})
                    except (ValueError,KeyError,AssertionError) as exc:
                        row.update(status='REJECTED',error=repr(exc))
                    row['seconds']=time.monotonic()-started
                    dump(d/(name+'.json'),row);results.append(row)
                    print(backend,name,row['status'],row.get('metrics',{}).get('working_states'),row.get('error',''),flush=True)
    need(all(sha(Path(p))==h for p,h in pins.items()),'Post-input drift')
    dump(a.out/'result.json',dict(status='BOUNDED_ENGINE_REBASE_MEASUREMENT_COMPLETE',inputs=pins,script_sha256=sha(Path(__file__)),allocator_sha256=sha(HERE/'code/allocator.py'),identity_controls=identities,results=results,scope='Allocation and exact decoder-prefix checks only. Not primitive runtime/startup, not a calibrated machine. Every non-native hybrid and added right CI entry remains separately unverified.'))
if __name__=='__main__':main()
