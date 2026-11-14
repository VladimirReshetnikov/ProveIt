#!/usr/bin/env python3
"""Independent literal/source census of the five supplied U209 packets.

Read-only inputs. Python 3.10+ standard library. Run from any directory; defaults are relative to this package.
This checks finite table/source identities, not their consistency calibration.
"""
from pathlib import Path
import argparse, collections, gzip, hashlib, itertools, json

def require(ok, message):
    if not ok:
        raise ValueError(message)

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def read_table(path):
    rows = {}
    for line in path.read_text().splitlines():
        if not line.strip() or line.startswith('#'):
            continue
        q, b, w, d, r = line.split()
        q, b, w, r = map(int, (q, b, w, r))
        require((q, b) not in rows, 'duplicate row')
        require(b in (0,1) and w in (0,1) and d in ('L','R'), 'bad row')
        rows[q,b] = (w,d,r)
    states = {q for q,b in rows}
    require(len(states) == 209 and set(rows) == set(itertools.product(states,(0,1))), 'state count')
    halts = {r for w,d,r in rows.values()} - states
    require(len(halts)==1, 'halt count')
    return rows, states, halts.pop()

def canonical(table, states, halt):
    seen, queue, rows = {0:0}, [0], []
    for q in queue:
        for b in (0,1):
            w,d,r = table[q,b]
            if r == halt:
                target = 'H'
            else:
                if r not in seen:
                    seen[r] = len(seen)
                    queue.append(r)
                target = seen[r]
            rows.append((seen[q],b,w,d,target))
    require(set(seen)==states, 'unreachable working state')
    return rows, seen

def forced_isomorphism(a,b,ha,hb):
    f, inverse, queue = {0:0,ha:hb}, {0:0,hb:ha}, [(0,'')]
    for q, path in queue:
        for bit in (0,1):
            w,d,r = a[q,bit]
            ww,dd,rr = b[f[q],bit]
            witness = path+str(bit)
            if (w,d)!=(ww,dd):
                return {'isomorphic':False,'witness':witness,'reason':'write or move differs'}
            if r in f and f[r]!=rr:
                return {'isomorphic':False,'witness':witness,'reason':'forward map conflict', 'from':r, 'required':rr,'earlier':f[r]}
            if rr in inverse and inverse[rr]!=r:
                return {'isomorphic':False,'witness':witness,'reason':'injectivity conflict','to':rr,'required':r,'earlier':inverse[rr]}
            if r not in f:
                f[r]=rr
                inverse[rr]=r
                queue.append((r,witness))
    require(len(f)==210, 'incomplete bijection')
    for (q,bit),(w,d,r) in a.items():
        require(b[f[q],bit]==(w,d,f[r]),'bijection fails row equation')
    return {'isomorphic':True,'nontrivial_native_mapping':{str(q):r for q,r in sorted(f.items())if q!=r}}

def source_graph(sites):
    addresses = [pc for pc,op,arg in sites]
    require(addresses==sorted(set(addresses)), 'source leaf order')
    lookup = dict(zip(addresses,range(len(addresses))))
    prefixes = {p[:i] for p in addresses for i in range(len(p))}
    require(not (set(addresses)&prefixes), 'source not prefix free')
    for p in prefixes:
        require(all(p+bit in prefixes or p+bit in lookup for bit in '01'), 'source not full binary')
    def decode(pc):
        for i in range(max(map(len,addresses))+1):
            p=(pc+'0'*i)[:i]
            if p in lookup:
                require(all(b=='0' for b in pc[i:]),'stray one after decoded target')
                return lookup[p]
        raise ValueError('undecodable target')
    def strip(pc,bit,count):
        if not count:
            return pc
        for i in range(len(pc)-1,-1,-1):
            if pc[i]==bit:
                count-=1
                if not count:
                    return pc[:i]
        return ''
    def inc(pc):
        n=len(pc)
        return format((int(pc or '0',2)+1) % (1<<n),f'0{n}b') if n else ''
    graph=[]
    for pc,op,arg in sites:
        if op=='CI':targets=[decode(inc(pc))]
        elif op=='CD':targets=[decode(inc(strip(pc,'0',1))),decode(inc(pc))]
        elif op=='CB':targets=[decode(inc(strip(pc,'0',arg)))]
        elif op=='CC':targets=[decode(strip(pc,'1',arg))]
        elif op=='CH':targets=[]
        else:raise ValueError(op)
        graph.append([op,arg,targets])
    return graph

def main():
    p=argparse.ArgumentParser();p.add_argument('--inputs',type=Path,default=Path(__file__).resolve().parents[1]/'comparison');p.add_argument('--output',type=Path,default=Path('comparison-recomputed.json'));args=p.parse_args()
    packets=sorted(x for x in args.inputs.iterdir() if x.is_dir() and (x/'machine/u209.native.tm').exists())
    require(len(packets)==5,'expected five code packets')
    records=[]; tables={};graphs={};sources={};halts={}
    for root in packets:
        name=root.name
        table,states,halt=read_table(root/'machine/u209.native.tm')
        can,mapping=canonical(table,states,halt)
        sites_path=root/'machine/sites.json'
        if not sites_path.exists():sites_path=root/'source/u209.sites.json'
        sites=json.loads(sites_path.read_text());graph=source_graph(sites)
        require(len(sites)==3909 and sum(len(g[2])for g in graph)==5083,'source census')
        sources[name]=sites;graphs[name]=graph;tables[name]=table;halts[name]=halt
        records.append({'package':name,'dense_sha256':sha(root/'machine/u209.tm'),'native_sha256':sha(root/'machine/u209.native.tm'),'source_sha256':sha(sites_path),
          'canonical_sha256':hashlib.sha256(json.dumps(can).encode()).hexdigest(),'working_states':len(states),'transition_rows':len(table),'graph_reachable_working_states':len(mapping),
          'source_occurrences':len(sites),'guarded_control_edges':sum(len(g[2])for g in graph),'maximum_source_depth':max(len(x[0])for x in sites),
          'maximum_source_zero_run':max(len(z)for x in sites for z in x[0].split('1'))})
    pairs=[]
    for a,b in itertools.combinations(tables,2):
        require(graphs[a]==graphs[b],'source CFG mismatch')
        pairs.append({'from':a,'to':b,'same_source_cfg':True,'changed_addresses':sum(x[0]!=y[0]for x,y in zip(sources[a],sources[b])),
          **forced_isomorphism(tables[a],tables[b],halts[a],halts[b])})
    result={'status':'FINITE_TABLE_AND_SOURCE_COMPARISON_PASS','records':records,'pairs':pairs,
      'canonical_isomorphism_classes':len({r['canonical_sha256']for r in records}),'scope':'Finite literal/source identities; no consistency or nonhalting claim.'}
    args.output.parent.mkdir(parents=True,exist_ok=True);args.output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({'status':result['status'],'isomorphism_classes':result['canonical_isomorphism_classes'],'packets':len(records),'pairwise_comparisons':len(pairs)},indent=2))
if __name__=='__main__':main()
