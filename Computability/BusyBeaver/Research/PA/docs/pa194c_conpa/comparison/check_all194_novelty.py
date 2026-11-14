#!/usr/bin/env python3
"""Check PA194C against every recognized 194-state table in the pinned census.

The tables directory contains each prior literal table as SHA256.tm. This is
a graph comparison, not a halting or consistency checker.
"""
from pathlib import Path
import argparse,hashlib,json

def sha(b):return hashlib.sha256(b).hexdigest()

def parse(b):
    rows={}
    for line in b.decode('utf8').splitlines():
        line=line.strip()
        if not line or line.startswith(('#','//',';')):continue
        q,r,w,d,t=line.split();q,r,w,t=map(int,(q,r,w,t))
        assert (q,r) not in rows and r in (0,1) and w in (0,1) and d in ('L','R')
        rows[q,r]=(w,d,t)
    states={q for q,r in rows}
    assert len(states)==194 and set(rows)=={(q,r) for q in states for r in (0,1)}
    halts={t for w,d,t in rows.values()}-states
    assert len(halts)==1
    return rows,states,next(iter(halts))

def canonical(rows,states,halt,reflect=False):
    best=None;roots=0
    for root in sorted(states):
        labels={root:0};todo=[root];ans=[]
        for q in todo:
            rr=[]
            for bit in (0,1):
                w,d,t=rows[q,bit]
                if reflect:d='L' if d=='R' else 'R'
                if t==halt:k=-1
                else:
                    if t not in labels:labels[t]=len(todo);todo.append(t)
                    k=labels[t]
                rr.append([w,d,k])
            ans.append(rr)
        if len(todo)!=len(states):continue
        roots+=1
        encoded=json.dumps(ans,separators=(',',':')).encode()
        if best is None or encoded<best:best=encoded
    assert best is not None
    return sha(best),roots

def main():
    assert __debug__,'Run without Python -O.'
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--census',required=True,type=Path)
    ap.add_argument('--tables',required=True,type=Path)
    ap.add_argument('--candidate',required=True,type=Path)
    ap.add_argument('--output',type=Path)
    args=ap.parse_args()
    census=json.loads(args.census.read_text())
    commit=census['summary']['commit']
    assert commit=='768c2be1a8e4d2fcf8aa3443c7b0f084d145734c'
    seen=set();catalog=[]
    for rec in census['tables']:
        if rec['states']!=194 or rec['sha256'] in seen:continue
        h=rec['sha256'];data=(args.tables/(h+'.tm')).read_bytes()
        assert sha(data)==h
        rows,states,halt=parse(data)
        g,n=canonical(rows,states,halt)
        reflected,_=canonical(rows,states,halt,True)
        seen.add(h)
        catalog.append(dict(rec,graph_sha256=g,reflected_graph_sha256=reflected,
                            full_reaching_roots=n))
    candidate=args.candidate.read_bytes()
    assert sha(candidate) in {
      'b35d80b01ce9c2e95c8b29222881f40928247cdeffac322e4643f4f6694cd33c',
      'd759313c03b515293fe06b12769fa1771d3829a2bad89febaa9b4391990f3a4b'}
    g,n=canonical(*parse(candidate))
    assert g=='b79f4d344740679b87dace02fe3f211565c2cd4513f346812570d90caa3d9a3f'
    assert len(catalog)==7
    assert all(g not in (r['graph_sha256'],r['reflected_graph_sha256']) for r in catalog)
    result={'commit':commit,
      'scope':'Every complete numeric 194-state .tm/.txt table recognized in all 36 top-level ZIPs recursively and all 14 direct PA .tm files; includes the rejected scanner table.',
      'prior194_occurrences':sum(r['states']==194 for r in census['tables']),
      'prior194_byte_forms':len(catalog),
      'prior194_graph_classes':len({r['graph_sha256'] for r in catalog}),
      'new_graph_sha256':g,
      'new194C_absent_even_after_control_relabeling_root_change_and_reflection':True,
      'prior194_tables':catalog}
    output=json.dumps(result,indent=2)+'\n'
    if args.output:args.output.write_text(output)
    print(output)

if __name__=='__main__':main()
