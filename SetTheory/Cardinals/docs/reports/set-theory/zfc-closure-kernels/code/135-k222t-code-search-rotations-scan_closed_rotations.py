#!/usr/bin/env python3
"""Reproduce the finite single-rotation screen on the exposed seed-G222 layout.

This is a bounded search-family census, not a lower bound on Turing machines.
Accepted decoder checks do not replace full unbounded instruction-runtime checks.
"""
from pathlib import Path
from collections import Counter
import argparse,hashlib,json,sys

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--support-dir',type=Path,required=True)
    ap.add_argument('--source',type=Path,required=True)
    ap.add_argument('--table',type=Path,required=True)
    ap.add_argument('--output',type=Path,required=True)
    a=ap.parse_args();sys.path.insert(0,str(a.support_dir.resolve()))
    import source_language as s
    import tm_tools as tm
    assert __debug__ and not sys.flags.optimize
    old=tm.read_table(a.table.read_bytes());src=s.tree(json.loads(a.source.read_text()))
    groups,_=tm.decoder_map(old,src)
    oldmap={node:q for q,alts in groups.items() for node in alts}
    paths={}
    def visit(n,p=''):
        if s.leaf(n) or n in paths:return
        paths[n]=p;visit(n[0],p+'0');visit(n[1],p+'1')
    visit(src)
    def nodes(n):
        found=set()
        def rec(x):
            if s.leaf(x) or x in found:return
            found.add(x);rec(x[0]);rec(x[1])
        rec(n);return found
    def compile(final,origins):
        live=nodes(final);origins={n:o for n,o in origins.items() if o not in live}
        table=old.copy();mapped=oldmap.copy();mapped[final]=84
        fresh=max(300,max(q for q,b in old)+1);claimed={84:final}
        def rec(n):
            nonlocal fresh
            if n in mapped:return mapped[n]
            if n in origins and origins[n] in oldmap and len(groups[oldmap[origins[n]]])==1 and oldmap[origins[n]] not in claimed:
                q=oldmap[origins[n]]
            else:q=fresh;fresh+=1
            mapped[n]=q;claimed[q]=n
            for bit,ch in enumerate(n):
                if not s.leaf(ch):table[q,bit]=bit,1,rec(ch);continue
                if n in origins and origins[n] in oldmap and origins[n][bit]==ch:
                    table[q,bit]=old[oldmap[origins[n]],bit];continue
                choices=Counter(old[q0,bit] for n0,q0 in oldmap.items() if n0[bit]==ch)
                direct=[act for act,count in choices.items() if act[:2]==(bit,1)]
                if len(direct)==1:table[q,bit]=direct[0]
                elif ch==('CC',1) and bit==1:table[q,bit]=0,-1,1
                elif ch==('CC',2) and bit==1:table[q,bit]=0,-1,16
                elif ch==('CB',1) and bit==1:table[q,bit]=0,-1,40
                else:raise ValueError('No inherited primitive entry')
            return q
        for bit,ch in enumerate(final):table[84,bit]=bit,1,rec(ch)
        reached={0};pending=[0]
        for q in pending:
            for bit in(0,1):
                z=table[q,bit][2]
                if z!=254 and z not in reached:reached.add(z);pending.append(z)
        table={key:row for key,row in table.items() if key[0] in reached}
        actual,_=tm.decoder_map(table,final)
        for q,alts in actual.items():
            if any(mapped[n]!=q for n in alts):raise ValueError('Unintended decoder role')
        return len(reached)
    stats=Counter();records=[]
    for n,path in paths.items():
        for side in('right','left'):
            if side=='right':
                if s.leaf(n[0]):continue
                x,y=n[0];z=n[1];replacement=x,(y,z)
            else:
                if s.leaf(n[1]):continue
                x=n[0];y,z=n[1];replacement=(x,y),z
            if not all(s.boundary(v)==(0,0,False) for v in(x,y,z)):continue
            origins={}
            def rotate(v):
                if v==n:origins[replacement]=v;return replacement
                if s.leaf(v):return v
                result=rotate(v[0]),rotate(v[1])
                if result!=v:origins[result]=v
                return result
            final=rotate(src);metrics=s.metrics(final)
            stats[metrics['dag_nodes'],metrics['maximum_zero_run']]+=1
            record=dict(path=path,direction=side,metrics=metrics)
            if metrics['dag_nodes']>208 or metrics['maximum_zero_run']>6:
                record['result']='SOURCE_BUDGET_FILTER'
            else:
                try:
                    count=compile(final,origins)
                    record.update(result='DECODER_PASS',states=count)
                except (AssertionError,ValueError,KeyError) as error:
                    record.update(result='DECODER_REJECT',reason=str(error))
            records.append(record)
    digest=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
    receipt=dict(status='FINITE_SINGLE_CLOSED_ROTATION_SCREEN',source_sha256=digest(a.source),table_sha256=digest(a.table),
        rotations=len(records),source_metric_census=[dict(dag_nodes=d,zero_run=z,count=count)for(d,z),count in sorted(stats.items())],
        decoder_passes=sum(r['result']=='DECODER_PASS'for r in records),
        best_decoder_state_count=min((r['states']for r in records if'states'in r),default=None),records=records,
        scope='One global associativity rotation of each distinct subtree, only when all three factors are closed. Compile only DAG<=208 and zero-run<=6 using inherited origin allocation; check exact finite decoder roles. No full-runtime rerun of these exploratory layouts and no unrestricted lower bound.')
    a.output.parent.mkdir(parents=True,exist_ok=True);a.output.write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps({k:v for k,v in receipt.items()if k not in('records',)},indent=2))

if __name__=='__main__':main()
