#!/usr/bin/env python3
"""One-step global reassociations with explicit finite control-flow repair.

The closedness restriction from source27 is deliberately removed. Every
decrement still has to implement its original two successor leaves. Control
leaves can be retargeted only with existing break/continue instruction kinds;
the independent full leaf-graph checker is the semantic acceptance gate.
"""
import argparse,json,sys,time
from collections import Counter
from pathlib import Path
import search246 as s
import rotate_search as r
from plateau_search import metrics
HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE.parent/'proof'))
from leaf_cfg import Program,check_map,increment,strip

def options(nodes):
    for n,(x,y) in nodes.items():
        if x[0]=='N':
            a,b=nodes[x[1]]
            yield n,('T',a,('T',b,y)),'right'
        if y[0]=='N':
            a,b=nodes[y[1]]
            yield n,('T',('T',x,a),b),'left'

def intern_sites(ss):
    trie={}
    for pc,op,arg in ss:
        p=trie
        for b in pc:p=p.setdefault(b,{})
        p['e']=(op[1:],) if op=='CH' else (op[1:],arg)
    nodes={};seen={}
    def rec(t):
        if 'e' in t:return t['e']
        pair=rec(t['0']),rec(t['1'])
        if pair not in seen:seen[pair]=len(nodes);nodes[seen[pair]]=pair
        return 'N',seen[pair]
    return nodes,rec(trie)[1]

def repair(src,nn,nr):
    ss=s.sites(nn,nr);dst=Program(ss)
    mapping=dict(zip(sorted(src.by_address),sorted(dst.by_address)))
    inverse={v:k for k,v in mapping.items()}
    edits=[];fixed=[]
    for pc,op,arg in ss:
        old=inverse[pc]
        expected={g:mapping[t] for g,t in src.successors(old).items()}
        if op not in ('CB','CC'):
            if dst.successors(pc)!=expected:return None,dict(outcome='arithmetic_successor',pc=pc,source=old,op=op)
            fixed.append((pc,op,arg));continue
        if dst.successors(pc)==expected:
            fixed.append((pc,op,arg));continue
        target=expected['always'];choices=[]
        for edge,bit in s.CONTROL_OPTIONS:
            if bit!=int(pc[-1]):continue
            typ,k=edge
            after=increment(strip(pc,'0',k)) if typ=='B' else strip(pc,'1',k)
            if dst.decode(after)==target:
                # Prefer unchanged opcode, then smallest operand.
                choices.append((typ!=op[1:],k,typ))
        if not choices:return None,dict(outcome='no_control_encoding',pc=pc,source=old)
        _,k,typ=min(choices)
        fixed.append((pc,'C'+typ,k));edits.append([pc,op,arg,'C'+typ,k])
    dst=Program(fixed);cert=check_map(src,dst,mapping)
    assert cert['status']=='PASS',cert['failures'][:2]
    nn,nr=intern_sites(fixed)
    return (nn,nr,fixed,cert,edits),None

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--output',type=Path,default=HERE/'control-rotations');a=ap.parse_args();a.output.mkdir(exist_ok=True)
    src=Program(s.sites(s.NODES,s.ROOT));hist=Counter();results=[];t=time.monotonic()
    for i,(n,e,k) in enumerate(options(s.NODES)):
        nn,nr=r.mutate(s.NODES,s.ROOT,n,e)
        repaired,fail=repair(src,nn,nr)
        record=dict(index=i,node=n,kind=k)
        if fail:record.update(fail)
        else:
            nn,nr,ss,cert,edits=repaired
            try:
                graph,cost=metrics(nn,nr)
                record.update(outcome='CFG_PASS',graph_states=graph,charged_states=cost,node_count=len(nn),control_edit_count=len(edits),zero_metrics=r.zero_metrics(nn,nr))
                if cost<=246:
                    out=s.evaluate(nn,nr)
                    record.update(affine_status=out['outcome'],runtime_states=out.get('runtime_states'))
                    data=dict(root=nr,nodes=nn,sites=ss,graph_certificate=cert,control_edits=edits,**record)
                    (a.output/f'candidate{i}.json').write_text(json.dumps(data,indent=2)+'\n')
                    if out['outcome']=='PASS':
                        (a.output/f'candidate{i}.tm').write_text('#! start 95\n'+''.join(f'{q} {b} {w} {d} {t}\n' for (q,b),(w,d,t) in sorted(out['table'].items(),key=lambda x:(int(x[0][0]),x[0][1]))))
                print('CFG',i,k,graph,cost,'edits',len(edits),flush=True)
            except (KeyError,IndexError) as ex:record.update(outcome='unsupported_emitter',error=str(ex))
        hist[record['outcome']]+=1;results.append(record)
        if (i+1)%20==0:print('progress',i+1,dict(hist),round(time.monotonic()-t,2),flush=True)
    summary=dict(scope='All one-step global binary reassociations of the baseline, with deterministic existing-control retargeting and exact leaf-graph validation.',counts=hist,proposals=len(results),seconds=time.monotonic()-t,results=results)
    (a.output/'results.json').write_text(json.dumps(summary,indent=2)+'\n');print(dict(hist),flush=True)

if __name__=='__main__':main()
