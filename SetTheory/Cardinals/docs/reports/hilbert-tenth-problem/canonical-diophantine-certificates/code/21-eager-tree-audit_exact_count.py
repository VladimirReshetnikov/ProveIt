#!/usr/bin/env python3
"""Independent structural audit, never writes to the frozen packet.
Direct evaluation uses only literal L/S/F nodes and the five Jay rules.
All operations are on exact hash-consed constructor trees, not hashes.
"""
import argparse
import hashlib
import importlib.util
import json
import sys
sys.dont_write_bytecode = True
from pathlib import Path

HERE = Path(__file__).resolve().parent
PACKET = HERE

class Trees:
    def __init__(self):
        self.nodes=[]; self.ids={}
    def make(self,tag,*children):
        t=(tag,*children)
        if t not in self.ids:
            self.ids[t]=len(self.nodes); self.nodes.append(t)
        return self.ids[t]
    def load(self,rows,x=None):
        ids=[]
        for r in rows:
            ids.append(x if r[0]=='X' else self.make(r[0],*(ids[j] for j in r[1:])))
        return ids

class ExactEval:
    def __init__(self,t): self.t=t; self.rows={}
    def app(self,x,y):
        root=(x,y); pending=[root]; active={root}
        def need(k):
            if k in self.rows: return False
            assert k not in active, ('cycle',k)
            active.add(k); pending.append(k); return True
        while pending:
            key=pending[-1]; x,y=key; tx=self.t.nodes[x]; ps=[]
            if tx[0]=='L': z=self.t.make('S',y)
            elif tx[0]=='S': z=self.t.make('F',tx[1],y)
            else:
                assert tx[0]=='F'
                left,right=tx[1:]; tl=self.t.nodes[left]
                if tl[0]=='L': z=right
                elif tl[0]=='S':
                    p=(right,y)
                    if need(p): continue
                    q=(tl[1],y)
                    if need(q): continue
                    r=(self.rows[p][0],self.rows[q][0])
                    if need(r): continue
                    z=self.rows[r][0]; ps=[p,q,r]
                else:
                    assert tl[0]=='F'
                    p=(y,tl[1])
                    if need(p): continue
                    q=(self.rows[p][0],tl[2])
                    if need(q): continue
                    z=self.rows[q][0]; ps=[p,q]
            self.rows[key]=(z,1+sum(self.rows[p][1] for p in ps),tuple(ps))
            pending.pop(); active.remove(key)
        return self.rows[root][0]

def load_module(name,path):
    spec=importlib.util.spec_from_file_location(name,path)
    mod=importlib.util.module_from_spec(spec);spec.loader.exec_module(mod);return mod

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--packet',type=Path,default=PACKET,help='directory containing the two frozen JSON inputs')
    args=parser.parse_args()
    sp=args.packet/'shared_symbolic_proofs.json';lp=args.packet/'shared_compression_program.json'
    s=json.loads(sp.read_text());literal=json.loads(lp.read_text()); cs={c['name']:c['rows'] for c in s['cases']}
    reach={}
    for name,rs in cs.items():
        todo=[0]; seen=set()
        while todo:
            i=todo.pop()
            if i in seen:continue
            seen.add(i);todo.extend(rs[i]['premises'])
        assert seen==set(range(len(rs)))
        assert len(set((r['x'],r['y']) for r in rs))==len(rs)
        reach[name]={'rows':len(rs),'reachable':len(seen),'oracle_indices':[i for i,r in enumerate(rs) if r['oracle']]}
    verified=load_module('audit_packet_assumptions',HERE/'verify_packet_assumptions.py').verify(args.packet)
    a=load_module('audit_subject_analysis',HERE/'analyze_growth.py').Analysis(s)
    actual=a.analyze(); receipt=json.loads((HERE/'exact_growth_receipt.json').read_text())
    for k,v in actual.items():
        assert json.loads(json.dumps(v))==receipt[k], ('receipt mismatch',k)
    assert receipt['source_sha256']==hashlib.sha256(sp.read_bytes()).hexdigest()
    t=Trees(); original=t.load(literal['nodes']); R=original[literal['root']]; L=t.make('L'); I=t.make('F',t.make('S',L),t.make('S',L))
    defs=t.load(s['nodes'],L)
    assert defs[s['names']['R']]==R and defs[s['names']['I']]==I
    base1={(defs[r['x']],defs[r['y']]):(defs[r['z']],r['cost'][1],tuple((defs[cs['base1'][p]['x']],defs[cs['base1'][p]['y']]) for p in r['premises'])) for r in cs['base1']}
    assert len(base1)==179
    union=set(base1); unary=[L]
    for n in range(1,257): unary.append(t.make('S',unary[-1]))
    checks=[]
    checkpoints=set(range(65))|{96,128,192,256}
    for n in range(257):
        if n>=2:
            inst=t.load(s['nodes'],unary[n-2])
            union.update((inst[r['x']],inst[r['y']]) for r in cs['step'] if not r['oracle'])
            assert len(union)==64*n+113,(n,len(union))
        if n not in checkpoints: continue
        e=ExactEval(t); z=e.app(R,unary[n]); assert z==I
        h=e.rows[(R,unary[n])][1]
        assert h==562*2**n-468
        expected=44 if n==0 else 179 if n==1 else 64*n+113
        assert len(e.rows)==expected,(n,len(e.rows),expected)
        if n: assert set(e.rows)==union
        if n==1: assert e.rows==base1
        checks.append({'n':n,'canonical_rows':len(e.rows),'union_rows':None if n==0 else len(union),'unfolded_calls':h})
    result={'status':'pass','symbolic_sha256':hashlib.sha256(sp.read_bytes()).hexdigest(),'literal_sha256':hashlib.sha256(lp.read_bytes()).hexdigest(),'reachability':reach,'packet_assumptions_verifier_status':verified['status'],'receipt_recomputed':True,'all_union_cardinalities_checked_through_n':256,'direct_evaluation_checks':checks,'tree_representation':'exact interned constructor tuples, with no structural-hash approximation','generality':'Fixed literal R, unary inputs S^n(L), unique terminating eager derivation, maximal sharing by exact application input pairs. Count excludes constructor storage and administrative/oracle-placeholder vertices.'}
    (HERE/'audit_exact_count_receipt.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({'status':result['status'],'reachability':reach,'direct_evaluation_n':[c['n'] for c in checks],'max_checked_rows':checks[-1]['canonical_rows'],'all_union_cardinalities_checked_through_n':256},indent=2))

if __name__=='__main__':main()
