#!/usr/bin/env python3
"""Reify the exact source/DAG decoder trees without duplicating shared subtrees."""
import json,re
from pathlib import Path
if not __debug__:
    raise SystemExit('Run this generator without Python -O; its validation uses assertions.')

BASE=Path(__file__).resolve().parent
OUT=BASE/'normalized_lean'
NS='SetTheory.BusyBeaver.ZFC.KSource215'

def main():
    original=(BASE/'upstream/KSource215Data.lean').read_text()
    raw=original[original.index('def p215Nodes'):original.index('def p215 :')]
    source={int(m[1]):[(op,int(v) if v else None) for op,v in re.findall(r'\.(\w+)(?: (\d+))?',m[2])]
            for line in raw.splitlines() if (m:=re.match(r'\s*\| (\d+) => (.*)',line))}
    assert len(source)==179
    trans={'N':'node','EInc':'inc','EDecnz':'decnz','EBreak':'brk','EContinue':'cont','EHalt':'halt'}
    dag={int(n):[(trans[a],b) for a,b in es] for n,es in json.loads((BASE/'upstream/dagperm_nodes.json').read_text())['nodes'].items()}
    header='import BusyBeaver.ZFC.KSource215Programs\n\nnamespace '+NS+'\n\nopen RegisterPath RMBisim\nset_option maxRecDepth 65536\nset_option maxHeartbeats 8000000\n\n'
    body=header
    stats={}
    for tag,nodes,root,p in [('s',source,178,'p215'),('d',dag,0,'pathDagPerm')]:
        order=[];heights={};visiting=set()
        def visit(n):
            if n in heights:return heights[n]
            assert n not in visiting;visiting.add(n)
            hs=[visit(v) if op=='node' else 0 for op,v in nodes[n]]
            visiting.remove(n);heights[n]=1+max(hs);order.append(n);return heights[n]
        visit(root)
        def tr(e):
            op,v=e
            return f'{tag}Tree{v}' if op=='node' else f'(.leaf (.{op}'+('' if v is None else f' {v}')+'))'
        def lhs(e):
            op,v=e
            return f'(toTree {p} f {v})' if op=='node' else tr(e)
        for n in order:
            a,b=nodes[n]
            body+=f'def {tag}Tree{n} : Tree := .node {tr(a)} {tr(b)}\n\n'
            body+=f'theorem {tag}Tree{n}_eq (f : Nat) (hf : {heights[n]} ≤ f) :\n    toTree {p} f {n} = {tag}Tree{n} := by\n  cases f with\n  | zero => omega\n  | succ f =>\n    rw [toTree_succ]\n'
            body+=f'    change Tree.node {lhs(a)} {lhs(b)} = Tree.node {tr(a)} {tr(b)}\n'
            ns=list(dict.fromkeys(v for op,v in nodes[n] if op=='node'))
            if ns:body+='    simp only ['+', '.join(f'{tag}Tree{v}_eq f (by omega)' for v in ns)+']\n\n'
            else:body+='    rfl\n\n'
        stats[tag]={'reachable_dag_nodes':len(order),'height':heights[root]}
    body+='def t215 : Tree := sTree178\ndef tD : Tree := dTree0\n\n'
    body+='theorem t215_eq : ptree p215 = t215 := sTree178_eq 180 (by decide)\n'
    body+='theorem tD_eq : ptree pathDagPerm = tD := dTree0_eq 488 (by decide)\n\n'
    body+='#print axioms t215_eq\n#print axioms tD_eq\n\nend '+NS+'\n'
    (OUT/'KSource215Data.lean').write_text(body)
    stats['bytes']=len(body.encode())
    (BASE/'shared_tree_summary.json').write_text(json.dumps(stats,indent=2)+'\n')
    print(json.dumps(stats,indent=2))

if __name__=='__main__':main()
