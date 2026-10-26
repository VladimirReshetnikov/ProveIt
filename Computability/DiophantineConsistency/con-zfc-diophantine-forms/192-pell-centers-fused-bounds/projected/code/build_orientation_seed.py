#!/usr/bin/env python3
"""Replace the squared sign penalty by a linear sign penalty.

This is a new arithmetic certificate, not a polynomial identity on all tuples.
It preserves existential zeros under the inherited raw Pell classification
and growth hypotheses, proved in LINEAR_ORIENTATION.md.
"""
from pathlib import Path
import json, sys

ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT / 'sources'
sys.path.insert(0, str(ROOT / 'code'))
from dag_parent import DAG, analyze

def build(src, alpha=1):
    doc = json.loads(Path(src).read_text())
    nodes = doc['nodes']; old_omega = doc['ports']['Omega']
    d = DAG(); translated = {}
    unique = []; seen = set()
    for r in doc['ports']['requests']:
        key = (r['D'],r['Y'],r['Z'])
        if key not in seen:
            seen.add(key); unique.append(r)
    def copy(i):
        if i in translated: return translated[i]
        if i == old_omega:
            squares = d.sum(d.square(d.sub(copy(r['Y']),copy(r['k'])))
                            for r in unique)
            traces = d.sum(d.add(copy(r['D']),copy(r['Z'])) for r in unique)
            out = d.add(squares,d.mul(d.c(alpha),d.sub(d.c(len(unique)),traces)))
        else:
            n=nodes[i]
            if n[0]=='const':out=d.c(n[1])
            elif n[0]=='var':out=d.v(n[1])
            else:out=getattr(d,n[0])(copy(n[1]),copy(n[2]))
        translated[i]=out
        return out
    out=dict(doc)
    out['residual_nodes']=[copy(r) for r in doc['residual_nodes']]
    out['root']=d.sum(d.square(r) for r in out['residual_nodes'])
    out['ports']={
        'A':copy(doc['ports']['A']),
        'bases':[copy(i) for i in doc['ports']['bases']],
        'T':[copy(i) for i in doc['ports']['T']],
        'E':[copy(i) for i in doc['ports']['E']],
        'requests':[{k:(v if k=='g' else copy(v)) for k,v in r.items()}
                    for r in doc['ports']['requests']],
        'Omega':copy(old_omega),
    }
    out['nodes']=d.nodes
    out['orientation_certificate']={
        'formula':'sum(alpha*(1-X)+(Y-k)^2)',
        'alpha':alpha,
        'unique_pairs':len(unique),
        'small_residue':'sum(alpha*(1-epsilon)+(epsilon*nu-k)^2)',
    }
    return out

def main():
    dst=ROOT/'sources';dst.mkdir(exist_ok=True)
    doc=build(SOURCE/'joint209.json')
    (dst/'joint209_linear_orientation.json').write_text(
        json.dumps(doc,sort_keys=True,indent=2)+'\n')
    metrics=analyze(doc)
    print(json.dumps(metrics,indent=2))

if __name__=='__main__':main()
