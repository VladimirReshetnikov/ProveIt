#!/usr/bin/env python3
"""Portable standard-library replay of the head-variant evidence.

No solver or Lean installation is required. Solver optimality, physical
allocation and binary-TM runtime are not asserted by this packet.
"""
from pathlib import Path
import sys,json,hashlib
sys.dont_write_bytecode=True
ROOT=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT/'code'))

def tup(t):return tuple(map(tup,t)) if isinstance(t,list) else t

def main():
    provenance=json.loads((ROOT/'provenance.json').read_text())
    for item in provenance['files']:
        assert hashlib.sha256((ROOT/item['path']).read_bytes()).hexdigest()==item['sha256'],item['path']
    import ax_head_reorder as extraction
    import verify_head_variants as variants
    import grammar as g,permute as p
    extraction.main();variants.main()
    def expected_word(order,mask):
        heads=p.heads.copy()
        for bit,h in enumerate((2,3,5)):
            if mask>>bit&1:
                t=heads[h];heads[h]=p.I(t[2][1],p.I(t[1],t[2][2]))
        return p.prefix+sum([p.compile(heads[j-1]) for j in order],[])+p.suffix
    best=json.loads((ROOT/'results/reorder_grammar_best.json').read_text())
    assert g.collapse(tup(best['tree']))==expected_word(best['order'],best['antecedent_mask'])==best['word']
    assert g.cost(tup(best['tree']))==best['internal_nodes']==161
    batch=json.loads((ROOT/'results/reorder_milp_batch0.json').read_text())
    counts=[]
    for item in batch:
        tree=tup(json.loads((ROOT/'results'/item['tree_path']).read_text()))
        assert g.collapse(tree)==expected_word(item['order'],item['antecedent_mask'])==item['word']
        assert g.cost(tree)==item['internal_nodes']
        assert item['reported_solver_gap']>0 and item['optimality_claimed'] is False
        counts.append(item['internal_nodes'])
    assert counts==[160,160,159,158,162,160,160,159]
    print('PASS: pinned source identities; 720 exact head permutations; 5,760 exact symbolic variants; all eight retained grammar witnesses.')
    print('No new physical TM or grammar optimality result is certified.')

if __name__=='__main__':main()
