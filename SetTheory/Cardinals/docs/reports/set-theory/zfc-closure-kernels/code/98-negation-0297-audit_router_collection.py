#!/usr/bin/env python3
"""Regression witness for descent through a temporary atomic-key rule.

Reconstruct the actual failed 243/1 route. The old pre-collection test accepts
it after a temporary rule is installed at a physical terminal. Collection
erases that rule. Both the terminal barrier and the post-collection test reject
the resulting path. The repaired 135-rule seed satisfies every route.
"""
from pathlib import Path
import argparse, hashlib, json

def main():
    p=argparse.ArgumentParser();p.add_argument('--output',type=Path,required=True);a=p.parse_args()
    base=Path(__file__).resolve().parent
    bad_path=base/'lm-church8-warm/search0.json';good_path=base/'lm-church8-repaired/seed.json'
    bad=json.loads(bad_path.read_text());good=json.loads(good_path.read_text())
    meta=json.loads((base/'lm-church8-backend/backend.json').read_text());terms=set(meta['terminals'])
    def dictionary(data):return {w:(l,r) for w,l,r in data['rules']}
    def routes(data):return {(r['source'],r['read']):r['word'] for r in data['routes']}
    def project(g,w,bits,terminal_barrier):
        for bit in bits:
            if terminal_barrier and w in terms:return None
            if w not in g:return None
            w=g[w][int(bit)]
        return w
    g=dictionary(bad);rt=routes(bad);atom='LNPQXJLNPQSU'
    assert atom in terms and atom not in g
    assert project(g,rt[243,1],'0',False)==atom
    augmented=dict(g);augmented[atom]=(atom[:-2],'SU')
    assert project(augmented,rt[243,1],'01',False)=='SU'
    assert project(augmented,rt[243,1],'01',True) is None
    live=set()
    def visit(w):
        if w in terms or w in live:return
        assert w in augmented;live.add(w)
        for c in augmented[w]:visit(c)
    for w in bad['roots']+list(rt.values()):visit(w)
    collected={w:augmented[w] for w in live}
    assert collected==g and project(collected,rt[243,1],'01',False) is None
    gg=dictionary(good);gr=routes(good)
    for c in meta['route_derivation']:
        assert project(gg,gr[c['source'],c['read']],c['prefix'],True)==c['new_target']
    report=dict(status='PASS_POST_COLLECTION_ROUTE_REGRESSION',invalid_witness_status='INVALID_ROUTING_TRACE',source=243,read=1,prefix='01',intermediate_physical_terminal=atom,old_pre_collection_check_accepts=True,terminal_barrier_rejects=True,post_collection_check_rejects=True,repaired_grammar_roles=good['rules_count'],repaired_projection_cases=len(meta['route_derivation']),invalid_candidate_sha256=hashlib.sha256(bad_path.read_bytes()).hexdigest(),repaired_seed_sha256=hashlib.sha256(good_path.read_bytes()).hexdigest())
    a.output.write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2))

if __name__=='__main__':main()
