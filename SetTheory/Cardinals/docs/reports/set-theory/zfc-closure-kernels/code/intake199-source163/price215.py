#!/usr/bin/env python3
"""Exact literal source composition only. No table compiler or runtime."""
import argparse, hashlib, importlib.util, json
from pathlib import Path

ROOT=Path('/home/codex/.codex/worktrees/ec20/Proofs')
PACKAGE=Path('/tmp/zfc-intake199-root/K216_Rho6_Permutation_2026-10-21/K216_Rho6_Permutation_2026-10-21')
BASE=ROOT/'Computability/BusyBeaver/Research/ZFC/candidate-k215/sites215.json'
HELPER=BASE.parent/'research/composition-allocation/source_splice.py'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--output',type=Path,required=True);a=ap.parse_args()
    assert not a.output.exists()
    assert sha(BASE)=='17af207195179b2508bf91154cd00739374f8862207ca21b9a3cb9098aa6f5ba'
    assert sha(HELPER)=='79036d8b1d85c37927fd9db67c49a8d8c3f8684359d4598c009f31d6c1a790ba'
    spec=importlib.util.spec_from_file_location('reviewed_splice',HELPER)
    sp=importlib.util.module_from_spec(spec);spec.loader.exec_module(sp)
    rows=json.loads(BASE.read_text());parent=json.loads((PACKAGE/'inputs/upstream216/sites216.compact.json').read_text())
    delivered=json.loads((PACKAGE/'machine/sites216.json').read_text())
    word=[r[1:]for r in rows];oldword=[r[1:]for r in parent];newword=[r[1:]for r in delivered]
    needle=oldword[902:1185]
    matches=[i for i in range(len(word)-len(needle)+1)if word[i:i+len(needle)]==needle]
    assert matches==[888],matches
    lo,hi=888,1171
    new=json.loads(json.dumps(rows));changes=[]
    for i in range(lo,hi):
        if new[i][1]in('CI','CD'):new[i][2]={3:5,5:3}.get(new[i][2],new[i][2])
        if new[i]!=rows[i]:changes.append({'ordinal':i,'old':rows[i],'new':new[i]})
    assert [r[1:]for r in new[lo:hi]]==newword[902:1185]
    assert [c['ordinal']for c in changes]==[959,964,1137,1142]
    oldgraph=sp.cfg_intervals(rows);newgraph=sp.cfg_intervals(new)
    assert oldgraph==sp.cfg_arithmetic(rows)and newgraph==sp.cfg_arithmetic(new)
    assert [g[2]for g in oldgraph]==[g[2]for g in newgraph]
    incoming=[(i,t)for i,g in enumerate(oldgraph)if not lo<=i<hi for t in g[2]if lo<=t<hi]
    outgoing=[(i,t)for i in range(lo,hi)for t in oldgraph[i][2]if not lo<=t<hi]
    assert incoming==[(882,888)]and outgoing==[(1165,1171)]
    oldtree=sp.parse(rows);newtree=sp.parse(new)
    oldnodes=sp.nodes(oldtree);newnodes=sp.nodes(newtree)
    a.output.mkdir();raw=sp.compact(new);(a.output/'sites215-rho6.json').write_bytes(raw)
    result={'status':'SOURCE_COMPOSITION_AND_PRICE_PASS','scope':'Local rho6 sampler substitution with exact literal macro identity and CFG boundary checks; no physical state allocation, binary runtime, or new state saving.',
      'baseline':sp.metrics(oldtree),'variant':sp.metrics(newtree),'source_sha256':hashlib.sha256(raw).hexdigest(),
      'interval':[lo,hi],'unique_old_macro_match':matches,'exact_delivered_new_macro_match':True,
      'changes':changes,'inbound':incoming,'outbound':outgoing,'guarded_edges':sum(len(g[2])for g in newgraph),
      'removed_types':len(oldnodes-newnodes),'added_types':len(newnodes-oldnodes),
      'inputs':{str(p):sha(p)for p in[BASE,HELPER,PACKAGE/'inputs/upstream216/sites216.compact.json',PACKAGE/'machine/sites216.json',Path(__file__)]}}
    (a.output/'result.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
if __name__=='__main__':main()
