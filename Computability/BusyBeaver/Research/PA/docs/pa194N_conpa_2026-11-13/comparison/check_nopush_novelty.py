"""Exact root-free action-graph novelty against every recognized 194 table.

Comparison uses tuples, not digest equality. Reflections and simultaneous
read/write complementations are included only as cosmetic transformations.
"""
from pathlib import Path
import argparse, hashlib, json
from audit_census import parse_table, canonical

def sh(b):return hashlib.sha256(b).hexdigest()
def full_form(data,reflect=False,complement=False):
    cs=[x for q in sorted(data[1]) if (x:=canonical(data,q,reflect,complement)) is not None]
    assert cs
    return min(cs)

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    here=Path(__file__).resolve().parent
    ap.add_argument('--candidate',type=Path,default=here.parent/'verification/independent/dense.tm')
    ap.add_argument('--census',type=Path,default=here/'census/census.json')
    ap.add_argument('--tables',type=Path,default=here/'census/tables')
    ap.add_argument('--output',type=Path,default=here/'nopush_novelty.json')
    args=ap.parse_args()
    raw=args.candidate.read_bytes();data=parse_table(raw)
    assert data is not None and len(data[1])==194
    assert sh(raw)=='37f7e909724cab7fd667db28f89b9c81653d2576c033750e783b40b3289c04f9'
    assert canonical(data,0) is not None
    forms={(r,c):full_form(data,r,c) for r,c in [(False,False),(True,False),(False,True),(True,True)]}
    corpus=json.loads(args.census.read_text());comparison=[];groups={}
    for rec in corpus['identities']:
        if rec['states']!=194:continue
        b=(args.tables/(rec['sha256']+'.tm')).read_bytes();assert sh(b)==rec['sha256']
        ref=parse_table(b);normal=full_form(ref)
        if rec['graph_hash'] in groups:assert normal==groups[rec['graph_hash']]
        else:groups[rec['graph_hash']]=normal
        equal={str((r,c)):normal==form for (r,c),form in forms.items()}
        assert not any(equal.values()),'Candidate is cosmetically identical to an existing table.'
        comparison.append(dict(sha256=rec['sha256'],graph_hash=rec['graph_hash'],first_path=rec['first_path'],matches=equal))
    assert len(groups)==8
    primary=(args.tables/'4bfea62b17aad7d8c8c5e682fe8942e0a86b93e4351f8e675e32705bdaae007f.tm').read_bytes()
    parent=parse_table(primary)
    assert len(parent[1])==194
    # State labels differ after BFS; the native witness independently fixes the
    # precise changed row. This graph receipt deliberately does not infer that.
    result=dict(status='PASS',snapshot=corpus['snapshot'],candidate_sha256=sh(raw),
        working_states=194,all_working_states_reachable_from_start=True,
        previous_literal_byte_forms=len(comparison),previous_graph_classes=len(groups),
        exact_tuple_comparison=True,arbitrary_state_renaming_excluded=True,
        arbitrary_graph_reaching_root_excluded=True,tape_reflection_excluded=True,
        global_symbol_complementation_excluded=True,
        semantic_scope='Graph distinction only; symbol complementation is not a blank-zero semantic equivalence.',
        candidate_graph_hash=sh(repr(forms[False,False]).encode()),comparisons=comparison)
    args.output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k!='comparisons'},indent=2))

if __name__=='__main__':main()
