#!/usr/bin/env python3
"""Independent finite-control audit and boundary-matcher controls.

Uses the repository's length-preserving RegisterPath transcription, rather
than the new canonical-path normalizer, for all exact control successors.
This validates the finite rank/bisimulation certificate and the matcher's
positive/negative controls. It does not prove any mutated binary table.
"""
import hashlib
import importlib.util
import json
from pathlib import Path
import sys
from types import SimpleNamespace

HERE=Path(__file__).resolve().parent
BASE=Path('/workspace/scratch/bf00ce1dffdf/source/ProveIt/Computability/BusyBeaver/Research/ZFC')
sys.path.insert(0,str(BASE))
import permutation252_phase_analysis as reference
import candidate252_independent_audit as audit
from action_contract import decoder_nodes
from ranked_contract import make_matcher

def main():
    program=audit.ROOT/'lib/jeff-busy-beaver-zfc254/ZF/m254/coq/tm/Prog254.v'
    raw=program.read_bytes();sites,cases,targets,root=reference.program_graph(raw)
    by_site={i:[] for i in range(len(sites))}
    for case,target in zip(cases,targets):by_site[case[0]].append((case,target))
    normal={};ranks={}
    def normalize(site,active=()):
        if site in normal:return normal[site],ranks[site]
        assert site not in active
        if sites[site][1] not in ('CB','CC'):
            normal[site]=site;ranks[site]=0
        else:
            assert len(by_site[site])==1
            target=by_site[site][0][1];assert target is not None
            endpoint,rank=normalize(target,active+(site,))
            normal[site]=endpoint;ranks[site]=rank+1
        return normal[site],ranks[site]
    for site in range(len(sites)):normalize(site)
    assert max(ranks.values())==4 and sum(r>0 for r in ranks.values())==1927
    certificate=HERE/'ranked_fold_scratch/ranked_action_quotient.json'
    q=json.loads(certificate.read_text());classes=q['classes']
    action_sites=[i for i,(_,op,_) in enumerate(sites) if op not in ('CB','CC')]
    assert set(classes)=={sites[i][0] for i in action_sites} and len(classes)==4533
    labels={};successors={};groups={}
    for i in action_sites:
        p,op,r=sites[i];label=(op,r);c=classes[p]
        succ=[sites[normal[t]][0] for _,t in by_site[i] if t is not None]
        assert succ==q['successors'][p]
        projected=tuple(classes[t] for t in succ)
        if c in labels:assert labels[c]==label and successors[c]==projected
        labels[c]=label;successors[c]=projected;groups.setdefault(c,[]).append(p)
    assert len(groups)==4530 and sum(len(v)>1 for v in groups.values())==3
    strict_path=audit.ROOT/'SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/code/27-variant-experiments-machine_search-grammar_search-strict_affine.py'
    sys.modules['cost_search']=SimpleNamespace()
    spec=importlib.util.spec_from_file_location('ranked_audit_strict',strict_path)
    strict=importlib.util.module_from_spec(spec);spec.loader.exec_module(strict)
    matches=make_matcher(strict.canon,decoder_nodes(raw.decode()),q,audit.successor)
    positives=stutters=gap_controls=0
    def frame(pc,effect,gap=40):
        return [('b',int(b)) for b in pc]+[('r',0,1,gap-len(pc)),('b',1),('box',('plain',effect))]
    for case,target in zip(cases,targets):
        site,p,op,r,zero=case
        if op=='CH':continue
        effect=('inc',audit.NEWPHYS[r]) if op=='CI' else ('dec',audit.NEWPHYS[r]) if op=='CD' and not zero else None
        goal=dict(effect=effect,rank_limit=ranks[site]-1 if op in ('CB','CC') else 4,
                  **{'class':classes[sites[normal[target]][0]]})
        pc=reference.successor(p,op,r,zero)
        assert matches([('b',1)],frame(pc,effect),goal);positives+=1
        assert not matches([('b',1)],frame(pc,effect,39),goal);gap_controls+=1
        if op in ('CB','CC'):
            assert not matches([('b',1)],frame(p,None),goal);stutters+=1
    result=dict(status='PASS',scope='Independent finite control rank/bisimulation certificate and matcher controls; no modified TM theorem.',
                original_source_cases=len(cases),silent_sites=1927,max_silent_rank=4,
                visible_action_sites=len(action_sites),bisimulation_classes=len(groups),
                nontrivial_classes=[v for v in groups.values() if len(v)>1],
                all_nonhalt_successor_controls=positives,insufficient_gap39_rejections=gap_controls,
                silent_stutter_rejections=stutters,root=sites[root],
                source_sha256=hashlib.sha256(raw).hexdigest(),certificate_sha256=hashlib.sha256(certificate.read_bytes()).hexdigest(),
                reference_graph_sha256=hashlib.sha256(Path(reference.__file__).read_bytes()).hexdigest())
    (HERE/'ranked_contract_audit.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result))

if __name__=='__main__':main()
