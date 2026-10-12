"""Alternative lower forests on the sixteen remaining supplied-cut refusals.

A successful core proof is not a complete cut certificate: bundle-interface
relations and their independently authenticated transport remain additional.
The production forest and every verifier are left unchanged.
"""
from collections import Counter
from contextlib import ExitStack
import hashlib
import json
from pathlib import Path
import sys
from unittest.mock import patch
ROOT=Path(__file__).resolve().parents[2];DATA=Path(__file__).parent
sys.path.insert(0,str(ROOT/'fast'))
from fastunknot.core_handlebody import core_handlebody_certificate
from fastunknot.core_handlebody_verify import verify_core_handlebody_certificate
from fastunknot.core_three_handle_reduction import reduce_core_three_handles
from fastunknot.core_three_handle_reduction_verify import replay_core_three_handles
from fastunknot.normal_parallelity_geometry import _parallelity_geometry
from fastunknot.normal_surface_geometry import _prepare,_coordinates
from fastunknot.normal_cut_handlebodies import normal_cut_handlebodies
from fastunknot.normal_cut_handlebodies_verify import verify_normal_cut_handlebodies
from normal_orbit_research.seeds import sources


def alternative(core, mode):
    costs=Counter(f['handle'] for h in core['handles2'] for f in h['cycle'] if f['dimension']==1)
    order=sorted(core['handles1'],key=lambda h:(-costs[h['id']],h['id']) if mode=='max_passages' else (-h['id'],))
    parent=list(range(len(core['handles0'])))
    def root(v):
        while parent[v]!=v:
            parent[v]=parent[parent[v]];v=parent[v]
        return v
    tree=[]
    for h in order:
        a,b=map(root,h['ends'])
        if a!=b:parent[max(a,b)]=min(a,b);tree.append(h['id'])
    return tree,[root(v) for v in range(len(parent))]


def main():
    pins=sources();a=json.loads((DATA/'weighted-forest-audit.json').read_text())
    refused={r['id'] for r in a['cases'] if r['weighted_status']!='COMPLETE'}
    references={r['id']:r['regina'] for r in a['cases']}
    bank=[c for n in ('corpus.json','three_handle_corpus.json') for c in json.loads(
        (ROOT/'fast/marked_parallelity_research'/n).read_text())['cases']]
    records=[]
    for c in bank:
        if c['id'] not in refused:continue
        p=_prepare(c['triangulation'],lambda:None);g=_parallelity_geometry(p,_coordinates(p,c['coordinates'],lambda:None),lambda:None)
        original,_=reduce_core_three_handles(g,strategy='max_weight')
        baseline=core_handlebody_certificate(original['core'])['status'];trials=[]
        for mode in ('max_passages','reverse_id'):
            tree,roots=alternative(g['core'],mode)
            def fixed(core,check):
                check();assert core['handles0']==g['core']['handles0'] and core['handles1']==g['core']['handles1']
                return list(tree),list(roots)
            with ExitStack() as stack:
                for module in ('core_handlebody','core_three_handle_reduction'):
                    stack.enter_context(patch('fastunknot.'+module+'._forest',side_effect=fixed))
                reduced,top=reduce_core_three_handles(g,strategy='max_weight')
                r=core_handlebody_certificate(reduced['core'])
                whole=(normal_cut_handlebodies(c['triangulation'],c['coordinates'],record_certificate=True)
                       if baseline!='COMPLETE' and r['status']=='COMPLETE' else None)
            assert replay_core_three_handles(g,top)==reduced
            trial=dict(mode=mode,forest=tree,status=r['status'],reason=r.get('reason'),top=top)
            if r['status']=='COMPLETE':
                assert verify_core_handlebody_certificate(reduced['core'],r['certificate'])
                trial['core_certificate']=r['certificate']
            if whole is not None:
                trial['whole_status']=whole['status']
                if whole['status']=='COMPLETE':
                    checked=verify_normal_cut_handlebodies(c['triangulation'],c['coordinates'],whole['certificate'])
                    trial['whole_replay']=checked
                    if checked:
                        assert whole['census']['histogram']==references[c['id']]['histogram']
                        trial.update(whole_certificate=whole['certificate'],census=whole['census'])
            trials.append(trial)
        records.append(dict(id=c['id'],default_core_status=baseline,trials=trials))
    assert sources()==pins
    improved=[r['id'] for r in records if r['default_core_status']!='COMPLETE' and any(t['status']=='COMPLETE' for t in r['trials'])]
    whole_improved=[r['id'] for r in records if any(t.get('whole_replay',False) for t in r['trials'])]
    report=dict(scope=__doc__,native_source_sha256=pins,cases=records,new_bare_core_completions=improved,
                new_experimental_whole_cuts=whole_improved,
                reference_sha256=hashlib.sha256((DATA/'weighted-forest-audit.json').read_bytes()).hexdigest())
    Path(__file__).with_suffix('.json').write_text(json.dumps(report,indent=2)+'\n')
    print('New bare core completions:',improved)
    print('New independently replayed experimental whole cuts:',whole_improved)
    print('Default already complete:',[r['id'] for r in records if r['default_core_status']=='COMPLETE'])


if __name__=='__main__':main()
