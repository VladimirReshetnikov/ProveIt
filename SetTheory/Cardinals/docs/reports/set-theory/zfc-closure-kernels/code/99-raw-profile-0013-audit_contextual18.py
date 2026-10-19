#!/usr/bin/env python3
"""Independent contextual-C grammar check, followed by inherited invariants.

The inherited terminal mask for C/state18 remains 2 in the context theorem.
A direct left C is permitted only inside a word whose incoming mask is 2.
The ordinary structural checker sees C provisionally widened ONLY AFTER the
independent recursive check discharges every real root.  No runtime or blank
initialization theorem is inferred from either structural calculation.
"""
from functools import cache
from pathlib import Path
import argparse, importlib.util, json

def context_masks(rules,allowed,roots):
    assert allowed['C']==2
    visiting=set()
    @cache
    def mask(w):
        if w in allowed:return allowed[w]
        assert w in rules and w not in visiting,('missing/cyclic word',w)
        visiting.add(w)
        a,b=rules[w]
        assert a and b and a+b==w
        left,right=mask(a),mask(b)
        result=2 if a=='C' else 3 if left&1 else 0
        if not right&2:result=0
        visiting.remove(w)
        return result
    values={w:mask(w)for w in rules}
    assert all(values[w]!=0 for w in rules),('illegal child orientation',values)
    assert all(mask(w)==3 for w in roots),('root lacks both orientations',[(w,mask(w))for w in roots if mask(w)!=3])
    return values

def check_boundary_examples():
    allowed={'C':2,'M':3,'A':3}
    assert context_masks({'CM':('C','M'),'ACM':('A','CM')},allowed,{'ACM'})=={'CM':2,'ACM':3}
    assert context_masks({'MC':('M','C')},allowed,{'MC'})=={'MC':3}
    for rules,roots in [({'CM':('C','M')},{'CM'}),
                        ({'CM':('C','M'),'CMM':('CM','M')},{'CMM'})]:
        try:context_masks(rules,allowed,roots)
        except AssertionError:pass
        else:raise AssertionError('An inadmissible boundary example was accepted')
    return 'PASS_CONTEXTUAL_BOUNDARY_EXAMPLES'

def audit(candidate,runtime):
    spec=importlib.util.spec_from_file_location('inherited_fine_audit',runtime/'code/audit_fine_grammar.py')
    module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module)
    data=json.loads(candidate.read_text())
    source,terminals,names,allowed,_=module.make_vocabulary(data.get('source_override'))
    assert source['atoms'][terminals['C']]['state']==18 and allowed['C']==2
    for p in data.get('terminal_orientation_relaxations',[]):
        assert p['word']!='C' and allowed[p['word']]==p['old_mask'] and p['new_mask']==3
        assert source['atoms'][terminals[p['word']]]['state']==p['state']
        allowed[p['word']]=3
    rules={w:(a,b)for w,a,b in data['rules']}
    routes={(r['source'],r['read']):r['word']for r in data['routes']}
    erased={177,74};sequences=set(source['sequence_states'])
    roots=set(data['roots'])|set(routes.values())
    # Reconstruct mandatory physical entry roots independently of the JSON
    # roots list, including the framework's direct target edges.
    for q in source['required_entry_roots']:
        edges=[tuple(e)for e in source['incoming'][str(q)]if e[0]not in sequences]
        released=edges and all(e in routes or e[0]in erased for e in edges)
        if not released and q not in erased:roots.add(names[q])
    for line in module.TABLE.read_text().splitlines():
        if not line or line.startswith('#'):continue
        q,b,w,d,t=line.split();q,b,t=int(q),int(b),int(t)
        if q not in sequences|erased and (q,b)not in routes and t in sequences:
            roots.add(names[t])
    masks=context_masks(rules,allowed,roots)
    original=module.make_vocabulary
    def provisional_vocabulary(override=None):
        source,terminals,names,allowed,encode=original(override)
        allowed['C']=3
        return source,terminals,names,allowed,encode
    module.make_vocabulary=provisional_vocabulary
    try:result=module.audit(candidate,short_scan=True)
    finally:module.make_vocabulary=original
    result['inherited_structural_status']=result['status']
    result['status']='PASS_CONTEXTUAL_STRUCTURAL_ONLY'
    result['contextual_state']=18
    result['contextual_terminal']='C'
    result['root_mask_requirement']=3
    result['checked_context_roots']=sorted(roots)
    result['right_only_words']=sorted(w for w,m in masks.items()if m==2)
    result['direct_C_left_words']=sorted(w for w,(a,b)in rules.items()if a=='C')
    result['scope']='Assumes the conditional C interface and declared ordinary terminal interfaces; requires actual-table universal verification and exact blank initialization.'
    result['boundary_examples']=check_boundary_examples()
    return result

if __name__=='__main__':
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('candidate',type=Path)
    ap.add_argument('--runtime',type=Path,required=True)
    ap.add_argument('--output',type=Path,required=True)
    args=ap.parse_args()
    result=audit(args.candidate.resolve(),args.runtime.resolve())
    args.output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:result[k]for k in ['status','grammar_states','right_only_words','direct_C_left_words','boundary_examples']},indent=2))
