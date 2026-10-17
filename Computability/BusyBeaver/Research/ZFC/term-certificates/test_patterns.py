#!/usr/bin/env python3
"""Finite controls of trusted top-down exact C254 pattern matching."""
from copy import deepcopy
from hashlib import sha256
from itertools import product, islice
import json
from pathlib import Path
import platform
import time

import term_patterns as V
import term_circuits as C
import pattern_codec as B
import term_codec as OLD
import term_paths as P
import test_circuits as TC
import test_paths as TP
import check_term254 as CT
import symbolic254 as S
import canonical254 as CAN
import term254 as T

BASE=Path(__file__).resolve().parent
TABLES=V.load_templates(BASE/'source50/data/spec254.json')


def strip(cert):
    cert=deepcopy(cert)
    cert['format']=V.FORMAT
    for row in cert['proof_rows']:
        row.pop('constructor_ids',None)
    return cert


def fresh_stats():
    return dict(pattern_visits=0, pattern_constructor_checks=0, parameter_checks=0,
                literal_zero_checks=0, virtual_zero_constructors=0,max_pending_obligations=0)


def main():
    start=time.monotonic()
    tests=[]; rejects=[]
    specimens=[S.Raw(0),S.Raw(1,(0,),(S.Raw(0),S.Raw(0))),S.Raw(2,(1,),(S.Raw(0),))]
    specimens += [S.Raw(tag,tuple(range(S.ARITY[tag]))) for tag in range(3,11)]
    specimens += [S.Raw(11,(0,1,2))]
    controls=[]
    for raw in specimens:
        term,goal=CT.convert_control(raw)
        old=TC.from_term(term); cert=strip(old)
        assert C.verify_certificate(old,TABLES,goal=goal)
        stats={}
        assert V.verify_certificate(cert,TABLES,goal=goal,stats=stats)
        assert not V.verify_certificate(cert,TABLES)
        controls.append((old,cert,goal))
    tests.append('all12 exact source50 rule controls accepted with trusted goal; all12 reject default fixedF')

    # Compare every trusted pattern against the original source50 constructor,
    # including dynamic B0(0,0) normalization from colliding substitutions.
    assignments=accepted=invalid_gates=virtual_cases=virtual_constructors=0
    per_rule={}
    for rule,pattern in TABLES.items():
        name='bundle' if rule==11 else 'rho'+str(rule-2)
        counts={'assignments':0,'accepted_rule_instances':0,'invalid_bundle_gates':0,
                'max_pattern_visits':0,'virtual_zero_cases':0}
        for vals in product(range(3),repeat=pattern.arity):
            arena=TP.ProducerArena()
            literal=[0,arena.b(1,0,0),arena.b(2,0,0)]
            args=[literal[x] for x in vals]
            out=arena.apply(name,args)
            stats=fresh_stats()
            assert V.match_pattern(arena.nodes,out,args,pattern,stats)
            assignments+=1; counts['assignments']+=1
            counts['max_pattern_visits']=max(counts['max_pattern_visits'],stats['pattern_visits'])
            if stats['virtual_zero_constructors']:
                virtual_cases+=1;counts['virtual_zero_cases']+=1
                virtual_constructors+=stats['virtual_zero_constructors']
            row={'tag':rule,'args':args,'children':[],'formula':out}
            valid=True
            if rule==11:
                paths=[P.find_path(arena.nodes,args[2],args[j]) for j in (0,1)]
                valid=all(path is not None for path in paths)
                row['gate_paths']=[path if path is not None else [] for path in paths]
            cert={'format':V.FORMAT,'nodes':arena.nodes,'proof_rows':[row]}
            assert V.verify_certificate(cert,TABLES,goal=out)==valid
            if valid:
                accepted+=1;counts['accepted_rule_instances']+=1
            else:
                invalid_gates+=1;counts['invalid_bundle_gates']+=1
        per_rule[str(rule)]=counts
    assert assignments==261 and virtual_cases>0
    # rho8 allzero collapses to literal truth, despite its nonliteral pattern.
    arena=TP.ProducerArena();out=arena.apply('rho8',[0,0,0,0]); assert out==0
    stats=fresh_stats(); assert V.match_pattern(arena.nodes,0,[0,0,0,0],TABLES[10],stats)
    assert stats['virtual_zero_constructors']>0
    tests.append('all261 assignments over0/1/2 match exact source50 templates, including actualZ at expectedB0; invalid bundle gates remain rejected')

    # Accept duplicated positive output and compound nodes, without relying on
    # a first-copy lookup or a witness-selected constructor-result array.
    for original in (2,3):
        old,cert,goal=deepcopy(controls[original])
        cert['nodes'].append(deepcopy(cert['nodes'][goal]));goal=len(cert['nodes'])-1
        cert['proof_rows'][-1]['formula']=goal
        old['nodes']=deepcopy(cert['nodes']);old['proof_rows'][-1]['formula']=goal
        if original==3:old['proof_rows'][-1]['constructor_ids'][-1]=goal
        assert V.verify_certificate(cert,TABLES,goal=goal)
        controls.append((old,cert,goal))
    # rho1 is the original existential/equality axiom. Duplicate its compound
    # All subtree (the root's left child), then the root, preserving denotation.
    old,cert,goal=deepcopy(controls[3]);root=cert['nodes'][goal]
    assert cert['nodes'][root[2]][1] == 2
    cert['nodes'].append(deepcopy(cert['nodes'][root[2]]));left=len(cert['nodes'])-1
    cert['nodes'].append(['b',root[1],left,root[3]]);goal=len(cert['nodes'])-1
    cert['proof_rows'][-1]['formula']=goal
    assert V.verify_certificate(cert,TABLES,goal=goal)
    tests.append('duplicate GEN/schema outputs and non-first duplicate compound branch accepted')
    # Same-value parameter copies may deliberately fail exactID leaf checks.
    arena=TP.ProducerArena();f=arena.b(1,0,0);out=arena.apply('rho1',[f,0])
    arena.nodes.append(['b',1,0,0]);duplicate=len(arena.nodes)-1
    cert={'format':V.FORMAT,'nodes':arena.nodes,'proof_rows':[
        {'tag':3,'args':[duplicate,0],'children':[],'formula':out}]}
    assert not V.verify_certificate(cert,TABLES,goal=out)
    rejects.append('equal_value_duplicate_parameter_leaf_mismatch_intentionally_rejected')

    for side in (True,False):
        cert,goal=TP.bundle_fixture(side);cert=strip(cert)
        stats={};assert not V.verify_certificate(cert,TABLES,goal=goal,stats=stats)
        assert stats['reason']==('bundle_gate_1' if side else 'bundle_gate_2')
        rejects.append(stats['reason']+'_distinctIDs_equalvalues')

    deep=json.loads((BASE/'deep-bundle-control.json').read_text())
    deep['certificate']['format']='term-c254-v1'
    old=TC.from_term(deep['certificate']);cert=strip(old);goal=deep['trusted_control_goal']
    deep_stats={};old_stats={}
    assert C.verify_certificate(old,TABLES,goal=goal,stats=old_stats)
    assert V.verify_certificate(cert,TABLES,goal=goal,stats=deep_stats)
    assert deep_stats['path_edges']==2048
    controls.append((old,cert,goal))
    tests.append('deep2048-edge exact bundle accepted; pattern traversal does not descend into parameter denotations')

    def reject(name,cert,goal):
        stats={};assert not V.verify_certificate(cert,TABLES,goal=goal,stats=stats),name
        rejects.append(name)
    for name,edit in [
        ('zero_alias',lambda c:c['nodes'].append(['b',0,0,0])),
        ('forward_reference',lambda c:c['nodes'].append(['b',1,len(c['nodes']),0])),
        ('boolean_node_tag',lambda c:c['nodes'].append(['b',True,0,0])),
        ('empty_proof',lambda c:c.update(proof_rows=[])),
        ('false_truth',lambda c:c['proof_rows'][0].update(formula=1)),
    ]:
        c=deepcopy(controls[0][1]);edit(c);reject(name,c,0)
    c=deepcopy(controls[3][1]);c['proof_rows'][-1]['constructor_ids']=[]
    reject('constructor_ids_not_in_new_protocol',c,controls[3][2])
    c=deepcopy(controls[2][1]);c['proof_rows'][-1]['formula']=0;reject('false_GEN',c,0)
    c=deepcopy(controls[5][1]);c['proof_rows'][-1]['formula']=0;reject('wrong_template_root',c,0)
    c=deepcopy(controls[1][1]);c['nodes'].append(['b',1,0,0]);f=len(c['nodes'])-1
    c['proof_rows'][-1].update(args=[f],formula=f);reject('false_MP_major',c,f)
    c=deepcopy(controls[11][1]);c['proof_rows'][-1]['gate_paths'][0]+=[0]
    reject('trailing_gate_path',c,controls[11][2])
    c=deepcopy(controls[0][1]);c['goal']=0;c['templates']={'all':True}
    assert not V.verify_certificate(c,TABLES)
    tests.append('malformed nodes/rows, forgedMP/GEN, retained circuit witness fields and malformed paths reject; candidate cannot pick templates/goal')

    # Compare exact binary protocols: literally erase only the old fixed-length
    # lists of unary constructor IDs. Everything else has the same fields.
    measurements=[]
    for old,cert,goal in controls:
        old_word=OLD.encode(old,TABLES);word=B.encode(cert,TABLES)
        ids=[j for row in old['proof_rows'] for j in row.get('constructor_ids',[])]
        removed=sum(j+1 for j in ids)
        assert len(old_word)-len(word)==removed
        assert B.decode(word,TABLES)==cert
        assert V.verify_certificate(B.decode(word,TABLES),TABLES,goal=goal)
        assert not B.accepts(word,TABLES)
        measurements.append({'last_tag':cert['proof_rows'][-1]['tag'],'positive_nodes':len(cert['nodes'])-1,
            'old_bits':len(old_word),'pattern_bits':len(word),'removed_unary_witness_bits':removed,
            'removed_constructor_ids':len(ids)})
    tests.append('15 exact new-codec roundtrips and fixedF negatives; bit savings equal exactly sum(id+1) of omitted witnesses')

    nat=lambda value:'1'*value+'0'
    tag=lambda value,width:format(value,'0'+str(width)+'b')
    malformed={
        'empty':'','truncated_unary':'111111','nonbinary':'02',
        'node_count_before_allocation':nat(8)+'0000',
        'row_count_before_allocation':nat(0)+nat(8)+'00000',
        'zero_alias':nat(1)+tag(0,2)+nat(0)+nat(0)+nat(0),
        'node_forward_reference':nat(1)+tag(1,2)+nat(1)+nat(0)+nat(0),
        'unknown_rule':nat(0)+nat(1)+tag(12,4)+nat(0),
        'proof_forward_reference':nat(0)+nat(1)+tag(2,4)+nat(0)+nat(0)+nat(0),
        'argument_reference':nat(0)+nat(1)+tag(2,4)+nat(1)+nat(0)+nat(0),
        'formula_reference':nat(0)+nat(1)+tag(0,4)+nat(1),
        'truncated_path':B.encode(controls[11][1],TABLES)[:-1],
        'unterminated_path':B.encode(controls[11][1],TABLES)[:-1]+'1',
        'leftover_bits':B.encode(controls[0][1],TABLES)+'0'}
    malformed_reasons={}
    for name,word in malformed.items():
        ss={};assert B.decode(word,TABLES,stats=ss) is None,name
        malformed_reasons[name]=ss['reason']
    truth_word=B.encode(controls[0][1],TABLES)
    assert all(B.decode(truth_word[:n],TABLES) is None for n in range(len(truth_word)))
    tests.append('14 explicit malformed-codec controls and all proper prefixes of8bit truth reject')
    short={'max_length':17,'words':0,'successful_parses':0,'fixedF_acceptances':0}
    for length in range(short['max_length']+1):
        for word in B.words_at_length(length):
            short['words']+=1;c=B.decode(word,TABLES)
            if c is not None:
                short['successful_parses']+=1;assert B.encode(c,TABLES)==word
                if V.verify_certificate(c,TABLES):short['fixedF_acceptances']+=1
    assert short['words']==262143
    assert short['fixedF_acceptances']==0
    assert list(islice(B.words(),8))==['','0','1','00','01','10','11','000']
    tests.append('all262143 words length<=17 terminate; every successful parse exactly re-encodes; finite negatives do not imply consistency')

    # Both arithmetic and runtime value construction are unnecessary verifier
    # dependencies. Trusted pattern tables have already been fixed above.
    def forbidden(*_a,**_k):raise AssertionError('producer/constructor interpreter called')
    patches=[(TC,'from_term',TC.from_term),(P,'find_path',P.find_path),
             (C,'verify_certificate',C.verify_certificate),(C,'load_templates',C.load_templates),
             (C,'compile_templates',C.compile_templates)]
    for module in (S,CAN):
        for name in ('pair','unpair','parse','build','verify_certificate','make_certificate'):
            patches.append((module,name,getattr(module,name)))
    for cls in (P.LookupArena,S.Arena,CAN.CanonicalArena):
        for name in ('b','apply'):
            patches.append((cls,name,getattr(cls,name)))
    try:
        for obj,name,_ in patches:setattr(obj,name,forbidden)
        for _,c,g in controls:assert V.verify_certificate(c,TABLES,goal=g)
    finally:
        for obj,name,old in reversed(patches):setattr(obj,name,old)
    tests.append('15 controls still accepted with all numeric/producer/compiler/old circuit verifier APIs disabled')

    old_match=V.match_pattern;old_constructor=C.constructor
    try:
        for kind in (MemoryError,RecursionError):
            def exhausted(*_a,_kind=kind,**_k):raise _kind('resource probe')
            for owner,name,case in ((V,'match_pattern',3),(C,'constructor',2)):
                setattr(owner,name,exhausted)
                try:B.accepts(B.encode(controls[case][1],TABLES),TABLES)
                except kind:pass
                else:raise AssertionError('resource exception swallowed')
                setattr(owner,name,old_match if owner is V else old_constructor)
    finally:V.match_pattern=old_match;C.constructor=old_constructor
    tests.append('MemoryError/RecursionError inside actual schema matcher and GEN checker propagate through codec')

    def expanded(pattern,slot):
        if slot<=pattern.arity:return (1,0)
        _,left,right=pattern.steps[slot-pattern.arity-1]
        l,c=expanded(pattern,left);r,d=expanded(pattern,right)
        return (1+l+r,1+c+d)
    static={str(tag):{'circuit_steps':len(p.steps),'expanded_pattern_visits':expanded(p,p.root)[0],
             'expanded_constructor_visits':expanded(p,p.root)[1]} for tag,p in TABLES.items()}
    result={'status':'PASS','python':platform.python_version(),'elapsed_seconds':time.monotonic()-start,
        'command':'uv run --no-project python -B test_patterns.py',
        'scope':'ordinary exact-calculus transformation and finite executable/codec QA; no Lean proof, actual TM, state cost or PA claim',
        'positive_controls':len(controls),'fixedF_control_rejections':len(controls),
        'template_assignments':assignments,'valid_template_rule_instances':accepted,
        'invalid_bundle_gate_instances':invalid_gates,'virtual_zero_cases':virtual_cases,
        'virtual_zero_constructor_checks':virtual_constructors,'per_rule':per_rule,
        'static_traversal_counts':static,'deep_bundle_pattern_stats':deep_stats,
        'deep_bundle_old_circuit_stats':old_stats,'word_measurements':measurements,
        'short_words':short,'malformed_word_reasons':malformed_reasons,'tests':tests,'rejected_corruptions':rejects,
        'source_sha256':{name:sha256((BASE/name).read_bytes()).hexdigest() for name in
           ['term_patterns.py','pattern_codec.py','test_patterns.py','term_circuits.py','term_codec.py','source50/data/spec254.json']}}
    (BASE/'pattern-results.json').write_text(json.dumps(result,indent=2)+'\n')
    (BASE/'example-pattern-bundle.json').write_text(json.dumps({
        'description':'Positive bundle(0,1,2), not a refutation',
        'trusted_control_goal':controls[11][2],
        'certificate':controls[11][1]},indent=2)+'\n')
    (BASE/'example-pattern-bundle.bits').write_text(B.encode(controls[11][1],TABLES))
    print(json.dumps(result,indent=2))

if __name__=='__main__':main()
