#!/usr/bin/env python3
"""Canonical native-Cantor term arenas and gate-free certificate reference.
No binary machine or free canonicality claim. Pairwise validation and a
fully deterministic square-shell arena generator are both explicit.
"""
from pathlib import Path
import sys,copy,itertools,random,json
if not __debug__:raise RuntimeError('Run without -O.')
HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE.parent/'architectures'))
import oracle_search as O
C,P,T=O.C,O.P,O.T
FORMAT='term-c254-canonical-v1'

def validate_canonical(nodes,stats):
    C.validate_nodes(nodes,stats)
    stats['uniqueness_pairs']=0
    for i in range(1,len(nodes)):
        for j in range(1,i):
            stats['uniqueness_pairs']+=1
            C.require(nodes[i][1:]!=nodes[j][1:],'duplicate_constructor')

def constructor_key(node):
    _,tag,left,right=node
    return max(left,right),left,right,tag

def validate_ordered(nodes,stats):
    C.validate_nodes(nodes,stats);previous=None;stats['adjacent_key_checks']=0
    for node in nodes[1:]:
        key=constructor_key(node)
        if previous is not None:
            stats['adjacent_key_checks']+=1
            C.require(previous<key,'constructor_order')
        previous=key

def priority_reindex(nodes):
    """Sparse canonical arena, ordered using only adjacent-key validation.
    Offline certificate normalization, not a proposed binary sorting routine.
    """
    canonical,firstmap=normalize_arena(nodes)
    remap={0:0};pending=set(range(1,len(canonical)));new=[['z']]
    while pending:
        eligible=[]
        for old in pending:
            _,tag,left,right=canonical[old]
            if left in remap and right in remap:
                node=['b',tag,remap[left],remap[right]]
                eligible.append((constructor_key(node),old,node))
        if not eligible:raise AssertionError('Acyclic arena has no available node')
        key,old,node=min(eligible)
        remap[old]=len(new);new.append(node);pending.remove(old)
    validate_ordered(new,{'node_records':0})
    return new,[remap[i] for i in firstmap]

def verify(cert,*,control_goal=None,stats=None,ordered=False):
    if stats is None:stats={}
    stats.update(node_records=0,constructor_checks=0,proof_rows=0,reason=None)
    try:
        C.require(type(cert) is dict and cert.get('format')==FORMAT,'format')
        nodes=cert['nodes'];(validate_ordered if ordered else validate_canonical)(nodes,stats)
        if control_goal is not None:C.require(type(control_goal) is int and 0<=control_goal<len(nodes),'control_goal')
        rows=cert['proof_rows'];C.require(type(rows) is list,'proof_list');formulas=[]
        for i,row in enumerate(rows):
            stats['proof_rows']+=1
            C.require(type(row) is dict and set(row)=={'tag','args','children','formula'},'row_fields')
            tag,args,children,out=(row[k] for k in ('tag','args','children','formula'))
            C.require(type(tag) is int and 0<=tag<12,'proof_tag')
            C.require(type(args) is list and len(args)==C.ARITY[tag],'proof_arity')
            C.require(all(type(j) is int and 0<=j<len(nodes) for j in args),'argument')
            C.require(type(out) is int and 0<=out<len(nodes),'claimed_formula')
            C.require(type(children) is list and len(children)==(2 if tag==1 else 1 if tag==2 else 0),'premise_arity')
            C.require(all(type(j) is int and 0<=j<i for j in children),'premise_reference')
            if tag==0:C.require(out==0,'truth')
            elif tag==1:
                C.require(out==args[0],'mp_conclusion')
                C.require(C.constructor(nodes,formulas[children[1]],0,formulas[children[0]],out,stats),'mp_major')
            elif tag==2:C.require(C.constructor(nodes,out,2,args[0],formulas[children[0]],stats),'gen')
            else:
                if tag==11:C.require(args[2]!=args[0] and args[2]!=args[1],'canonical_bundle_gate')
                C.require(O.O.match_oracle(nodes,out,args,O.ORACLE,tag),'fixed_pattern')
            formulas.append(out)
        C.require(bool(formulas),'empty_proof')
        C.require(formulas[-1]==control_goal if control_goal is not None else C.is_falsity(nodes,formulas[-1]),'fixed_or_control_endpoint')
        return True
    except (C.Invalid,ValueError,TypeError,KeyError,IndexError) as e:
        stats['reason']=str(e);return False

def normalize_arena(nodes):
    stats={'node_records':0};C.validate_nodes(nodes,stats)
    new=[['z']];remap=[0];intern={}
    for _,tag,left,right in nodes[1:]:
        key=(tag,remap[left],remap[right])
        if key==(0,0,0):newid=0
        elif key in intern:newid=intern[key]
        else:newid=len(new);intern[key]=newid;new.append(['b',*key])
        remap.append(newid)
    validate_canonical(new,{'node_records':0})
    return new,remap

def normalize_certificate(cert,*,ordered=False):
    nodes,mp=(priority_reindex if ordered else normalize_arena)(cert['nodes']);rows=[]
    for r in cert['proof_rows']:
        rows.append(dict(tag=r['tag'],args=[mp[i] for i in r['args']],children=r['children'].copy(),formula=mp[r['formula']]))
    return dict(format=FORMAT,nodes=nodes,proof_rows=rows),mp

def duplicate_certificate(cert):
    nodes=[['z']];mp=[0]
    for _,tag,l,r in cert['nodes'][1:]:
        node=['b',tag,mp[l],mp[r]];nodes.extend([node.copy(),node.copy()]);mp.append(len(nodes)-1)
    out=copy.deepcopy(cert);out['nodes']=nodes
    for r in out['proof_rows']:
        r['args']=[mp[i] for i in r['args']];r['formula']=mp[r['formula']]
    return out,mp

def shell_pairs(m):
    yield from ((l,m) for l in range(m))
    yield from ((m,r) for r in range(m+1))

def cantor_pairs(m):
    yield from ((m-r,r) for r in range(m+1))

def generated_prefix(last_id,*,pairing='square'):
    if type(last_id) is not int or last_id<0:raise ValueError('last_id')
    nodes=[['z']]
    pairs=shell_pairs if pairing=='square' else cantor_pairs if pairing=='cantor' else None
    if pairs is None:raise ValueError('pairing')
    for m in itertools.count():
        for l,r in pairs(m):
            for tag in range(4):
                if (tag,l,r)==(0,0,0):continue
                if len(nodes)>last_id:return nodes
                assert l<len(nodes) and r<len(nodes)
                nodes.append(['b',tag,l,r])

def square_pair(l,r):return l*l+l+r if l>=r else r*r+l

def native_values(nodes):
    vals=[0]
    for _,tag,l,r in nodes[1:]:
        a,b=vals[l],vals[r];vals.append(4*((a+b)*(a+b+1)//2+b)+tag)
    return vals

def tests():
    counts={'controls':0,'duplicate_normalizations':0,'accepted_control_preservations':0,'fixedF_rejections':0,'generator_prefixes':0,'generated_nodes':0,'random_arena_denotation_checks':0,'cantor_generator_prefixes':0,'cantor_generated_nodes':0,'ordered_normalizations':0,'ordered_acceptance_preservations':0}
    for cert,out in O.controls():
        for old,goal in ((cert,out),(lambda d:(d[0],d[1][out]))(duplicate_certificate(cert))):
            accepted=O.verify(old,control_goal=goal)
            new,mp=normalize_certificate(old)
            # Normalization cannot turn an invalid source gate into a valid one;
            # controls otherwise agree exactly, including virtual-zero MP.
            assert verify(new,control_goal=mp[goal])==accepted
            if accepted:counts['accepted_control_preservations']+=1
            assert not verify(new);counts['fixedF_rejections']+=1
            counts['duplicate_normalizations']+=1
            sortedcert,sm=normalize_certificate(old,ordered=True)
            assert verify(sortedcert,control_goal=sm[goal],ordered=True)==accepted
            assert not verify(sortedcert,ordered=True)
            counts['ordered_normalizations']+=1
            counts['ordered_acceptance_preservations']+=int(accepted)
        counts['controls']+=1
    for last in (0,1,2,3,4,7,15,16,63,255,1023,2047):
        nodes=generated_prefix(last);assert len(nodes)==last+1
        validate_canonical(nodes,{'node_records':0});vals=native_values(nodes);assert len(set(vals))==len(vals)
        for i,(_,tag,l,r) in enumerate(nodes[1:],1):assert i==4*square_pair(l,r)+tag
        counts['generator_prefixes']+=1;counts['generated_nodes']+=len(nodes)
    for last in (0,1,2,3,4,7,15,16,63,255,1023,2047):
        nodes=generated_prefix(last,pairing='cantor')
        validate_canonical(nodes,{'node_records':0})
        assert native_values(nodes)==list(range(last+1))
        counts['cantor_generator_prefixes']+=1;counts['cantor_generated_nodes']+=len(nodes)
    rng=random.Random(20261018)
    for _ in range(300):
        nodes=[['z']]
        for i in range(1,31):
            while True:
                t,l,r=rng.randrange(4),rng.randrange(i),rng.randrange(i)
                if (t,l,r)!=(0,0,0):break
            nodes.append(['b',t,l,r])
        new,mp=normalize_arena(nodes);oldvals,newvals=native_values(nodes),native_values(new)
        assert all(oldvals[i]==newvals[j] for i,j in enumerate(mp))
        assert len(set(newvals))==len(newvals)
        ordered,order=priority_reindex(nodes)
        assert all(oldvals[i]==native_values(ordered)[j] for i,j in enumerate(order))
        counts['random_arena_denotation_checks']+=1
    # Distinct raw IDs alone do not prove disequality without canonicality.
    bad=[['z'],['b',1,0,0],['b',1,0,0]]
    assert native_values(bad)[1]==native_values(bad)[2] and 1!=2
    try:validate_canonical(bad,{'node_records':0})
    except C.Invalid:pass
    else:raise AssertionError('Duplicate gate counterexample accepted')
    # Backward distances cannot be compared as if they were absolute child IDs.
    assert 3-1!=4-1  # Same child at different current records: differing fields.
    assert 3-1==4-2  # Different children: same raw distance field.
    return dict(counts,all_passed=True,scope='Finite reference checks; general theorem in canonical_arena.md; no TM state count.')
if __name__=='__main__':
    r=tests();(HERE/'canonical_arena_results.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r,indent=2))
