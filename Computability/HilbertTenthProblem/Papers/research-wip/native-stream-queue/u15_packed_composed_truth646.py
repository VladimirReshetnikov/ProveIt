"""Guarded composition of relabel652 and computed-truth647: complete 403/646.

The signed graph identity concerns the freshly tagged relabel652 parent.
The old untagged baseline is related only after refreshing native extensions.
"""
from __future__ import annotations
import argparse
import ast
from copy import deepcopy
from functools import lru_cache
import hashlib
import importlib.util
import itertools
import json
from pathlib import Path
import random
from types import SimpleNamespace

BASELINE_FILE='u15_packed_two_tape_history.py'
BASELINE_SHA256='ada8106314bffe545cc106ca66b737d48398d6288f3d86cfaf602e58d0e1c318'
RELABEL_FILE='u15_packed_state_relabel652.py'
RELABEL_SHA256='cd3904fb083d1a254461ffde87636a6b9014bcdecb1db48cfcf2f30f41493879'
TRUTH_FILE='u15_packed_computed_truth647.py'
TRUTH_SHA256='c363ea0679825559d5247608f748d877e75146dbb997b159db42294d9d676eb7'
SWAP=(0,9,2,3,4,5,6,7,8,1,10,11,12,13,14)
TRUTH_FIELDS=('native__F0','native__F1','native__F2')


def _flag(value,name='ordinary'):
    if type(value) is not bool:raise ValueError(name+' must be Boolean')
    return value


def _paths(root=None):
    here=Path(__file__).resolve().parent
    root=here if root is None else Path(root).resolve()
    paths={'baseline':root/BASELINE_FILE}
    for key,name in (('relabel',RELABEL_FILE),('truth',TRUTH_FILE)):
        paths[key]=here/name if (here/name).is_file() else root/name
    for key,expected in (('baseline',BASELINE_SHA256),('relabel',RELABEL_SHA256),('truth',TRUTH_SHA256)):
        if not paths[key].is_file() or hashlib.sha256(paths[key].read_bytes()).hexdigest()!=expected:
            raise ValueError('Pinned '+key+' source changed or missing')
    return root,paths


def _load(path,name):
    spec=importlib.util.spec_from_file_location(name,path)
    module=importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


@lru_cache(None)
def _bundle(root_text,relabel_text,truth_text):
    root,paths=_paths(root_text)
    assert str(paths['relabel'])==relabel_text and str(paths['truth'])==truth_text
    relabel=_load(paths['relabel'],'_u15_composed646_relabel')
    truth=_load(paths['truth'],'_u15_composed646_truth')
    # The relabel parent's context isolates every sibling import and restores
    # preloaded module objects. The truth parent additionally authenticates both
    # complete actual baseline packets with its fixed exact-type hashes.
    with relabel.parent_module(root) as (baseline,base_tree,sha):
        assert sha==BASELINE_SHA256
        old={o:truth.checked(truth.build(o)) for o in (False,True)}
        rel={o:relabel.checked(relabel.build(o,root=root),root=root) for o in (False,True)}
        assert all(tuple(p['state_relabel'])==SWAP for p in rel.values())
        hashes=tuple(truth._packet_hash(rel[o]) for o in (False,True))
        adapter=SimpleNamespace(build=lambda ordinary=False:deepcopy(rel[_flag(ordinary)]),finish=baseline.finish)
        env=dict(truth.__dict__)
        env.update(_parent_module=lambda:adapter,PARENT_SHA256=RELABEL_SHA256,PARENT_PACKET_SHA256=hashes)
        tree=ast.parse(paths['truth'].read_bytes())
        defs=[deepcopy(next(n for n in tree.body if isinstance(n,ast.FunctionDef) and n.name==name))
              for name in ('_tagged','_child')]
        module=ast.Module(body=defs,type_ignores=[]);ast.fix_missing_locations(module)
        exec(compile(module,'<pinned647 transforms on canonical652>','exec'),env)
        tagged={o:deepcopy(env['_tagged'](o)) for o in (False,True)}
        child={o:deepcopy(env['_child'](o)) for o in (False,True)}
        lineage={'baseline':{'file':BASELINE_FILE,'sha256':BASELINE_SHA256},
                 'relabel':{'file':RELABEL_FILE,'sha256':RELABEL_SHA256},
                 'truth_projection':{'file':TRUTH_FILE,'sha256':TRUTH_SHA256}}
        for o in (False,True):
            for p in (tagged[o],child[o]):p['composition_lineage']=deepcopy(lineage)
            tagged[o]['composition_kind']='relabelled_tagged_parent'
            child[o]['composition_kind']='relabelled_computed_truth'
            child[o]['relation_to_647']='Same complete supplied-positive zero set by the B/J state permutation; new tagged native ports and computed truth fields are identical.'
            assert child[o]['ledger']['polynomial']['operations']==(646 if o else 403)
        return dict(child=child,tagged=tagged,old647=old,relabeled=rel,
                    truth=truth,relabel=relabel,baseline=baseline)


def _context(root=None):
    root,paths=_paths(root)
    return root,_bundle(str(root),str(paths['relabel']),str(paths['truth']))


def build(ordinary=False,*,root=None):
    ordinary=_flag(ordinary);_,bundle=_context(root)
    return deepcopy(bundle['child'][ordinary])


def tagged_parent(ordinary=False,*,root=None):
    ordinary=_flag(ordinary);_,bundle=_context(root)
    return deepcopy(bundle['tagged'][ordinary])


def _checked(packet,kind,root):
    _,bundle=_context(root)
    if type(packet) is not dict:raise ValueError('Complete canonical packet required')
    ordinary=_flag(packet.get('ordinary'))
    if not bundle['truth'].exact(packet,bundle[kind][ordinary]):raise ValueError('Noncanonical composition packet')
    return packet,bundle


def checked(packet,*,root=None):return _checked(packet,'child',root)[0]
def checked_tagged_parent(packet,*,root=None):return _checked(packet,'tagged',root)[0]


def polynomial_source(packet,*,root=None):return deepcopy(checked(packet,root=root)['polynomial_source'])


def evaluate(packet,values,*,signed=False,root=None):
    p,b=_checked(packet,'child',root);t=b['truth'];v=t._assignment(p,values,signed)
    return t._execute(p['polynomial_source'],v)[p['output']]


def evaluate_tagged_parent(packet,values,*,signed=False,root=None):
    p,b=_checked(packet,'tagged',root);t=b['truth'];v=t._assignment(p,values,signed)
    return t._execute(p['polynomial_source'],v)[p['output']]


def lift_to_tagged_parent(packet,values,*,signed=False,root=None):
    p,b=_checked(packet,'child',root);t=b['truth'];v=t._assignment(p,values,signed)
    env=t._execute(p['source'],v)
    if not signed:t._pretyping_guard(p,env)
    restored=dict(v,**{n:env[n] for n in TRUTH_FIELDS})
    return t._assignment(b['tagged'][p['ordinary']],restored,signed)


def project_from_tagged_parent(packet,values,*,signed=False,root=None):
    p,b=_checked(packet,'child',root);t=b['truth'];old=b['tagged'][p['ordinary']]
    v=t._assignment(old,values,signed);env=t._execute(old['source'],v)
    if not signed:t._pretyping_guard(old,env)
    if any(t._at(env,a)!=t._at(env,c) for a,c in t.REMOVED_COMPARISONS):
        raise ValueError('Tagged assignment is outside the computed truth-field graph')
    return {n:v[n] for n in p['parameters']+p['auxiliaries']}


def _graph_symbolic(child,parent,truth):
    nodes={}
    def intern(key):
        if key not in nodes:nodes[key]=len(nodes)
        return nodes[key]
    def source(packet,override=None):
        env={} if override is None else dict(override)
        def get(v):
            if type(v) is int:return intern(('constant',v))
            return env[v] if v in env else intern(('variable',v))
        for name,op,a,b in packet['source']:
            x,y=get(a),get(b)
            if op in ('+','*') and x>y:x,y=y,x
            env[name]=intern((op,x,y))
        return env,[(get(a),get(b)) for a,b in packet['comparisons']]
    ce,cc=source(child);pe,pc=source(parent,{n:ce[n] for n in TRUTH_FIELDS})
    removed=set(truth.REMOVED_ROWS);kept=0
    for n,op,a,b in parent['source']:
        if n not in removed:assert ce[n]==pe[n];kept+=1
    kept_comparisons=[p for row,p in zip(parent['comparisons'],pc) if row not in truth.REMOVED_COMPARISONS]
    assert cc==kept_comparisons
    # The three eliminated rows vanish by an exact affine identity in opaque
    # ports A,M,Z,q. This avoids expanding astronomical native polynomials.
    def add(a,b,sign=1):
        out=dict(a)
        for k,v in b.items():out[k]=out.get(k,0)+sign*v
        return {k:v for k,v in out.items() if v}
    env={k:{k:1} for k in ('native__padded_A','native__padded_B','native__F3','native__q')}
    get=lambda x:({'':x} if x else {}) if type(x) is int else env[x]
    for n,op,a,b in child['computed_definitions']:
        assert op=='-';env[n]=add(get(a),get(b),-1)
    for n,op,a,b in parent['source']:
        if n in removed:
            assert op in ('+','-');env[n]=add(get(a),get(b),1 if op=='+' else -1)
    for a,b in truth.REMOVED_COMPARISONS:assert add(get(a),get(b),-1)=={}
    return dict(identical_restored_registers=kept,identical_retained_comparisons=len(cc),
                exactly_zero_deleted_comparisons=3,expression_nodes=len(nodes))


def verify(root=None):
    if not __debug__:raise RuntimeError('Assertions required for research replay')
    root,bundle=_context(root);t=bundle['truth'];rel=bundle['relabel'];base=bundle['baseline']
    rng=random.Random(6461503);counts=dict(exact_graph_forms=0,exact_relabel_forms=0,
        complete_graph_identities=0,signed_graph_identities=0,complete_relabel_corrections=0,
        positive_outer_restorations=0,public_guard_rejections=0,cache_copy_checks=0,cold_import_isolation_checks=0)
    symbolic=[];records=[]
    def reject(call):
        try:call()
        except (ValueError,TypeError,KeyError):counts['public_guard_rejections']+=1;return
        raise AssertionError('Malformed public object accepted')
    for ordinary in (False,True):
        p=build(ordinary,root=root);tag=tagged_parent(ordinary,root=root);old=bundle['old647'][ordinary]
        graph=_graph_symbolic(p,tag,t);change=rel._symbolic_rows(old,p)
        assert p['parameters']==old['parameters'] and p['auxiliaries']==old['auxiliaries']
        assert graph['identical_retained_comparisons']==(46 if ordinary else 11)
        for field in TRUTH_FIELDS:
            assert field not in p['auxiliaries'] and field in tag['auxiliaries']
        for key in ('equations','positive_witnesses','formal_degree_upper_bound','exact_degree_claimed'):
            assert p['ledger'][key]==old['ledger'][key]
        assert p['ledger']['polynomial']['operations']==old['ledger']['polynomial']['operations']-1
        columns_old=rel._linear_columns(old);columns_new=rel._linear_columns(p)
        for name,wanted in (('Q',{'':-8,'edge2':8,'edge3':8,'edge18':-8}),
                            ('N',{'':-8,'edge0':8,'edge23':8,'edge17':-8})):
            delta={k:columns_new[name].get(k,0)-columns_old[name].get(k,0)
                   for k in set(columns_old[name])|set(columns_new[name])}
            assert {k:v for k,v in delta.items() if v}==wanted
        counts['exact_graph_forms']+=1;counts['exact_relabel_forms']+=1
        names=p['parameters']+p['auxiliaries']
        index=change['state_comparison_index']
        for case in range(64):
            values={n:rng.randrange(-3,5) if case>=32 else rng.randrange(1,6) for n in names}
            restored=lift_to_tagged_parent(p,values,signed=True,root=root)
            assert project_from_tagged_parent(p,restored,signed=True,root=root)==values
            pe=t._execute(p['polynomial_source'],values);te=t._execute(tag['polynomial_source'],restored)
            oe=t._execute(old['polynomial_source'],values)
            assert pe[p['output']]==te[tag['output']]==evaluate(p,values,signed=True,root=root)
            assert evaluate_tagged_parent(tag,restored,signed=True,root=root)==pe[p['output']]
            R=t._at(oe,old['comparisons'][index][0])-t._at(oe,old['comparisons'][index][1])
            B=t._at(oe,old['registers']['B']);P=t._at(oe,old['registers']['P']);E=lambda i:values['edge'+str(i)]-1
            delta=8*(B*(E(0)+E(23)-E(17))-(E(2)+E(3)-E(18))+P)
            assert pe[p['output']]-oe[old['output']]==delta*(2*R+delta)
            assert all(t._at(te,a)==t._at(te,b) for a,b in t.REMOVED_COMPARISONS)
            counts['complete_graph_identities']+=1;counts['signed_graph_identities']+=case>=32
            counts['complete_relabel_corrections']+=1
        one={n:1 for n in names}
        for n in names:
            for badval in (True,1.0,0 if n in p['auxiliaries'] or ordinary else -1):
                bad=dict(one);bad[n]=badval;reject(lambda bad=bad:evaluate(p,bad,root=root))
        for packet,check in ((p,checked),(tag,checked_tagged_parent)):
            for field in ('source','polynomial_source'):
                for i,row in enumerate(packet[field]):
                    for slot in (2,3):
                        if type(row[slot]) is int:
                            bad=deepcopy(packet);r=list(row);r[slot]=float(r[slot]);bad[field][i]=tuple(r)
                            reject(lambda bad=bad,check=check:check(bad,root=root))
            bad=deepcopy(packet);bad['state_relabel'][1]=9.0;reject(lambda bad=bad,check=check:check(bad,root=root))
        reject(lambda:lift_to_tagged_parent(p,one,root=root))
        restored=lift_to_tagged_parent(p,one,signed=True,root=root);restored['native__F1']+=1
        reject(lambda:project_from_tagged_parent(p,restored,signed=True,root=root))
        for flag in (0,1,None,'False'):
            reject(lambda flag=flag:build(flag,root=root));reject(lambda flag=flag:tagged_parent(flag,root=root))
            reject(lambda flag=flag:evaluate(p,one,signed=flag,root=root))
        for getter in (build,tagged_parent):
            snap=getter(ordinary,root=root);bad=getter(ordinary,root=root);bad['source'].clear();bad['composition_lineage'].clear()
            assert t.exact(getter(ordinary,root=root),snap);counts['cache_copy_checks']+=1
        exposed=polynomial_source(p,root=root);exposed.clear();assert polynomial_source(p,root=root)==p['polynomial_source'];counts['cache_copy_checks']+=1
        symbolic.append(dict(ordinary=ordinary,graph=graph,relabel=change))
        records.append(dict(ordinary=ordinary,ledger=p['ledger'],tagged_parent_ledger=tag['ledger']))
    # Exercise the composition's actual cold dependency chain, not only the
    # isolated parent in a separate test. Caller module identities are restored.
    import sys,types
    loader_name='u15_raw_half_tape_loader';previous=sys.modules.get(loader_name)
    poisoned=deepcopy(base.loader.build(False))
    idx=next(i for i,r in enumerate(poisoned['source']) if r[0]=='raw_Q_term')
    row=list(poisoned['source'][idx]);row[2]='program_B';poisoned['source'][idx]=tuple(row)
    reference=build(True,root=root)
    for foreign_file in (None,'/foreign/root/u15_raw_half_tape_loader.py'):
        fake=types.ModuleType(loader_name)
        if foreign_file is not None:fake.__file__=foreign_file
        fake.build=lambda scaled=False:deepcopy(poisoned)
        _bundle.cache_clear();sys.modules[loader_name]=fake
        try:
            assert t.exact(build(True,root=root),reference)
            assert sys.modules[loader_name] is fake
            counts['cold_import_isolation_checks']+=1
        finally:
            if previous is None:sys.modules.pop(loader_name,None)
            else:sys.modules[loader_name]=previous
            _bundle.cache_clear()
    examples=[];p=build(root=root)
    for L,R in itertools.product(range(16),range(12)):
        result=base.trace(L,R,40)
        if result is None:continue
        original,meta=base.outer_fixture(L,R,40)
        values={n:original[n] for n in p['parameters']+p['auxiliaries']}
        lifted=lift_to_tagged_parent(p,values,root=root)
        assert project_from_tagged_parent(p,lifted,root=root)==values
        env=t._execute(p['source'],values);reg=p['tag_registers'];val=lambda n:t._at(env,reg[n])
        assert val('A')&val('M')==val('Z') and max(val('A'),val('M'))<val('cap')
        assert min(lifted[n] for n in TRUTH_FIELDS)>0
        assert all(t._at(env,a)==t._at(env,b) for a,b in p['comparisons'][:5])
        counts['positive_outer_restorations']+=1
        if len(examples)<6:examples.append(dict(L=L,R=R,duration=meta['t']))
    return dict(status='PASS',source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        lineage=build(root=root)['composition_lineage'],counts=counts,ledgers=records,symbolic_source_audits=symbolic,
        examples=examples,complete_raw_compiler=build(root=root),complete_ordinary_compiler=build(True,root=root),
        complete_raw_tagged_parent=tagged_parent(root=root),complete_ordinary_tagged_parent=tagged_parent(True,root=root),
        scope='Exact full signed graph identity to the freshly tagged relabel652 parent; same supplied-positive zero set as647. Relation to the untagged652 baseline refreshes all native auxiliaries. Outer fixtures are not materialized Pell zeros; inherited1936 is a formal upper bound.')


def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--root',type=Path);ap.add_argument('--write',action='store_true');args=ap.parse_args()
    result=verify(args.root);path=Path(__file__).with_suffix('.json');wire=json.dumps(result,indent=2)+'\n'
    if args.write:path.write_text(wire)
    else:
        _,bundle=_context(args.root)
        assert bundle['truth'].exact(json.loads(path.read_text()),json.loads(wire))
    print(json.dumps({k:result[k] for k in ('status','counts','ledgers','symbolic_source_audits')},indent=2))


if __name__=='__main__':main()
