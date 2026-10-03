"""Targeted independent addendum; checks remain live under python -O."""
import copy
import hashlib
import json
from pathlib import Path
import sys
import time
import lazy_reversible as lazy
ref=lazy.ref
ROOT=Path(__file__).resolve().parent
EXPECTED='42e8aa65c05fcf373a03a02be51ebb89a4fdcb1f1070ad776ffe1e8e99049c61'


def require(value, detail='check failed'):
    if not value:
        raise AssertionError(detail)


def row(name='e',q='q',target='h',side=1,delta=1,guard=None):
    return dict(name=name,source=q,target=target,side=side,delta=delta,
                guard={'op':'true'} if guard is None else guard)


def source(J=0,rows=None,controls=None):
    return dict(schema='reversible-two-counter-v1',controls=['q','h'] if controls is None else controls,
                start='q',halt='h',class_cut=J,branches=[row()] if rows is None else rows)


def atom(op,j,k):
    return {'op':op,'counter':j,'value':k}


class ListSubclass(list): pass
class DictSubclass(dict): pass
class StrSubclass(str): pass
class IntSubclass(int): pass


def main():
    start=time.perf_counter()
    digest=hashlib.sha256(Path(lazy.__file__).read_bytes()).hexdigest()
    require(digest==EXPECTED,'core implementation changed')
    counts=dict(source_outcomes=0,accepted_large_J_sources=0,large_J_gate_bounds=0,
                endpoint_pairs=0,guard_patterns=0,malformed_schema_cases=0,overlap_precedence_cases=0)
    failures=[]
    observed=[]

    def compare(data,label):
        outcomes=[];compiled=[]
        for compiler in (ref.compile_source,lazy.compile_lazy_source):
            try:
                result=compiler(data)
            except Exception as e:
                outcomes.append((type(e).__name__,str(e)));compiled.append(None)
            else:
                outcomes.append(('accepted',));compiled.append(result)
        require(outcomes[0]==outcomes[1],(label,outcomes))
        counts['source_outcomes']+=1
        if compiled[0] is not None:
            c,l=compiled
            require(c.ledger()==l.ledger(),label)
            require(c.branches==l.branches,label)
            require(c.source_data==l.source_data,label)
        observed.append(dict(case=label,outcome=list(outcomes[0])))
        return compiled

    for J in (17,64):
        for side in (-1,1):
            j=int(side==1)
            guards=[
                ('inc_eq_max_image',1,atom('eq',j,J-1)),
                ('inc_gt_max_image',1,atom('gt',j,J-1)),
                ('inc_other_cut',1,atom('eq',1-j,J)),
                ('dec_eq_cut',-1,atom('eq',j,J)),
                ('dec_gt_cut',-1,atom('gt',j,J)),
                ('dec_compound',-1,{'op':'and','args':[atom('gt',j,0),{'op':'not','arg':atom('eq',j,J)}]}),
                ('direct_nested',0,{'op':'and','args':[{'op':'or','args':[atom('eq',0,0),atom('gt',0,J)]},{'op':'not','arg':atom('eq',1,J)}]}),
                ('true_increment',1,{'op':'true'})]
            for name,delta,guard in guards:
                c,l=compare(source(J,[row(side=side,delta=delta,guard=guard)]),f'J{J}:{side}:{name}')
                require(c is not None)
                counts['accepted_large_J_sources']+=1
                for i,g in enumerate(c.E+c.P):
                    require(g==l.gate_at(i),(J,i))
                    require(g.B<=c.B3)
                    for shape in g.shapes:
                        require(all(-g.B<=p<=g.B for p in shape))
                    require(len(g.P)==len(g.Q))
                    for p in g.P:
                        for q in g.Q:
                            require(abs(q-p)<=2*c.B3,(g.name,p,q))
                            counts['endpoint_pairs']+=1
                    counts['large_J_gate_bounds']+=1
            # Finite explicit threshold failures include dead predicates: validation is syntactic here.
            invalid=[('atom_above_cut',0,atom('eq',j,J+1)),
                     ('image_cut_eq',1,atom('eq',j,J)),
                     ('image_cut_gt',1,atom('gt',j,J)),
                     ('dead_image_cut',1,{'op':'and','args':[{'op':'or','args':[]},atom('eq',j,J)]}),
                     ('negative_post',-1,{'op':'true'})]
            for name,delta,guard in invalid:
                c,l=compare(source(J,[row(side=side,delta=delta,guard=guard)]),f'J{J}:{side}:{name}')
                require(c is None)

        c,l=compare(source(J),f'J{J}:guard_probe_source')
        g=next(g for g in c.E if g.name=='dispatch:e')
        require(g.guard is not None and all(all(r) for r in g.guard.table))
        choices=[(),(0,),(J,),(J//2,),(0,J),(1,J-1),(0,1),(-1,),(J+1,),(-1,J+1),(0,J+1),(J,-1)]
        for u in (-10**50,0,10**70):
            for left in choices:
                for right in choices:
                    x=frozenset([u-g.guard.Z-k for k in left]+[u+g.guard.Z+k for k in right])
                    count_l=len({k for k in left if 0<=k<=J})
                    count_r=len({k for k in right if 0<=k<=J})
                    expected=count_l<=1 and count_r<=1
                    a=g.guard.allows(x,u);b=lazy._guard_sparse(g.guard,sorted(x),u)
                    require(a==b==expected,(J,u,left,right,a,b,expected))
                    counts['guard_patterns']+=1
        # Largest class bit, simultaneous domain/image tie, and image-earlier-than-domain precedence.
        high={'op':'and','args':[atom('gt',0,J),atom('gt',1,J)]}
        overlap_cases=[
            [row('a',delta=0,guard=high),row('b',delta=0,guard=high)],
            [row('a',target='q',delta=0,guard=atom('eq',0,J)),row('b',target='q',delta=0,guard=atom('eq',0,J))],
            [row('a',q='r',target='q',delta=0,guard=atom('eq',0,0)),row('b',q='r',target='q',delta=0,guard=atom('eq',0,0)),
             row('c',q='q',target='h',delta=0,guard=atom('eq',0,J)),row('d',q='q',target='h',delta=0,guard=atom('eq',0,J))]]
        for i,rows in enumerate(overlap_cases):
            c,l=compare(source(J,rows,['q','r','h']),f'J{J}:overlap_order:{i}')
            require(c is None)
            counts['overlap_precedence_cases']+=1

    base=source(0,[row(delta=0)])
    malformed=[]
    def alter(label,path,value):
        d=copy.deepcopy(base);obj=d
        for k in path[:-1]:obj=obj[k]
        obj[path[-1]]=value
        malformed.append((label,d))
    for label,obj in [('root_dict_subclass',DictSubclass(base)),('root_list',[]),('root_string','source'),('root_bool',False),('root_none',None)]:
        malformed.append((label,obj))
    for field,values in [
        ('schema',[StrSubclass('reversible-two-counter-v1'),True,0]),
        ('controls',[ListSubclass(['q','h']),('q','h'),'qh']),
        ('start',[StrSubclass('q'),False]),('halt',[StrSubclass('h'),False]),
        ('class_cut',[IntSubclass(0),False,0.0]),
        ('branches',[ListSubclass(base['branches']),tuple(base['branches']),{}])]:
        for i,value in enumerate(values):alter(f'{field}:{i}',[field],value)
    alter('control_string_subclass',['controls',0],StrSubclass('q'))
    alter('control_bool',['controls',0],False)
    alter('row_dict_subclass',['branches',0],DictSubclass(base['branches'][0]))
    for field in ('name','source','target'):
        alter(f'row:{field}:str_subclass',['branches',0,field],StrSubclass(base['branches'][0][field]))
        alter(f'row:{field}:bool',['branches',0,field],False)
    for field in ('side','delta'):
        for name,value in [('int_subclass',IntSubclass(base['branches'][0][field])),('bool',True),('float',1.0)]:
            alter(f'row:{field}:{name}',['branches',0,field],value)
    malformed.append(('root_string_key_subclass',{StrSubclass(k):v for k,v in base.items()}))
    d=copy.deepcopy(base);d['branches'][0]={StrSubclass(k):v for k,v in d['branches'][0].items()};malformed.append(('row_string_key_subclass',d))
    guard_cases=[DictSubclass(op='true'),{'op':StrSubclass('true')},{StrSubclass('op'):'true'},
                 {'op':'and','args':ListSubclass([])},{'op':'or','args':()}, {'op':'not','arg':True},
                 {'op':'eq','counter':True,'value':0},{'op':'eq','counter':IntSubclass(0),'value':0},
                 {'op':'gt','counter':0,'value':False},{'op':'gt','counter':0,'value':IntSubclass(0)},
                 {'op':'true','extra':1},{'op':'unknown'},{}]
    for i,g in enumerate(guard_cases):alter(f'guard_malformed:{i}',['branches',0,'guard'],g)
    d=copy.deepcopy(base);d['extra']=0;malformed.append(('extra_root_key',d))
    d=copy.deepcopy(base);del d['class_cut'];malformed.append(('missing_root_key',d))
    cycle={'op':'not'};cycle['arg']=cycle
    d=copy.deepcopy(base);d['branches'][0]['guard']=cycle;malformed.append(('guard_cycle',d))
    for label,data in malformed:
        c,l=compare(data,label);require(c is None,label)
        counts['malformed_schema_cases']+=1
    # Bool is non-subclassable in Python; exact bool objects above exercise bool-vs-int rejection.
    bool_subclass_rejected=False
    try:type('BoolSubclass',(bool,),{})
    except TypeError:bool_subclass_rejected=True
    require(bool_subclass_rejected)
    # A malformed last row must win over an earlier domain/image overlap.
    for J in (0,17,64):
        for i,bad in enumerate([row('bad',side=True),row('bad',guard=DictSubclass(op='true')),row('bad',guard={'op':'eq','counter':0,'value':True})]):
            c,l=compare(source(J,[row('a',delta=0),row('b',delta=0),bad]),f'J{J}:malformed_after_overlap:{i}')
            require(c is None)
            counts['overlap_precedence_cases']+=1
    require(hashlib.sha256(Path(lazy.__file__).read_bytes()).hexdigest()==EXPECTED,'core changed during audit')
    receipt=dict(status='passed',lazy_sha256=digest,frozen_sha256=lazy.FROZEN_SHA256,
                 optimization_level=sys.flags.optimize,tested_J=[0,17,64],counts=counts,
                 bool_subclass_construction_rejected=bool_subclass_rejected,
                 exception_and_acceptance_cases=observed,
                 elapsed_seconds=time.perf_counter()-start)
    target=ROOT/('addendum-receipt-optimized.json' if sys.flags.optimize else 'addendum-receipt.json')
    target.write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps({k:v for k,v in receipt.items() if k!='exception_and_acceptance_cases'},indent=2))

if __name__=='__main__':main()
