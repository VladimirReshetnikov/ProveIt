#!/usr/bin/env python3
"""Reconstruct three joint-forest machines from the literal AX11H parent.

Python 3.10+, standard library. Assertions are part of the finite certificate.
This is not a proof-assistant kernel. The written iPRA argument is in report/.
"""
from pathlib import Path
import argparse,collections,hashlib,json,sys
HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE/'vendor'))
import compiler as c
import support as s

INC=('leaf','inc',1)

def tup(x):
    return tuple(map(tup,x)) if isinstance(x,list) else x

def dump(path,obj):
    path.write_text(json.dumps(obj,indent=2)+'\n')

def reachable(rows):
    seen,todo={74},[74]
    for q in todo:
        for bit in (0,1):
            target=rows[q,bit][2]
            if target!=254 and target not in seen:
                seen.add(target);todo.append(target)
    return {key:value for key,value in rows.items() if key[0] in seen}

def history_folds(rows):
    """Propose one-step/three-step folds, then check every simultaneous case."""
    incoming=collections.defaultdict(list)
    for key,action in rows.items():
        incoming[action[2]].append((key,action))
    candidates=c.opportunities_fast(rows,{q:None for q,_ in rows})
    candidates=[(a,b,opts) for a,b,opts in candidates
                if all(v[1] and v[0]==k[1]
                       for q in (a,b) for k,v in incoming[q])]
    # The source search uses sorted native labels, so preserve that convention.
    candidates.sort(key=lambda x:(x[0],x[1]))
    choices={(a,b):opts for a,b,opts in candidates}
    pairs=c.max_matching(candidates)
    folds=[[a,b,[opts[0] for opts in choices[a,b]]] for a,b in pairs]
    child,aliases=s.apply_folds(rows,folds)
    local=s.check_local_folds(rows,child,aliases,folds)
    return child,folds,local

def build(name,destination):
    if not __debug__ or sys.flags.optimize:
        raise SystemExit('Do not use Python -O: assertions check the certificate.')
    config=json.loads((HERE/'specifications.json').read_text())[name]
    original=s.read_table(HERE/'inputs/parent.native.tm')
    oldnodes={key:tup(value) for key,value in
              json.loads((HERE/'inputs/nodes.json').read_text()).items()}
    grammar=c.read_grammar(HERE/'inputs/grammar.json')
    c.raw_nodes=lambda:oldnodes
    oldsites,oldinstructions,_=c.source(grammar)
    nodes=dict(oldnodes)
    for key in ('node75','node164','node62'):
        nodes[key]=tup(config[key])
    c.raw_nodes=lambda:nodes

    # Replace exactly the three closed source routines. Control 92 remains
    # a separate history entry; removing it is the rejected ORH193 shortcut.
    removed={92,185,213,100,174,164,139,190}
    fixed={key:value for key,value in original.items()
           if key[0]<1300 and key[0] not in removed}
    fixed.update({(69,0):(0,False,92),(92,0):(0,True,111),
                  (92,1):(1,True,90)})
    atoms={'node32':104,'node53':107,'node55':98,'node65':90,
           'node37':28,'node6':77,'node54':114,INC:61}
    compiled={};fresh=330

    def state(tree):
        nonlocal fresh
        if tree in atoms:return atoms[tree]
        if tree in compiled:return compiled[tree]
        assert c.isnode(tree)
        def action(child,bit):
            if isinstance(child,tuple) and child[0]=='leaf' and child[1]=='continueTo':
                assert child[2] in (2,3)
                return (0,False,16) if child[2]==2 else (1,False,73)
            return bit,True,state(child)
        pair=action(tree[0],0),action(tree[1],1)
        for q,_ in fixed:
            if (fixed[q,0],fixed[q,1])==pair:
                compiled[tree]=q;return q
        q=fresh;fresh+=1
        fixed[q,0],fixed[q,1]=pair
        compiled[tree]=q
        return q

    operand=state(nodes['node75']);atoms['node75']=operand
    mp=state(nodes['node164']);loop=state(nodes['node62'])
    fixed[96,1]=(1,True,mp);fixed[125,1]=(1,True,loop)
    c.MACROS={'node65':90,'node55':98,'node58':12,'node70':166,
              'node49':19,'node72':69,'node75':operand,'node142':194,
              'node150':221,INC:61,'node60':99,(INC,INC):99}
    c.MACROS.update(compiled)
    c.machine=lambda:(fixed,[])
    raw,index,shape=c.build(grammar)
    raw=reachable(raw)
    child,folds,local=history_folds(raw)
    sites,instructions,contracts=c.source(grammar)
    assert instructions==oldinstructions
    assert len(sites)==3671 and len(contracts)==4778
    assert max(len(path) for path,_,_ in sites)<=48
    runtime=c.validate(child,contracts)
    assert runtime['ok'],runtime
    startup=s.startup(child,sites[25][0])
    dense,labels=s.dense_table(child,194)
    digest=hashlib.sha256(s.table_text(dense).encode()).hexdigest()
    assert digest==config['expected_sha256'],(name,digest)
    folder=destination/name;folder.mkdir(parents=True,exist_ok=True)
    for filename,table in [('machine.tm',dense),('machine.native.tm',child),
                           ('raw.native.tm',raw)]:
        (folder/filename).write_text(s.table_text(table))
    for filename,value in [('nodes.json',nodes),('grammar.tree.json',grammar),
                           ('macro_bindings.json',list(c.MACROS.items())),
                           ('instructions.json',instructions),('folds.json',folds),
                           ('local.json',local),('labels.json',labels),
                           ('sites.json',[[''.join(map(str,p)),op,a] for p,op,a in sites])]:
        dump(folder/filename,value)
    receipt={'name':name,'search_family':config['search_family'],
             'working_states':194,'transition_rows':388,'raw_states':len(raw)//2,
             'fixed_states':sum(b==0 and q<1300 for q,b in raw),
             'reader_states':len(shape),'folds':len(folds),
             'source_sites':len(sites),'source_outcomes':len(contracts),
             'source_graph_identical':True,
             'changed_addresses':sum(a[0]!=b[0] for a,b in zip(sites,oldsites)),
             'maximum_address_length':max(len(p) for p,_,_ in sites),
             'runtime':runtime,'startup':startup,'dense_sha256':digest,
             'scope':'Construction certificate; independent literal replay and written iPRA proof are separate.'}
    dump(folder/'receipt.json',receipt)
    print(json.dumps({key:receipt[key] for key in
                     ('name','working_states','raw_states','fixed_states','reader_states',
                      'folds','changed_addresses','maximum_address_length','dense_sha256')}),flush=True)
    return receipt

if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path,default=HERE.parent/'machines')
    parser.add_argument('--name',choices=('PA194ForestR','PA194ForestB','PA194ForestX'))
    args=parser.parse_args()
    for name in ([args.name] if args.name else ('PA194ForestR','PA194ForestB','PA194ForestX')):
        build(name,args.output)
