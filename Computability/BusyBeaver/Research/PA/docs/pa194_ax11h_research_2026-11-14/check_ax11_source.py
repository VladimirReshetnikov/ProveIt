#!/usr/bin/env python3
"""Independent tree expansion, CFG resolution, and two-splice source binding."""
from pathlib import Path
import sys,json,argparse,tempfile
ROOT=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT/'verification/reference'))
import source_language as language

def tup(x):return tuple(map(tup,x)) if isinstance(x,list) else x

def gram(path):
    obj=json.loads(path.read_text());rules=obj['rules']
    def expand(t):
        if isinstance(t,str) and t in rules:return tuple(expand(x)for x in rules[t])
        return tup(t)
    return expand(obj['root'])

def graph(sites):
    names={'inc':'CI','dec':'CD','breakTo':'CB','continueTo':'CC','halt':'CH'}
    mapped=[[p,names[op],a]for p,op,a in sites]
    a,_=language.graph_arithmetic(mapped);b=language.graph_intervals(mapped)
    assert a==b
    ops={'identity':'jump','increment':'inc','decrement':'dec','halt':'halt'}
    return [[ops[e[0]]]+e[1:]+targets for e,targets in a]

def bind(machine):
    nodes={k:tup(v)for k,v in json.loads((ROOT/'inputs/primary.nodes.json').read_text()).items()}
    base=gram(ROOT/'inputs/primary.grammar.json')
    visits={}
    def expand(t,p,ns,g,sites,record=False):
        if isinstance(t,str):
            if record:visits.setdefault(t,[]).append(p)
            return expand(g if t=='x67' else ns[t],p,ns,g,sites,record)
        if t[0]=='leaf':sites.append([''.join(map(str,p)),t[1],t[2]]);return
        assert len(t)==2
        expand(t[0],p+(0,),ns,g,sites,record);expand(t[1],p+(1,),ns,g,sites,record)
    old=[];expand('node172',(),nodes,base,old,True)
    assert old==json.loads((ROOT/'inputs/primary.sites.json').read_text())
    oldins=graph(old);assert oldins==json.loads((ROOT/'inputs/primary.instructions.json').read_text())
    def replace(t):
        if t==('leaf','breakTo',1):return 'node49'
        return tuple(map(replace,t))if isinstance(t,tuple)and len(t)==2 else t
    newnodes=dict(nodes);newnodes['node163']=('node6','node54')
    newg=replace(base);new=[];expand('node172',(),newnodes,newg,new)
    assert newnodes=={k:tup(v)for k,v in json.loads((machine/'nodes.json').read_text()).items()}
    given=json.loads((machine/'sites.json').read_text())
    given=[[''.join(map(str,p))if isinstance(p,list)else p,op,a]for p,op,a in given]
    assert new==given
    newins=graph(new);assert newins==json.loads((machine/'instructions.json').read_text())
    assert len(old)==3673 and len(new)==3672
    assert len(visits['node163'])==1 and len(visits['x67'])==1
    mp=''.join(map(str,visits['node163'][0]));ax=''.join(map(str,visits['x67'][0]))
    oldbreak=max(i for i,(p,op,a)in enumerate(old)if p.startswith(ax)and(op,a)==('breakTo',1))
    bp=old[oldbreak][0]
    removed=[i for i,(p,op,a)in enumerate(old)if p.startswith(mp+'10')]
    copy=[i for i,(p,op,a)in enumerate(old)if p.startswith(mp+'11')]
    inserted=[i for i,(p,op,a)in enumerate(new)if p.startswith(bp)]
    assert len(removed)==len(inserted)==19 and len(copy)==7
    lookup={p:i for i,(p,op,a)in enumerate(new)};relocation={}
    for i,(p,op,a)in enumerate(old):
        if i==oldbreak or i in removed:continue
        dest=mp+'1'+p[len(mp)+2:]if i in copy else p
        j=lookup[dest];relocation[i]=j;assert new[j][1:]==[op,a]
    def target(j):
        if j==oldbreak:return min(inserted)
        if j in removed:
            assert j==min(removed),'An external edge enters the removed MP push internally.'
            return relocation[min(copy)]
        return relocation[j]
    for i,j in relocation.items():
        oldcode=oldins[i];k=2 if oldcode[0]in('inc','dec')else 1
        assert oldcode[:k]+[target(x)for x in oldcode[k:]]==newins[j],(i,j)
    # The inserted node49 is exactly the deleted node49 under local relocation.
    localmap=dict(zip(removed,inserted))
    for oldi,newi in localmap.items():
        ins=oldins[oldi];k=2 if ins[0]in('inc','dec')else 1
        def relocate_push(j):
            if j in localmap:return localmap[j]
            assert j==max(removed)+1
            return relocation[oldbreak+1]
        assert ins[:k]+[relocate_push(j)for j in ins[k:]]==newins[newi]
    # Original MP field reader now immediately follows the inserted AX push.
    assert max(inserted)+1==relocation[oldbreak+1]
    # All external incoming edges into each splice target only its first site.
    for block,instructions in [(set(inserted),newins),(set(removed),oldins)]:
        entrances=[]
        for i,ins in enumerate(instructions):
            if i in block:continue
            k=2 if ins[0]in('inc','dec')else 1
            for j in ins[k:]:
                if j in block:assert j==min(block);entrances.append([i,j])
    return dict(status='PASS',old_sites=3673,new_sites=3672,unchanged_sites=len(relocation),old_AX_exit=oldbreak,new_AX_push=inserted,old_MP_dummy_push=removed,old_MP_copy=copy,new_MP_field_entry=relocation[oldbreak+1],new_AX_push_last_instruction=newins[max(inserted)],new_AX_push_exact_transplant=True,resolved_edges_preserved_modulo_two_splices=True,no_external_internal_splice_entry=True,independent_CFG_resolvers_agree=True,relocation=relocation)

if __name__=='__main__':
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--machine',type=Path,default=ROOT/'machine');ap.add_argument('--output',type=Path);a=ap.parse_args()
    result=bind(a.machine)
    out=a.output or Path(tempfile.mkdtemp(prefix='ax11-source-'))/'source_binding.json';out.parent.mkdir(parents=True,exist_ok=True)
    out.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items()if k!='relocation'},indent=2))
