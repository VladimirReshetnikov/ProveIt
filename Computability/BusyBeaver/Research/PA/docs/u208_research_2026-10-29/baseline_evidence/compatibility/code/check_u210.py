#!/usr/bin/env python3
"""Independent finite/source certificate audit for Research+Rotated U210.

Standard library only; all obligations use explicit exceptions and survive -O.
This is an ordinary mathematical certificate checker, not a proof-assistant kernel.
It checks the new eight source rotations and final two-cell fold. It does not
claim the whole unbounded primitive-runtime or inherited consistency calibration.
"""
from __future__ import annotations
import argparse
import hashlib
import json
from pathlib import Path

ROTATIONS = ((162,203),(203,223),(223,188),(188,177),
             (177,89),(89,174),(174,217),(217,163))

def require(condition, message):
    if not condition:
        raise ValueError(message)

def read_table(path):
    result={};starts=[]
    for raw in Path(path).read_text(encoding='ascii').splitlines():
        if raw.startswith('#! start '):starts.append(int(raw[9:]));continue
        if not raw or raw.startswith('#'):continue
        q,b,w,d,t=raw.split();q,b,w,t=map(int,(q,b,w,t))
        require((q,b) not in result and b in (0,1) and w in (0,1)
                and d in ('L','R'),'malformed transition')
        result[q,b]=(w,1 if d=='R' else -1,t)
    require(starts==[0],'incorrect initial state')
    return result

def census(table,count,halt):
    states={q for q,_ in table}
    require(len(states)==count and 0 in states and halt not in states,'state census')
    require(set(table)=={(q,b) for q in states for b in (0,1)},'row census')
    require({v[2] for v in table.values()}-states=={halt},'target closure')
    reached={0};pending=[0]
    for q in pending:
        for b in (0,1):
            t=table[q,b][2]
            if t!=halt and t not in reached:reached.add(t);pending.append(t)
    require(reached==states,'unreachable working state')
    return sorted(states)

def inspect_source(rows):
    require(rows and all(isinstance(r,list) and len(r)==3 for r in rows),'source rows')
    addresses=[p for p,_,_ in rows]
    require(addresses==sorted(set(addresses)),'source order or duplicate')
    leaf={p:(op,arg) for p,op,arg in rows}
    prefixes=set()
    for p,op,arg in rows:
        require(p and set(p)<={'0','1'},'binary address')
        require(op in ('CI','CD','CB','CC','CH'),'opcode')
        require((op=='CH' and arg is None) or (op!='CH' and type(arg) is int
                and arg>=0),'operand')
        require(op not in ('CI','CD') or arg<9,'register operand')
        require(op not in ('CB','CC') or arg>=1,'control depth')
        prefixes.update(p[:i] for i in range(len(p)))
    require(not prefixes.intersection(leaf),'prefix conflict')
    require(all(p+b in prefixes or p+b in leaf for p in prefixes for b in '01'),
            'incomplete source tree')
    ordinal={p:i for i,p in enumerate(addresses)}
    spans={};types={}
    def walk(p):
        if p in leaf:
            spans[p]=(ordinal[p],ordinal[p]+1);types[p]=leaf[p]
        else:
            walk(p+'0');walk(p+'1')
            x,y=spans[p+'0'],spans[p+'1']
            require(x[1]==y[0],'noncontiguous subtree')
            spans[p]=(x[0],y[1]);types[p]=(types[p+'0'],types[p+'1'])
    walk('')
    # Resolver 1: ordinal intervals selected by the indicated enclosing edge.
    n=len(rows);graph_a=[]
    for i,(p,op,arg) in enumerate(rows):
        def enclosing(edge,level):
            for j in range(len(p)-1,-1,-1):
                if p[j]==edge:
                    level-=1
                    if level==0:return spans[p[:j]][1 if edge=='0' else 0]%n
            return 0
        if op=='CI':out=((i+1)%n,)
        elif op=='CD':out=(enclosing('0',1),(i+1)%n)
        elif op=='CB':out=(enclosing('0',arg),)
        elif op=='CC':out=(enclosing('1',arg),)
        else:out=()
        graph_a.append((op,arg,out))
    # Resolver 2: increment/cut of binary addresses, then a zero-filled lookup.
    maxdepth=max(map(len,addresses));graph_b=[];resolved=0
    def locate(word):
        nonlocal resolved
        padded=word+'0'*maxdepth
        for k in range(1,maxdepth+1):
            if padded[:k] in ordinal:
                require('1' not in word[k:],'stray suffix after decoded leaf')
                resolved+=1;return ordinal[padded[:k]]
        raise ValueError('no successor leaf')
    def successor(p):
        if not p:return ''
        return format((int(p,2)+1)%(1<<len(p)),f'0{len(p)}b')
    def cut(p,edge,level):
        at=[j for j,b in enumerate(p) if b==edge]
        return p[:at[-level]] if len(at)>=level else ''
    for p,op,arg in rows:
        if op=='CI':out=(locate(successor(p)),)
        elif op=='CD':out=(locate(successor(cut(p,'0',1))),locate(successor(p)))
        elif op=='CB':out=(locate(successor(cut(p,'0',arg))),)
        elif op=='CC':out=(locate(cut(p,'1',arg)),)
        else:out=()
        graph_b.append((op,arg,out))
    require(locate('')==0,'source entry')
    require(graph_a==graph_b,'independent ordinal resolvers disagree')
    return {'prefixes':prefixes,'spans':spans,'graph':graph_a,
            'metrics':{'leaf_occurrences':n,'dag_nodes':len(set(types.values())),
                       'maximum_depth':maxdepth,
                       'maximum_zero_run':max(len(z) for p in addresses for z in p.split('1'))},
            'resolved':resolved}

def prefix_bindings(table,prefixes):
    bound={};maxsteps=0
    for word in sorted(prefixes):
        cells={-1:1,**{i:int(b) for i,b in enumerate(word)}};head=0;state=84
        for steps in range(500):
            if head==len(word):break
            require(head in cells,('opaque prefix read',word,head,state))
            bit=cells[head];w,d,state=table[state,bit]
            require(w==bit,('prefix write',word,head));head+=d
        else:raise ValueError('prefix did not finish')
        bound[word]=state;maxsteps=max(maxsteps,steps)
    return bound,maxsteps

def closed_factor(rows,prefix):
    """Leafwise closure, independently of the supplied recursive signatures."""
    selected=[(p[len(prefix):],op,arg) for p,op,arg in rows if p.startswith(prefix)]
    require(selected,'empty factor')
    for suffix,op,arg in selected:
        require(op!='CH','halt in supposedly closed factor')
        if op=='CD':require(suffix.count('0')>=1,'escaping decrement')
        if op=='CB':require(suffix.count('0')>=arg,'escaping break')
        if op=='CC':require(suffix.count('1')>=arg,'escaping continue')
    return len(selected)

def readdress(rows,roots):
    answer=[]
    for path,op,arg in rows:
        transformed=path
        for root in roots:
            if path.startswith(root):
                suffix=path[len(root):]
                if suffix.startswith('00'):transformed=root+'0'+suffix[2:]
                elif suffix.startswith('01'):transformed=root+'10'+suffix[2:]
                else:
                    require(suffix.startswith('1'),'rotation leaf shape')
                    transformed=root+'11'+suffix[1:]
                break
        answer.append([transformed,op,arg])
    return answer

def fold_paths(old,new,tag=0):
    traces=[]
    for current in (0,1):
        frame={-1:tag,0:current};w,d,t=old[218,current]
        expected=({**frame,0:w},d,t)
        tape=frame.copy();head=0;state=157;trace=[(state,head)]
        for _ in range(3):
            require(head in tape,'local proof reads opaque exterior')
            bit=tape[head];w,d,state=new[state,bit];tape[head]=w;head+=d
            require(state!=254,'intermediate halt');trace.append((state,head))
        require((tape,head,state)==expected,('local endpoint mismatch',tag,current))
        traces.append({'tag':tag,'current':current,'old_endpoint':[t,d],
                       'replacement_path':trace,'whole_frame_preserved':tape==frame})
    return traces

def fold_guard(table):
    incoming=[(key,value) for key,value in sorted(table.items()) if value[2]==218]
    require(incoming==[((158,0),(0,1,218)),((163,0),(0,1,218)),((211,0),(0,1,218))],
            'complete zero-tag incoming inventory')
    require(218!=0,'deleted state is initial')
    return incoming

def rejects(action,label):
    try:action()
    except (ValueError,KeyError,IndexError):return label
    raise ValueError('negative control was accepted: '+label)

def audit(parent_table,parent_source,prefold_path,candidate_path,source_path,dense_path=None):
    old=read_table(parent_table);census(old,211,254)
    rows=json.loads(Path(parent_source).read_text());base_info=inspect_source(rows)
    graph=base_info['graph'];table=old.copy();original_word=[r[1:] for r in rows]
    stages=[]
    for p,q in ROTATIONS:
        info=inspect_source(rows);bound,steps=prefix_bindings(table,info['prefixes'])
        roots=sorted(word for word,state in bound.items() if state==p)
        require(roots,'no outer source occurrence')
        require(all(not x.startswith(y) for x in roots for y in roots if x!=y),'nested roots')
        require(all(table[r,b][:2]==(b,1) for r in (p,q) for b in (0,1)),'nonpure decoder')
        require({key for key,value in table.items() if value[2]==q}=={(p,0)},
                'inner decoder has another physical entrance')
        require(table[p,0][2]==q,'incorrect inner edge')
        factors=[]
        for prefix in roots:
            require(bound[prefix+'0']==q,'inner source binding')
            factors.append([closed_factor(rows,prefix+s) for s in ('00','01','1')])
        x,y,z=table[q,0][2],table[q,1][2],table[p,1][2]
        table.update({(p,0):(0,1,x),(p,1):(1,1,q),(q,0):(0,1,y),(q,1):(1,1,z)})
        rows=readdress(rows,roots);after=inspect_source(rows)
        require([r[1:] for r in rows]==original_word,'primitive word changed')
        require(after['graph']==graph,'ordinal control graph changed')
        newbound,maxsteps=prefix_bindings(table,after['prefixes'])
        stages.append({'outer':p,'inner':q,'paths':roots,'closed_factor_sizes':factors,
                       'internal_prefixes':len(newbound),'maximum_prefix_steps':maxsteps,
                       'metrics':after['metrics'],'both_cfg_resolvers':True})
    require(table==read_table(prefold_path),'complete rotated table differs')
    require(rows==json.loads(Path(source_path).read_text()),'complete source differs')
    incoming=fold_guard(table)
    candidate=read_table(candidate_path);states=census(candidate,210,254)
    expected={(q,b):(w,d,157 if t==218 else t) for (q,b),(w,d,t) in table.items() if q!=218}
    require(candidate==expected,'final table is not the exact fold')
    traces=fold_paths(table,candidate)
    # Existing Research U211 fold is preserved at all relevant rows/tag producers.
    retained=[(220,0),(220,1),(129,0),(129,1),(185,1),(216,0)]
    require(all(candidate[k]==old[k] for k in retained),'Research fold support changed')
    require(candidate[171,0]==old[171,0],'arithmetic entry repair unexpectedly introduced')
    final_info=inspect_source(rows);require(final_info['metrics']['maximum_zero_run']<=6,
                                           'seven-zero detector source exclusion fails')
    _,maxsteps=prefix_bindings(candidate,final_info['prefixes'])
    if dense_path is not None:
        dense=read_table(dense_path);census(dense,210,210)
        renaming={q:i for i,q in enumerate(states)};renaming[254]=210
        require(dense=={(renaming[q],b):(w,d,renaming[t]) for (q,b),(w,d,t) in candidate.items()},
                'dense table isomorphism')
    # These controls rerun semantic local/entry checks; no digest checks are involved.
    controls=[]
    for key,value,label in [((157,0),(1,-1,67),'wrong write'),
                            ((157,0),(0,1,67),'wrong direction'),
                            ((157,0),(0,-1,148),'wrong first helper'),
                            ((67,0),(0,1,152),'wrong zero selector'),
                            ((148,0),(0,1,173),'wrong one selector'),
                            ((151,0),(0,1,165),'wrong zero endpoint'),
                            ((186,1),(1,1,90),'wrong one endpoint')]:
        damaged=dict(candidate);damaged[key]=value
        controls.append(rejects(lambda t=damaged:fold_paths(table,t),label))
    controls.append(rejects(lambda:fold_paths(table,candidate,1),'false predecessor-one premise'))
    damaged=dict(table);damaged[0,0]=(1,1,218)
    controls.append(rejects(lambda:fold_guard(damaged),'extra nonzero-tag entrance'))
    changed=[{'state':q,'read':b,'before':old[q,b],'after':value}
             for (q,b),value in sorted(candidate.items()) if value!=old[q,b]]
    return {'status':'INDEPENDENT_U210_FINITE_SOURCE_PASS','rotations':len(stages),
            'working_states':210,'transition_rows':420,'source_primitives':len(rows),
            'source_edges':sum(len(x[2]) for x in graph),'source_cases':base_info['resolved'],
            'metrics':final_info['metrics'],'stages':stages,'fold_incoming':incoming,
            'fold_paths':traces,'unchanged_research_fold_rows':retained,
            'unchanged_entry_row_171_0':candidate[171,0],
            'final_internal_prefixes':len(final_info['prefixes']),
            'final_maximum_prefix_steps':maxsteps,
            'changed_retained_rows_from_research_u211':changed,
            'negative_controls_rejected':controls,
            'scope':'New finite/source/local certificates only; whole-runtime, blank startup, '
                    'and inherited Con(PA) calibration are separate obligations.'}

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    for arg in ('parent_table','parent_source','prefold','candidate','source'):
        parser.add_argument(arg,type=Path)
    parser.add_argument('--dense',type=Path);parser.add_argument('--output',type=Path)
    a=parser.parse_args();result=audit(a.parent_table,a.parent_source,a.prefold,a.candidate,a.source,a.dense)
    result['input_sha256']={name:hashlib.sha256(getattr(a,name).read_bytes()).hexdigest()
                            for name in ('parent_table','parent_source','prefold','candidate','source')}
    if a.dense:result['input_sha256']['dense']=hashlib.sha256(a.dense.read_bytes()).hexdigest()
    payload=json.dumps(result,indent=2)+'\n'
    if a.output:a.output.write_text(payload)
    print(json.dumps({k:v for k,v in result.items() if k not in ('stages','changed_retained_rows_from_research_u211')},indent=2))

if __name__=='__main__':main()
