#!/usr/bin/env python3
"""Pure queue reconstruction and scoped reachability for header checkpoints."""
from collections import deque

TARGETS=('Foundation.Vorspiel.Matrix',
         'Mathlib.LinearAlgebra.Matrix.Defs',
         'Mathlib.LinearAlgebra.Matrix.InvariantBasisNumber')

def require(ok,msg):
    if not ok:raise ValueError(msg)

def imports_of(record):
    names=sorted({n for part in record['headers'].values() for n in part['imports']})
    require(record['imports']==names,'header/import union mismatch')
    return names

def pop_expected(queue,queued,seen,graph):
    require(bool(queue),'unexpected empty queue')
    name=queue.popleft();queued.remove(name)
    require(name not in seen and name in graph,'queue head lacks a fresh record: '+name)
    seen.add(name)
    for dep in imports_of(graph[name]):
        if dep not in seen and dep not in queued:queue.append(dep);queued.add(dep)
    return name

def restore(prior,declared_seeds,checkpoint=None):
    """Authenticate old BFS, append real seeds, then replay checkpoint order."""
    require(prior['status']=='PARTIAL_COMPILED_HEADERS','expected partial baseline')
    require(len(prior['seeds'])==len(set(prior['seeds'])),'duplicate original seed')
    graph=dict(prior['modules']);queue=deque(prior['seeds']);queued=set(queue);seen=set()
    for _ in range(len(graph)):pop_expected(queue,queued,seen,graph)
    require(seen==set(graph),'baseline seen set mismatch')
    require(list(queue)==prior['frontier'],'baseline frontier order mismatch')
    require(len(declared_seeds)==len(set(declared_seeds)),'duplicate declared seed')
    for name in sorted(declared_seeds):
        if name not in seen and name not in queued:queue.append(name);queued.add(name)
    processed=[]
    if checkpoint is not None:
        require(checkpoint['declared_seeds']==sorted(declared_seeds),'declared seed mismatch')
        graph=dict(checkpoint['modules'])
        require(all(name in graph and graph[name]==rec for name,rec in prior['modules'].items()),
                'baseline module records changed')
        for expected in checkpoint['processed']:
            name=pop_expected(queue,queued,seen,graph)
            require(name==expected,'checkpoint processing order mismatch')
            processed.append(name)
        require(seen==set(graph),'checkpoint seen set mismatch')
        require(list(queue)==checkpoint['frontier'],'checkpoint frontier mismatch')
    return {'modules':graph,'queue':queue,'queued':queued,'seen':seen,'processed':processed}

def append(state,name,record):
    require(state['queue'] and state['queue'][0]==name,'worker attempted non-head module')
    require(name not in state['modules'],'duplicate module')
    state['modules'][name]=record
    actual=pop_expected(state['queue'],state['queued'],state['seen'],state['modules'])
    state['processed'].append(actual)

def validate_extension(previous,current):
    old_processed=previous.get('processed',[])
    require(current['processed'][:len(old_processed)]==old_processed,'processed prefix changed')
    delta=current['processed'][len(old_processed):]
    require(current['new_processed']==delta and len(delta)<=64,'checkpoint delta mismatch')
    for key in ('modules','artifacts','namespace_observations'):
        require(all(name in current[key] and current[key][name]==rec
                    for name,rec in previous[key].items()),key+' changed across checkpoint')
    require(current['root_observations']==previous['root_observations'],'root observations changed')

def validate_chain(prior,declared_seeds,states):
    """Replay each checkpoint and require append-only transitions, oldest first."""
    previous=prior
    for current in states:
        restore(prior,declared_seeds,current)
        validate_extension(previous,current)
        previous=current

def reachability(graph,seeds):
    """Known header paths and per-seed unknown closure (no runtime claim)."""
    result={}
    for seed in sorted(seeds):
        queue=deque([(seed,[seed])]);seen={seed};found={};unknown=set()
        while queue:
            name,path=queue.popleft()
            if name in TARGETS and name in graph:found.setdefault(name,path)
            if name not in graph:
                unknown.add(name);continue
            for dep in imports_of(graph[name]):
                if dep not in seen:seen.add(dep);queue.append((dep,path+[dep]))
        result[seed]={'known_paths':found,'unexpanded':sorted(unknown),
                      'complete':not unknown}
    return result
