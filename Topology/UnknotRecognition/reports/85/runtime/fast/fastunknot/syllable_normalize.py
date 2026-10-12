"""Bounded power-run normalization of raw projection roots.

Unknown intermediate summaries cause fallback, never an equality assertion.
The limit is on syllables, not expanded letters or exponent magnitude.
"""


def _join(left, right):
    out=list(left)
    for g,e in right:
        if out and out[-1][0]==g:
            value=out[-1][1]+e
            if value:out[-1]=(g,value)
            else:out.pop()
        else:out.append((g,e))
    return tuple(out)


def _cyclic(word):
    out=list(word);left=0;right=len(out)
    while right-left>1 and out[left][0]==out[right-1][0] and (out[left][1]>0)!=(out[right-1][1]>0):
        g,a=out[left];_,b=out[right-1];total=a+b
        if abs(a)>=abs(b):
            right-=1
            if total:out[left]=(g,total)
            else:left+=1
        else:left+=1;out[right-1]=(g,total)
    return out[left:right]


def bounded_cyclic_roots(arena, roots, *, cache=None, max_runs=4, min_length=64):
    """Return exact cyclically reduced roots, or None before word allocation.

    Short roots retain the existing normalization. The probe succeeds on long
    roots only when every needed intermediate has at most max_runs free runs.
    """
    if type(max_runs) is not int or max_runs<1 or type(min_length) is not int or min_length<0:
        raise ValueError('run limit must be positive and length gate nonnegative')
    arena.tick(len(roots)+1)
    long=[r for r in roots if arena.lengths[r]>min_length]
    if not long:return None
    arena.stats['run_normalization_attempts']=arena.stats.get('run_normalization_attempts',0)+1
    if cache is None:cache={}
    summaries=cache.setdefault(max_runs,{0:()})
    for root in long:
        pending=[(root,False)]
        while pending:
            arena.tick();node,ready=pending.pop()
            if node in summaries:
                if summaries[node] is None:
                    summaries[root]=None
                    arena.stats['run_normalization_misses']=arena.stats.get('run_normalization_misses',0)+1
                    return None
                continue
            rule=arena.rules[node]
            if arena.uniform[node]:
                # Exact raw-word metadata proves every descendant has one run.
                x=arena.uniform[node]
                summaries[node]=((abs(x),arena.lengths[node] if x>0 else -arena.lengths[node]),)
                arena.stats['run_normalization_uniform_hits']=arena.stats.get('run_normalization_uniform_hits',0)+1
            elif not ready:
                pending.extend(((node,True),(rule[2],False),(rule[1],False)));continue
            else:
                a,b=summaries[rule[1]],summaries[rule[2]]
                if a is None or b is None:summaries[node]=None
                else:
                    arena.tick(len(a)+len(b));word=_join(a,b)
                    summaries[node]=word if len(word)<=max_runs else None
            arena.stats['run_normalization_nodes']=arena.stats.get('run_normalization_nodes',0)+1
            if summaries[node] is None:
                # One unsupported descendant forces this root to fall back;
                # do not visit unrelated pending siblings or build output words.
                summaries[root]=None
                arena.stats['run_normalization_misses']=arena.stats.get('run_normalization_misses',0)+1
                return None
    result=[]
    for root in roots:
        arena.tick()
        if arena.lengths[root]<=min_length:
            result.append(arena.cyclic_reduce(root));continue
        word=summaries[root];arena.tick(len(word)+1);word=_cyclic(word)
        nodes=[arena.power(arena.letter(g if e>0 else -g),abs(e)) for g,e in word]
        while len(nodes)>1:
            nodes=[arena.concat(nodes[i],nodes[i+1]) if i+1<len(nodes) else nodes[i] for i in range(0,len(nodes),2)]
        value=nodes[0] if nodes else 0
        arena._reduced[value]=value  # Constructed from a checked free run list.
        result.append(value)
    arena.stats['run_normalization_hits']=arena.stats.get('run_normalization_hits',0)+1
    return result
