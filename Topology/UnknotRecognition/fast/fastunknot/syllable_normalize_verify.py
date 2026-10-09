"""Independent bounded-run evaluation for the existing normalization move.

No producer normalizer, merge routine or cyclic trimming helper is imported.
Unsupported summaries defer to the maintained general word operations.
"""
from collections import deque


def replay_cyclic_roots(arena, roots, *, cache=None, max_runs=4, min_length=64):
    if type(max_runs) is not int or max_runs<1 or type(min_length) is not int or min_length<0:
        raise ValueError('run limit must be positive and length gate nonnegative')
    arena.tick(len(roots)+1)
    targets=[r for r in roots if arena.lengths[r]>min_length]
    if not targets:return None
    if cache is None:cache={}
    memo=cache.setdefault(max_runs,{0:()})
    arena.stats['run_normalization_attempts']=arena.stats.get('run_normalization_attempts',0)+1
    for root in targets:
        stack=[(root,0)]
        while stack:
            arena.tick();node,phase=stack.pop()
            if node in memo:
                if memo[node] is None:
                    memo[root]=None
                    arena.stats['run_normalization_misses']=arena.stats.get('run_normalization_misses',0)+1
                    return None
                continue
            rule=arena.rules[node]
            letter=arena.uniform[node]
            if letter:
                # The source-built arena certifies a single signed raw letter.
                exponent=arena.lengths[node]
                memo[node]=((abs(letter),exponent if letter>0 else -exponent),)
                arena.stats['run_normalization_uniform_hits']=arena.stats.get('run_normalization_uniform_hits',0)+1
            elif phase==0:stack.extend(((node,1),(rule[2],0),(rule[1],0)));continue
            else:
                prefix,suffix=memo[rule[1]],memo[rule[2]]
                if prefix is None or suffix is None:memo[node]=None
                else:
                    arena.tick(len(prefix)+len(suffix));left=list(prefix);right=deque(suffix)
                    # Only the boundary can cancel; both children are already
                    # free run normal forms. This differs from producer folding.
                    while left and right and left[-1][0]==right[0][0]:
                        arena.tick();g,a=left.pop();_,b=right.popleft();total=a+b
                        if total:left.append((g,total))
                    word=tuple(left)+tuple(right)
                    memo[node]=word if len(word)<=max_runs else None
            arena.stats['run_normalization_nodes']=arena.stats.get('run_normalization_nodes',0)+1
            if memo[node] is None:
                # Cache the query's rejection without evaluating its other branch.
                memo[root]=None
                arena.stats['run_normalization_misses']=arena.stats.get('run_normalization_misses',0)+1
                return None
    answers=[]
    for root in roots:
        arena.tick()
        if arena.lengths[root]<=min_length:answers.append(arena.cyclic_reduce(root));continue
        runs=deque(memo[root])
        while len(runs)>1:
            arena.tick();g,a=runs[0];h,b=runs[-1]
            if g!=h or (a>0)==(b>0):break
            runs.popleft();runs.pop();cancel=min(abs(a),abs(b))
            a-=cancel if a>0 else -cancel;b-=cancel if b>0 else -cancel
            if a:runs.appendleft((g,a))
            if b:runs.append((h,b))
        # Left-associated construction is independent of the producer's
        # balanced builder; both encode the same anchored cyclic reduction.
        value=0
        for g,e in runs:
            arena.tick();piece=arena.power(arena.letter(g if e>0 else -g),abs(e))
            value=arena.concat(value,piece)
        arena._reduced[value]=value
        answers.append(value)
    arena.stats['run_normalization_hits']=arena.stats.get('run_normalization_hits',0)+1
    return answers
