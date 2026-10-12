"""Producer-only monomial discovery on immutable source words.

Preserves the ordinary greedy projection/forest policy and exports once per
raw block. Never imports checker arithmetic. Source recovery and independent
complete replay are still required before an unknot verdict.
"""
from math import gcd
from .primitive_projection import plan_projection
from .primitive_forest import plan_forest
from .elimination_batch import _select_batch


class _SourceSearch:
    def __init__(self, arena, roots, alive):
        arena.tick(len(roots)+len(alive)+1)
        self.arena, self.roots = arena, tuple(roots)
        self.alive, self.dead = set(alive), set()
        self.images = {g:(g,1) for g in alive}
        self.max_bits = 1
        self.rounds = 0

    def order(self, goals=None):
        # Postorder only surviving requested roots, never historical allocations.
        return self.arena._reachable([r for i,r in enumerate(self.roots) if i not in self.dead]
                                     if goals is None else goals)

    def candidates(self):
        arena=self.arena;counts={0:{}}
        for node in self.order():
            arena.tick();rule=arena.rules[node]
            if rule[0]=='t':
                label,k=self.images[abs(rule[1])]
                if rule[1]<0:k=-k
                counts[node]={label:(max(k,0),max(-k,0))}
            else:
                left,right=counts[rule[1]],counts[rule[2]]
                if left is None or right is None or len(left.keys() | right.keys())>2:
                    counts[node]=None
                else:
                    local=dict(left)
                    for g,(p,n) in right.items():
                        a,b=local.get(g,(0,0));local[g]=a+p,b+n
                    counts[node]=local
        candidates=[]
        for slot,root in enumerate(self.roots):
            arena.tick()
            if slot in self.dead:continue
            local=counts[root]
            if local is None or len(local)!=2 or any(p and n for p,n in local.values()):continue
            pair=tuple(sorted(local))
            candidates.append((slot,root,(pair,tuple(local[g][0]-local[g][1] for g in pair))))
        self.vectors={root:(pair,vector) for _,root,(pair,vector) in candidates}
        arena.stats['anchored_search_candidate_nodes']=arena.stats.get('anchored_search_candidate_nodes',0)+len(counts)-1
        return candidates,{}

    def power(self, arena, roots, alive):
        # This callback is used only on coherent two-label candidates. The
        # maintained planners decide when a profile is necessary.
        root,=roots;pair,raw=self.vectors[root]
        u,v=raw;d=gcd(abs(u),abs(v));u//=d;v//=d
        values={0:(0,0,0)}
        for node in self.order([root]):
            arena.tick();rule=arena.rules[node]
            if rule[0]=='t':
                g,k=self.images[abs(rule[1])]
                if rule[1]<0:k=-k
                h=k*(v if g==pair[0] else -u)
                values[node]=h,min(0,h),max(0,h)
            else:
                h,l,r=values[rule[1]];k,b,t=values[rule[2]]
                values[node]=h+k,min(l,h+b),max(r,h+t)
        _,low,high=values[root];width=abs(u)+abs(v)-1
        if high-low!=width:return None
        return dict(kind='rank_two_primitive_power',relation=0,generators=list(pair),
                    primitive_vector=[u,v],exponent=d,width=width)

    def plan(self, forest):
        prepared=self.candidates();cache={}
        if forest and len(prepared[0])>=2:
            edges=plan_forest(self.arena,self.roots,self.alive,cache,_prepared=prepared,_power=self.power)
            if len(edges)>=2:return dict(kind='primitive_forest',edges=edges)
        pairs=plan_projection(self.arena,self.roots,self.alive,cache,_prepared=prepared,_power=self.power)
        return dict(kind='primitive_projection',pairs=pairs) if pairs else None

    def elimination(self):
        """Exact maintained singleton priority without materializing powers."""
        arena=self.arena;labels=sorted(self.alive);bits={g:1<<i for i,g in enumerate(labels)}
        order=self.order();summary={0:(0,0,0)}
        for node in order:
            arena.tick();rule=arena.rules[node]
            if rule[0]=='t':
                g,k=self.images[abs(rule[1])];bit=bits[g]
                summary[node]=abs(k),bit,bit if abs(k)>1 else 0
            else:
                n,p,a=summary[rule[1]];m,q,b=summary[rule[2]]
                summary[node]=n+m,p|q,a|b|(p&q)
        weights={};counts={g:0 for g in labels}
        for slot,root in enumerate(self.roots):
            arena.tick()
            if slot not in self.dead:weights[root]=weights.get(root,0)+1
        for node in reversed(order):
            arena.tick();weight=weights.get(node,0);rule=arena.rules[node]
            if rule[0]=='t':
                g,k=self.images[abs(rule[1])];counts[g]+=weight*abs(k)
            else:
                for child in rule[1:]:weights[child]=weights.get(child,0)+weight
        candidates=[];supports={}
        for slot,root in enumerate(self.roots):
            arena.tick()
            if slot in self.dead:continue
            length,present,repeated=summary[root];mask=present;support=set()
            while mask:
                arena.tick();bit=mask&-mask;mask^=bit;support.add(labels[bit.bit_length()-1])
            supports[slot]=support;single=present&~repeated
            while single:
                arena.tick();bit=single&-single;single^=bit;g=labels[bit.bit_length()-1]
                candidates.append(((length-2)*counts[g],length,slot,g))
        return _select_batch(arena,candidates,supports,self.alive,bits,ordered=True)

    def apply(self, move):
        arena=self.arena;local={};removed=set();slots=[]
        if move['kind']=='primitive_projection':
            for proof in move['pairs']:
                arena.tick();a,b=proof['generators'];u,v=proof['primitive_vector']
                local[a],local[b]=(a,abs(v)),(a,-u if v>0 else u)
                removed.add(b);slots.append(proof['relation'])
        else:
            parents={}
            for edge in move['edges']:
                arena.tick();proof=edge['proof'];a,b=proof['generators'];u,v=proof['primitive_vector'];child=edge['child']
                parents[child]=(b,-v*u) if child==a else (a,-u*v)
                slots.append(proof['relation'])
            # Resolve parent chains separately from the verifier's BFS routine.
            for child in parents:
                chain=[];g=child
                while g in parents and g not in local:
                    arena.tick();chain.append(g);g=parents[g][0]
                for g in reversed(chain):
                    arena.tick();parent,k=parents[g];target,factor=local.get(parent,(parent,1))
                    local[g]=target,k*factor
            removed=set(parents)
        updated={}
        for original,(g,k) in self.images.items():
            arena.tick();target,factor=local.get(g,(g,1));power=k*factor
            updated[original]=target,power;self.max_bits=max(self.max_bits,abs(power).bit_length())
        self.images=updated;self.dead.update(slots);self.alive.difference_update(removed);self.rounds+=1
        kind='forest' if move['kind']=='primitive_forest' else 'projection'
        for key,amount in ((kind+'_rounds',1),(kind+('_edges' if kind=='forest' else '_pairs'),len(slots))):
            arena.stats[key]=arena.stats.get(key,0)+amount

    def export(self):
        arena=self.arena;mapped={0:0};powers={}
        for node in self.order():
            arena.tick();rule=arena.rules[node]
            if rule[0]=='t':
                g,k=self.images[abs(rule[1])]
                if rule[1]<0:k=-k
                if (g,k) not in powers:powers[g,k]=arena.power(arena.letter(g if k>0 else -g),abs(k))
                mapped[node]=powers[g,k]
            else:mapped[node]=arena.concat(mapped[rule[1]],mapped[rule[2]])
        arena.tick(len(self.roots)+1)
        return [0 if i in self.dead else mapped[root] for i,root in enumerate(self.roots)]


def produce_block(arena, roots, alive, moves, first, *, forest=False, elimination=False):
    """Discover whole raw block; atomically publish ordinary state and moves.

    Rank two always returns to the caller's existing endpoint priority. A
    singleton batch of at least two donors also ends the monomial block.
    """
    state=_SourceSearch(arena,roots,alive);pending=[];move=first
    while move is not None:
        state.apply(move);pending.append(move)
        if len(state.alive)<=2:break
        if elimination and len(state.elimination())>=2:break
        move=state.plan(forest)
    output=state.export();arena.tick()
    roots[:]=output;alive.clear();alive.update(state.alive);moves.extend(pending)
    stats=arena.stats
    stats['anchored_search_blocks']=stats.get('anchored_search_blocks',0)+1
    stats['anchored_search_rounds']=stats.get('anchored_search_rounds',0)+state.rounds
    stats['anchored_search_max_exponent_bits']=max(stats.get('anchored_search_max_exponent_bits',0),state.max_bits)
