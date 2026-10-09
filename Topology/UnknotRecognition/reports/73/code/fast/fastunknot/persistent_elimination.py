"""Persistent raw-block producer with the maintained greedy donor policy.

The independent checker lives in persistent_elimination_verify and is never
called here. Search summaries use exact lengths, occurrence multiplicities,
and presence/repetition masks; no free reduction occurs inside a block.
"""
from .compressed_words import CompressedLimit
from .elimination_batch import _select_batch


class _Block:
    def __init__(self, arena, roots, alive):
        self.arena = arena
        self.rules, self.depths = [None], [0]
        self.interned, self.bindings = {}, {}
        self.alive = set(alive)
        self.labels = sorted(alive)
        self.bits = {g:1 << i for i,g in enumerate(self.labels)}
        mapped = {0:0}
        for node in arena._reachable(roots):
            rule = arena.rules[node]
            if rule[0] == 't':
                letter = rule[1]
                terminal = self.intern(('t',abs(letter)),0)
                mapped[node] = terminal if letter>0 else -terminal
            else:mapped[node] = self.concat(mapped[rule[1]],mapped[rule[2]])
        self.roots = [mapped[root] for root in roots]
        self.summaries = None
        self.context_siblings = 0

    def capacity(self):
        total = len(self.arena.rules)+len(self.rules)-2
        stats = self.arena.stats
        stats['persistent_search_peak_nodes'] = max(stats.get('persistent_search_peak_nodes',0),total)
        if total>self.arena.max_nodes:
            raise CompressedLimit('persistent producer combined node allowance exhausted')

    def intern(self, rule, depth):
        self.arena.tick()
        if rule in self.interned:return self.interned[rule]
        if len(self.arena.rules)+len(self.rules)-2>=self.arena.max_nodes:
            raise CompressedLimit('persistent producer combined node allowance exhausted')
        node=len(self.rules);self.rules.append(rule);self.depths.append(depth)
        self.interned[rule]=node;self.capacity()
        return node

    def concat(self, left, right):
        self.arena.tick()
        if not left:return right
        if not right:return left
        return self.intern(('c',left,right),1+max(self.depths[abs(left)],self.depths[abs(right)]))

    def join(self, pieces):
        row=[p for p in pieces if p]
        while len(row)>1:
            row=[self.concat(row[i],row[i+1]) if i+1<len(row) else row[i] for i in range(0,len(row),2)]
        return row[0] if row else 0

    def children(self, node):
        rule=self.rules[node]
        if rule[0]=='c':return abs(rule[1]),abs(rule[2])
        target=self.bindings.get(rule[1],0)
        return (abs(target),) if target else ()

    def postorder(self, goals=None):
        # Iterative DFS, independent of the checker's Kahn evaluation.
        seen={0:2};order=[]
        for goal in (range(1,len(self.rules)) if goals is None else goals):
            pending=[(abs(goal),False)]
            while pending:
                self.arena.tick();node,ready=pending.pop()
                if seen.get(node)==2:continue
                if ready:
                    seen[node]=2;order.append(node)
                else:
                    if seen.get(node)==1:raise ArithmeticError('cyclic persistent producer bindings')
                    seen[node]=1;pending.append((node,True))
                    pending.extend((child,False) for child in reversed(self.children(node)))
        return order

    def summarize(self):
        if self.summaries is not None:return self.summaries
        order=self.postorder();size=len(self.rules)
        lengths=[0]*size;present=[0]*size;repeated=[0]*size
        for node in order:
            self.arena.tick();rule=self.rules[node]
            if rule[0]=='c':
                left,right=abs(rule[1]),abs(rule[2]);p,q=present[left],present[right]
                lengths[node]=lengths[left]+lengths[right]
                present[node]=p|q;repeated[node]=repeated[left]|repeated[right]|(p&q)
            elif rule[1] in self.bindings:
                target=abs(self.bindings[rule[1]])
                lengths[node],present[node],repeated[node]=lengths[target],present[target],repeated[target]
            else:
                lengths[node]=1;present[node]=self.bits[rule[1]]
        weights=[0]*size;counts={g:0 for g in self.alive}
        for root in self.roots:
            self.arena.tick();weights[abs(root)]+=1
        for node in reversed(order):
            self.arena.tick();weight=weights[node];rule=self.rules[node]
            if rule[0]=='c':
                weights[abs(rule[1])]+=weight;weights[abs(rule[2])]+=weight
            elif rule[1] in self.bindings:
                weights[abs(self.bindings[rule[1]])]+=weight
            else:counts[rule[1]]+=weight
        self.summaries=lengths,present,repeated,counts
        stats=self.arena.stats
        stats['persistent_search_summary_nodes']=stats.get('persistent_search_summary_nodes',0)+len(order)
        return self.summaries

    def plan(self):
        lengths,present,repeated,counts=self.summarize();supports={};candidates=[]
        for slot,root in enumerate(self.roots):
            self.arena.tick();node=abs(root);mask=present[node];support=set()
            while mask:
                self.arena.tick();bit=mask&-mask;mask^=bit
                support.add(self.labels[bit.bit_length()-1])
            supports[slot]=support;single=present[node]&~repeated[node]
            while single:
                self.arena.tick();bit=single&-single;single^=bit;g=self.labels[bit.bit_length()-1]
                if g in self.alive and support<=self.alive:
                    length=lengths[node];candidates.append(((length-2)*counts[g],length,slot,g))
        return _select_batch(self.arena,candidates,supports,self.alive,self.bits,ordered=True)

    def apply(self, selected):
        _,present,repeated,_=self.summarize();images={};slots=set()
        for entry in selected:
            self.arena.tick();slot,g=entry['relation'],entry['generator'];node=abs(self.roots[slot]);bit=self.bits[g]
            if (g not in self.alive or g in images or slot in slots
                    or not present[node]&bit or repeated[node]&bit):
                raise ArithmeticError('invalid persistent producer singleton')
            current=self.roots[slot];prefix=[];suffix=[]
            while True:
                self.arena.tick();rule=self.rules[abs(current)];sign=1 if current>0 else -1
                if rule[0]=='t':
                    if rule[1] in self.bindings:current=sign*self.bindings[rule[1]];continue
                    if rule[1]!=g:raise ArithmeticError('persistent producer descent missed pivot')
                    break
                left,right=rule[1:]
                if sign<0:left,right=-right,-left
                if present[abs(left)]&bit:suffix.append(right);current=left
                else:prefix.append(left);current=right
            self.context_siblings+=len(prefix)+len(suffix)
            rest=self.join(list(reversed(suffix))+prefix)
            images[g]=-rest if sign>0 else rest;slots.add(slot)
        # The selection policy has proved that these simultaneous definitions
        # have an acyclic selected dependency graph. All contexts above are old.
        self.bindings.update(images)
        self.alive.difference_update(images)
        for slot in slots:self.roots[slot]=0
        self.summaries=None
        stats=self.arena.stats
        stats['elimination_batch_rounds']=stats.get('elimination_batch_rounds',0)+1
        stats['elimination_batch_generators']=stats.get('elimination_batch_generators',0)+len(selected)

    def export(self):
        # Dependency-first compilation of both orientations. This is separate
        # from the checker's signed demand walk; ordinary caches stay immutable.
        mapped={0:0}
        for node in self.postorder(self.roots):
            self.arena.tick();rule=self.rules[node]
            if rule[0]=='c':
                left,right=rule[1:]
                mapped[node]=self.arena.concat(mapped[left],mapped[right])
                self.capacity()
                mapped[-node]=self.arena.concat(mapped[-right],mapped[-left])
            elif rule[1] in self.bindings:
                target=self.bindings[rule[1]]
                mapped[node],mapped[-node]=mapped[target],mapped[-target]
            else:
                mapped[node]=self.arena.letter(rule[1]);self.capacity()
                mapped[-node]=self.arena.letter(-rule[1])
            self.capacity()
        return [mapped[root] for root in self.roots]


def produce_block(arena, roots, alive, moves, first):
    """Run the existing greedy batch policy to its next explicit boundary.

    `first` is the already selected ordered batch from the ordinary producer.
    Return whether planning stalled with at least three generators; the caller
    must not repeat that unchanged plan before trying the next search stage.
    Root, generator and trace publication occurs only after a complete export.
    """
    block=_Block(arena,roots,alive);selected=first;trace=[];stalled=False
    while len(selected)>=2:
        block.apply(selected);trace.append(dict(kind='elimination_batch',entries=selected))
        if len(block.alive)<3:break
        selected=block.plan()
        if len(selected)<2:stalled=True
    output=block.export()
    stats=arena.stats
    stats['persistent_search_blocks']=stats.get('persistent_search_blocks',0)+1
    stats['persistent_search_batches']=stats.get('persistent_search_batches',0)+len(trace)
    stats['persistent_search_nodes']=stats.get('persistent_search_nodes',0)+len(block.rules)-1
    stats['persistent_search_context_siblings']=stats.get('persistent_search_context_siblings',0)+block.context_siblings
    stats['persistent_search_max_depth']=max(stats.get('persistent_search_max_depth',0),max(block.depths))
    roots[:]=output;alive.clear();alive.update(block.alive);moves.extend(trace)
    return stalled
