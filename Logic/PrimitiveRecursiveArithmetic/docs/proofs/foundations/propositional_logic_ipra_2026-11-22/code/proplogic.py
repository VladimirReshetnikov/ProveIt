"""Finite, explicit reference constructions for propositional logic.

All loops have bounds computable from finite input. Python integers/lists are an
executable model of the natural-number encodings described in the report, not
an arithmetization or a machine-checked iPRA proof.
"""
from __future__ import annotations
from dataclasses import dataclass
from itertools import product
from typing import Iterable, Mapping

@dataclass(frozen=True)
class Formula:
    tag: str
    args: tuple = ()
    def __post_init__(self):
        assert self.tag in ('bot', 'var', 'and', 'or', 'imp')
        if self.tag == 'bot':
            assert not self.args
        elif self.tag == 'var':
            assert len(self.args) == 1 and type(self.args[0]) is int and self.args[0] >= 0
        else:
            assert len(self.args) == 2 and all(isinstance(x, Formula) for x in self.args)
    def __str__(self):
        if self.tag == 'bot': return 'F'
        if self.tag == 'var': return f'p{self.args[0]}'
        symbols = {'and': '&', 'or': '|', 'imp': '->'}
        return f'({self.args[0]}{symbols[self.tag]}{self.args[1]})'

BOT = Formula('bot')
def Var(i): return Formula('var', (i,))
def And(a,b): return Formula('and',(a,b))
def Or(a,b): return Formula('or',(a,b))
def Imp(a,b): return Formula('imp',(a,b))
def Not(a): return Imp(a,BOT)
TOP = Imp(BOT,BOT)
def Iff(a,b): return And(Imp(a,b),Imp(b,a))

def variables(a: Formula) -> frozenset[int]:
    if a.tag == 'bot': return frozenset()
    if a.tag == 'var': return frozenset((a.args[0],))
    return variables(a.args[0]) | variables(a.args[1])

def nodes(a: Formula) -> int:
    return 1 if a.tag in ('var','bot') else 1 + nodes(a.args[0]) + nodes(a.args[1])

def evaluate(a: Formula, valuation: Mapping[int,bool]) -> bool:
    if a.tag == 'bot': return False
    if a.tag == 'var': return bool(valuation.get(a.args[0],False))
    x,y = (evaluate(b,valuation) for b in a.args)
    if a.tag == 'and': return x and y
    if a.tag == 'or': return x or y
    return (not x) or y

def valuations(vs: Iterable[int]):
    vs = tuple(sorted(set(vs)))
    for bits in product((False,True), repeat=len(vs)):
        yield dict(zip(vs,bits))

def substitute(a: Formula, sigma: Mapping[int,Formula]) -> Formula:
    if a.tag == 'bot': return a
    if a.tag == 'var': return sigma.get(a.args[0],a)
    return Formula(a.tag, tuple(substitute(b,sigma) for b in a.args))

def fold_and(xs):
    a = TOP
    for x in reversed(tuple(xs)): a = And(x,a)
    return a

def fold_or(xs):
    a = BOT
    for x in reversed(tuple(xs)): a = Or(x,a)
    return a

def truth_table(a):
    return [(v,evaluate(a,v)) for v in valuations(variables(a))]

def canonical_dnf(a):
    vs = sorted(variables(a))
    return fold_or(fold_and(Var(i) if v[i] else Not(Var(i)) for i in vs)
                   for v,value in truth_table(a) if value)

def canonical_cnf(a):
    vs = sorted(variables(a))
    return fold_and(fold_or(Not(Var(i)) if v[i] else Var(i) for i in vs)
                    for v,value in truth_table(a) if not value)

def equivalent(a,b):
    return all(evaluate(a,v)==evaluate(b,v) for v in valuations(variables(a)|variables(b)))

# A clause is a frozenset of signed integers. Literal +(i+1) denotes p_i;
# -(i+1) denotes its negation. This keeps p_0 distinct from signed zero.
Literal = int
Clause = frozenset[Literal]
CNF = frozenset[Clause]

def clause_value(c: Clause, v):
    return any(bool(v.get(abs(l)-1,False)) == (l>0) for l in c)

def cnf_value(cs: CNF, v): return all(clause_value(c,v) for c in cs)
def cnf_variables(cs): return frozenset(abs(l)-1 for c in cs for l in c)
def tautological(c): return any(-l in c for l in c)

def resolution_closure(cs: CNF):
    """Return a saturation and a replayable resolution DAG.

    All non-tautological clauses over n variables are among 3**n clauses.
    Scans stop after at most 3**n rounds, including the stabilization round.
    Nodes are (clause, ('input',) or ('resolve', left, right, pivot)).
    """
    vs = cnf_variables(cs)
    history=[]; index={}
    for c in sorted(cs,key=lambda z:(len(z),sorted(z))):
        if not tautological(c) and c not in index:
            index[c]=len(history); history.append((c,('input',)))
    for _ in range(3**len(vs)):
        old=len(history)
        for i in range(old):
            for j in range(i+1,old):
                c,d=history[i][0],history[j][0]
                for l in sorted(c):
                    if -l in d:
                        e=(c-{l}) | (d-{-l})
                        if not tautological(e) and e not in index:
                            index[e]=len(history); history.append((e,('resolve',i,j,l)))
        if len(history)==old: break
    return frozenset(index), history

def check_resolution(cs,history):
    for k,(clause,rule) in enumerate(history):
        if rule==('input',):
            if clause not in cs: return False
        elif len(rule)==4 and rule[0]=='resolve':
            _,i,j,l=rule
            if not (0<=i<k and 0<=j<k): return False
            c,d=history[i][0],history[j][0]
            if l not in c or -l not in d or clause != (c-{l}) | (d-{-l}):
                return False
        else: return False
    return True

def dpll(cs):
    """Deterministic splitting, with depth at most the input variable count."""
    order=sorted(cnf_variables(cs))
    def run(current,depth,v):
        if frozenset() in current: return None
        if not current: return {**{i:False for i in order},**v}
        if depth==len(order): return None
        i=order[depth]; l=i+1
        for b in (False,True):
            true_l=l if b else -l
            remaining=frozenset(c-{-true_l} for c in current if true_l not in c)
            r=run(remaining,depth+1,{**v,i:b})
            if r is not None: return r
        return None
    return run(cs,0,{})

@dataclass
class TseitinResult:
    clauses: CNF
    root: int
    original_vars: frozenset[int]
    definitions: tuple[tuple[int,Formula],...]
    def extend(self,v):
        w=dict(v)
        for z,a in self.definitions: w[z]=evaluate(a,v)
        return w

def tseitin(a):
    """Definitional CNF, clauses of width <= 3, one fresh variable per DAG node.

    Variables themselves are shared with the original formula. The returned
    root unit clause demands truth. `definitions` records the semantic map.
    """
    vs=variables(a); next_var=max(vs,default=-1)+1
    memo={}; defs=[]; cs=set()
    def walk(b):
        nonlocal next_var
        if b.tag=='var': return b.args[0]+1
        if b in memo: return memo[b]+1
        children=[] if b.tag=='bot' else [walk(t) for t in b.args]
        z=next_var; next_var+=1; memo[b]=z; defs.append((z,b)); s=z+1
        if b.tag=='bot': rows=[[-s]]
        elif b.tag=='and':
            x,y=children; rows=[[-s,x],[-s,y],[s,-x,-y]]
        elif b.tag=='or':
            x,y=children; rows=[[s,-x],[s,-y],[-s,x,y]]
        else:
            x,y=children; rows=[[s,x],[s,-y],[-s,-x,y]]
        cs.update(frozenset(r) for r in rows)
        return s
    root=walk(a); cs.add(frozenset((root,)))
    return TseitinResult(frozenset(cs),root-1,vs,tuple(defs))

def forget(a,forgotten):
    """Boolean existential projection as disjunction of substitutions."""
    forgotten=set(forgotten)&variables(a)
    return fold_or(substitute(a,{i:TOP if b else BOT for i,b in v.items()})
                   for v in valuations(forgotten))

def interpolant(a,b):
    """If a entails b, return I in their common variables with a |= I |= b."""
    return forget(a,variables(a)-variables(b))

@dataclass(frozen=True)
class NDNode:
    context: frozenset[Formula]
    conclusion: Formula
    rule: str
    premises: tuple[int,...]=()

def check_nd(nodes: list[NDNode], classical=False):
    """Explicit finite DAG proof checker; premises always point backwards.

    No formula is accepted by its truth table. `lem` is allowed only in CPC.
    This checks the whole DAG; use check_nd_conclusion for a chosen target.
    Contexts are finite sets; context extension is explicit in rule checks.
    """
    for i,n in enumerate(nodes):
        if not isinstance(n,NDNode) or not isinstance(n.context,frozenset) or not isinstance(n.conclusion,Formula): return False
        if not isinstance(n.premises,tuple) or not all(isinstance(a,Formula) for a in n.context): return False
        if any(type(j) is not int or j<0 or j>=i for j in n.premises): return False
        ps=[nodes[j] for j in n.premises]; g=n.context; a=n.conclusion
        same=lambda p: p.context==g
        r=n.rule; good=False
        if r=='hyp' and not ps: good=a in g
        elif r=='botE' and len(ps)==1: good=same(ps[0]) and ps[0].conclusion==BOT
        elif r=='andI' and len(ps)==2 and a.tag=='and':
            good=all(same(p) for p in ps) and tuple(p.conclusion for p in ps)==a.args
        elif r in ('andL','andR') and len(ps)==1 and ps[0].conclusion.tag=='and':
            good=same(ps[0]) and a==ps[0].conclusion.args[r=='andR']
        elif r in ('orL','orR') and len(ps)==1 and a.tag=='or':
            good=same(ps[0]) and ps[0].conclusion==a.args[r=='orR']
        elif r=='impI' and len(ps)==1 and a.tag=='imp':
            b,c=a.args; good=ps[0].context==g|{b} and ps[0].conclusion==c
        elif r=='impE' and len(ps)==2 and ps[0].conclusion.tag=='imp':
            b,c=ps[0].conclusion.args
            good=all(same(p) for p in ps) and ps[1].conclusion==b and a==c
        elif r=='orE' and len(ps)==3 and ps[0].conclusion.tag=='or':
            b,c=ps[0].conclusion.args
            good=same(ps[0]) and ps[1].context==g|{b} and ps[2].context==g|{c} and ps[1].conclusion==ps[2].conclusion==a
        elif r=='weak' and len(ps)==1:
            good=ps[0].context<=g and a==ps[0].conclusion
        elif r=='cut' and len(ps)==2:
            good=same(ps[0]) and ps[1].context==g|{ps[0].conclusion} and a==ps[1].conclusion
        elif r=='lem' and not ps and classical and a.tag=='or':
            b,c=a.args; good=c==Not(b)
        if not good: return False
    return True


def check_nd_conclusion(nodes, index, context, conclusion, classical=False):
    """Check the entire finite DAG and the exact selected conclusion/context."""
    return (type(index) is int and 0<=index<len(nodes) and check_nd(nodes,classical)
            and nodes[index].context==frozenset(context)
            and nodes[index].conclusion==conclusion)


@dataclass(frozen=True)
class Kripke:
    # up[w] lists every world >= w, including w; atom_truth lists upsets.
    up: tuple[frozenset[int],...]
    atom_truth: tuple[tuple[int,frozenset[int]],...]
    def valid(self):
        n=len(self.up)
        if n==0: return False
        if any(w not in self.up[w] or any(v<0 or v>=n for v in self.up[w]) for w in range(n)): return False
        if any(not self.up[v]<=self.up[w] for w in range(n) for v in self.up[w]): return False
        if any(w!=v and w in self.up[v] for w in range(n) for v in self.up[w]): return False
        return all(all(0<=w<n and self.up[w]<=truth for w in truth) for _,truth in self.atom_truth)
    def forces(self,w,a):
        if a.tag=='bot': return False
        if a.tag=='var': return w in dict(self.atom_truth).get(a.args[0],frozenset())
        b,c=a.args
        if a.tag=='and': return self.forces(w,b) and self.forces(w,c)
        if a.tag=='or': return self.forces(w,b) or self.forces(w,c)
        return all(not self.forces(v,b) or self.forces(v,c) for v in self.up[w])

def subformulas(a):
    r={a}
    if a.tag not in ('bot','var'):
        for b in a.args: r.update(subformulas(b))
    return r

@dataclass
class IPCDecision:
    formulas: tuple[Formula,...]
    rows: tuple[int,...]
    proof_nodes: list[NDNode]
    proof_index: dict[tuple[int,int],int]
    worlds: tuple[int,...]
    model: Kripke
    rounds: int
    def index(self,a): return self.formulas.index(a)
    def context_code(self,g): return sum(1<<self.index(a) for a in set(g))
    def derivable(self,g,a): return bool(self.rows[self.context_code(g)] & (1<<self.index(a)))
    def truth_lemma(self):
        return all(self.model.forces(w,a)==bool(t&(1<<j))
                   for w,t in enumerate(self.worlds) for j,a in enumerate(self.formulas))

def ipc_saturate(gamma,goal):
    """Small executable version of finite relative IPC consequence saturation.

    The finite formula universe contains bottom and all input subformulas.
    Rules include cut; we use no cut-elimination theorem. Finite prime theories
    give the canonical model. This is exponential and intended for small input.
    """
    universe={BOT}
    for a in (*gamma,goal): universe.update(subformulas(a))
    fs=tuple(sorted(universe,key=lambda a:(nodes(a),str(a))))
    m=len(fs); pos={a:i for i,a in enumerate(fs)}; full=(1<<m)-1
    ctxs=[frozenset(fs[i] for i in range(m) if g&(1<<i)) for g in range(1<<m)]
    rows=[0]*(1<<m); history=[]; witness={}
    def add(g,a,rule,ps=()):
        if rows[g]&(1<<a): return False
        rows[g]|=1<<a; witness[g,a]=len(history)
        history.append(NDNode(ctxs[g],fs[a],rule,tuple(ps)))
        return True
    for g in range(1<<m):
        for a in range(m):
            if g&(1<<a): add(g,a,'hyp')
    bot=pos[BOT]
    for rounds in range(1,m*(1<<m)+2):
        before=len(history)
        for g in range(1<<m):
            # One-step weakening; transitive closure is obtained by saturation.
            for a in range(m):
                if g&(1<<a):
                    h=g & ~(1<<a)
                    for c in range(m):
                        if rows[h]&(1<<c): add(g,c,'weak',(witness[h,c],))
            if rows[g]&(1<<bot):
                for a in range(m): add(g,a,'botE',(witness[g,bot],))
            for a,f in enumerate(fs):
                if f.tag in ('bot','var'): continue
                b,c=(pos[x] for x in f.args)
                if f.tag=='and':
                    if rows[g]&(1<<b) and rows[g]&(1<<c):
                        add(g,a,'andI',(witness[g,b],witness[g,c]))
                    if rows[g]&(1<<a):
                        add(g,b,'andL',(witness[g,a],)); add(g,c,'andR',(witness[g,a],))
                elif f.tag=='or':
                    if rows[g]&(1<<b): add(g,a,'orL',(witness[g,b],))
                    if rows[g]&(1<<c): add(g,a,'orR',(witness[g,c],))
                    if rows[g]&(1<<a):
                        gb=g|(1<<b); gc=g|(1<<c)
                        for d in range(m):
                            if rows[gb]&rows[gc]&(1<<d):
                                add(g,d,'orE',(witness[g,a],witness[gb,d],witness[gc,d]))
                elif f.tag=='imp':
                    gb=g|(1<<b)
                    if rows[gb]&(1<<c): add(g,a,'impI',(witness[gb,c],))
                    if rows[g]&(1<<a) and rows[g]&(1<<b):
                        add(g,c,'impE',(witness[g,a],witness[g,b]))
            for b in range(m):
                if rows[g]&(1<<b):
                    gb=g|(1<<b)
                    for a in range(m):
                        if rows[gb]&(1<<a): add(g,a,'cut',(witness[g,b],witness[gb,a]))
        if len(history)==before: break
    else: raise AssertionError('Finite saturation bound exceeded')
    worlds=tuple(t for t in range(1<<m)
                 if not t&(1<<bot) and rows[t]==t
                 and all(f.tag!='or' or not t&(1<<i) or
                         t&((1<<pos[f.args[0]])|(1<<pos[f.args[1]]))
                         for i,f in enumerate(fs)))
    up=tuple(frozenset(v for v,u in enumerate(worlds) if t&u==t) for t in worlds)
    atom_truth=tuple((f.args[0],frozenset(w for w,t in enumerate(worlds) if t&(1<<i)))
                     for i,f in enumerate(fs) if f.tag=='var')
    return IPCDecision(fs,tuple(rows),history,witness,worlds,Kripke(up,atom_truth),rounds)

@dataclass(frozen=True)
class ProofResult:
    """An actual finite checked proof of the specified sequent."""
    logic: str
    context: frozenset[Formula]
    goal: Formula
    proof: tuple[NDNode,...]
    root: int
    kind: str = 'proof'

@dataclass(frozen=True)
class IPCCountermodelResult:
    context: frozenset[Formula]
    goal: Formula
    model: Kripke
    world: int = 0
    kind: str = 'countermodel'

@dataclass(frozen=True)
class BooleanCountervaluationResult:
    context: frozenset[Formula]
    goal: Formula
    valuation: tuple[tuple[int,bool],...]
    kind: str = 'countervaluation'


def extract_proof(nodes,root):
    """Prune a backwards-reference DAG to the ancestors of a chosen root."""
    needed={root}
    for i in range(root,-1,-1):
        if i in needed: needed.update(nodes[i].premises)
    order=sorted(needed); rename={old:new for new,old in enumerate(order)}
    return tuple(NDNode(nodes[i].context,nodes[i].conclusion,nodes[i].rule,
                        tuple(rename[j] for j in nodes[i].premises)) for i in order)


def generated_submodel(model,w):
    """The upward cone above w, renumbered with its root at zero."""
    order=[w]+sorted(model.up[w]-{w}); rename={old:new for new,old in enumerate(order)}
    up=tuple(frozenset(rename[v] for v in model.up[u]) for u in order)
    atoms=tuple((i,frozenset(rename[v] for v in truth if v in rename))
                for i,truth in model.atom_truth)
    return Kripke(up,atoms)


def decide_ipc(context,goal):
    """Return a proof with root reference, or a designated finite counterworld.

    The negative result is restricted to the generated submodel above the
    chosen world, hence is a nonempty rooted model with root zero. No missing
    existential witness is left to the caller.
    """
    context=frozenset(context); d=ipc_saturate(context,goal)
    g=d.context_code(context); a=d.index(goal)
    if d.rows[g]&(1<<a):
        root=d.proof_index[g,a]; proof=extract_proof(d.proof_nodes,root)
        return ProofResult('ipc',context,goal,proof,len(proof)-1)
    for w,t in enumerate(d.worlds):
        if t&g==g and not t&(1<<a):
            return IPCCountermodelResult(context,goal,generated_submodel(d.model,w))
    raise AssertionError('Canonical counterworld existence failed')


def check_ipc_result(result):
    if isinstance(result,ProofResult):
        return (result.logic=='ipc' and check_nd_conclusion(result.proof,result.root,
                                                          result.context,result.goal,False))
    if isinstance(result,IPCCountermodelResult):
        m=result.model; w=result.world
        return (m.valid() and type(w) is int and 0<=w<len(m.up)
                and m.up[w]==frozenset(range(len(m.up)))
                and all(m.forces(w,a) for a in result.context)
                and not m.forces(w,result.goal))
    return False


def truth_table_prove(context,goal):
    """Return a CPC proof DAG or an actual Boolean countervaluation.

    First scan the finite truth table. In the valid case construct signed
    formula proofs under each full valuation's literals and merge them with
    LEM/disjunction elimination. The leaf constructions use IPC rules only.
    """
    context=frozenset(context)
    vs=sorted(set().union(variables(goal),*(variables(a) for a in context)))
    for v in valuations(vs):
        if all(evaluate(a,v) for a in context) and not evaluate(goal,v):
            return BooleanCountervaluationResult(context,goal,tuple(sorted(v.items())))
    history=[]
    def emit(g,a,rule,ps=()):
        history.append(NDNode(g,a,rule,tuple(ps))); return len(history)-1
    def weaken(j,g):
        if history[j].context==g: return j
        return emit(g,history[j].conclusion,'weak',(j,))
    def signed(a,g,v):
        # Returns a proof of a if it evaluates true, and of a -> bottom otherwise.
        if a.tag=='bot':
            ext=g|{BOT}; h=emit(ext,BOT,'hyp')
            return emit(g,Not(BOT),'impI',(h,))
        if a.tag=='var':
            return emit(g,a if evaluate(a,v) else Not(a),'hyp')
        b,c=a.args; bv=evaluate(b,v); cv=evaluate(c,v)
        if a.tag=='and':
            if bv and cv:
                return emit(g,a,'andI',(signed(b,g,v),signed(c,g,v)))
            bad=b if not bv else c; nb=signed(bad,g,v); ext=g|{a}
            h=emit(ext,a,'hyp'); q=emit(ext,bad,'andL' if not bv else 'andR',(h,))
            bot=emit(ext,BOT,'impE',(weaken(nb,ext),q))
            return emit(g,Not(a),'impI',(bot,))
        if a.tag=='or':
            if bv: return emit(g,a,'orL',(signed(b,g,v),))
            if cv: return emit(g,a,'orR',(signed(c,g,v),))
            nb=signed(b,g,v); nc=signed(c,g,v); ext=g|{a}
            h=emit(ext,a,'hyp'); gb=ext|{b}; gc=ext|{c}
            hb=emit(gb,b,'hyp'); hc=emit(gc,c,'hyp')
            bb=emit(gb,BOT,'impE',(weaken(nb,gb),hb))
            bc=emit(gc,BOT,'impE',(weaken(nc,gc),hc))
            bot=emit(ext,BOT,'orE',(h,bb,bc))
            return emit(g,Not(a),'impI',(bot,))
        if cv:
            q=signed(c,g,v); ext=g|{b}
            return emit(g,a,'impI',(weaken(q,ext),))
        if not bv:
            nb=signed(b,g,v); ext=g|{b}; h=emit(ext,b,'hyp')
            bot=emit(ext,BOT,'impE',(weaken(nb,ext),h))
            q=emit(ext,c,'botE',(bot,))
            return emit(g,a,'impI',(q,))
        pb=signed(b,g,v); nc=signed(c,g,v); ext=g|{a}
        h=emit(ext,a,'hyp'); q=emit(ext,c,'impE',(h,weaken(pb,ext)))
        bot=emit(ext,BOT,'impE',(weaken(nc,ext),q))
        return emit(g,Not(a),'impI',(bot,))
    def tree(i,g,v):
        if i==len(vs):
            if evaluate(goal,v): return signed(goal,g,v)
            false_assumption=next(a for a in sorted(context,key=str) if not evaluate(a,v))
            na=signed(false_assumption,g,v); h=emit(g,false_assumption,'hyp')
            bot=emit(g,BOT,'impE',(na,h))
            return emit(g,goal,'botE',(bot,))
        x=vs[i]; p=Var(x); np=Not(p)
        left=tree(i+1,g|{p},{**v,x:True})
        right=tree(i+1,g|{np},{**v,x:False})
        lem=emit(g,Or(p,np),'lem')
        return emit(g,goal,'orE',(lem,left,right))
    root=tree(0,context,{})
    proof=extract_proof(history,root)
    return ProofResult('cpc',context,goal,proof,len(proof)-1)


def check_cpc_result(result):
    if isinstance(result,ProofResult):
        return (result.logic=='cpc' and check_nd_conclusion(result.proof,result.root,
                                                          result.context,result.goal,True))
    if isinstance(result,BooleanCountervaluationResult):
        if not all(type(i) is int and i>=0 and type(b) is bool for i,b in result.valuation): return False
        v=dict(result.valuation)
        if len(v)!=len(result.valuation): return False
        return all(evaluate(a,v) for a in result.context) and not evaluate(result.goal,v)
    return False


def formula_data(a):
    if a.tag=='bot': return ['bot']
    if a.tag=='var': return ['var',a.args[0]]
    return [a.tag,formula_data(a.args[0]),formula_data(a.args[1])]


def formula_from_data(data):
    if data==['bot']: return BOT
    if data[0]=='var' and len(data)==2: return Var(data[1])
    if data[0] in ('and','or','imp') and len(data)==3:
        return Formula(data[0],(formula_from_data(data[1]),formula_from_data(data[2])))
    raise ValueError('Invalid formula data')


def result_data(result):
    g=[formula_data(a) for a in sorted(result.context,key=str)]
    base={'kind':result.kind,'context':g,'goal':formula_data(result.goal)}
    if isinstance(result,ProofResult):
        return {**base,'logic':result.logic,'root':result.root,
                'proof':[{'context':[formula_data(a) for a in sorted(n.context,key=str)],
                          'conclusion':formula_data(n.conclusion),'rule':n.rule,
                          'premises':list(n.premises)} for n in result.proof]}
    if isinstance(result,IPCCountermodelResult):
        return {**base,'world':result.world,'model':{'up':[sorted(u) for u in result.model.up],
                'atom_truth':[[i,sorted(t)] for i,t in result.model.atom_truth]}}
    if isinstance(result,BooleanCountervaluationResult):
        return {**base,'valuation':[[i,b] for i,b in result.valuation]}
    raise ValueError('Unknown result type')


def result_from_data(data):
    g=frozenset(formula_from_data(a) for a in data['context']); a=formula_from_data(data['goal'])
    if data['kind']=='proof':
        proof=tuple(NDNode(frozenset(formula_from_data(b) for b in n['context']),
                           formula_from_data(n['conclusion']),n['rule'],tuple(n['premises']))
                    for n in data['proof'])
        return ProofResult(data['logic'],g,a,proof,data['root'])
    if data['kind']=='countermodel':
        model=data['model']; m=Kripke(tuple(frozenset(u) for u in model['up']),
                                    tuple((i,frozenset(t)) for i,t in model['atom_truth']))
        return IPCCountermodelResult(g,a,m,data['world'])
    if data['kind']=='countervaluation':
        return BooleanCountervaluationResult(g,a,tuple((i,b) for i,b in data['valuation']))
    raise ValueError('Unknown result kind')
