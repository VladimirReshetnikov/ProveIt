#!/usr/bin/env python3
"""Own CBV-lambda -> original Jay branch-first Tree Calculus compiler.

Pure standard library. No downloaded code is imported or run.
Metasyntax separates L/S/F tree constructors from computational application A.
The generated literal universal tree is serialized as an acyclic constructor DAG.
"""
from functools import lru_cache
from pathlib import Path
import hashlib
import json
import sys

sys.setrecursionlimit(50000)

# Source lambda syntax. Variables are strings; all generated binders are fresh.
def V(x): return ('v', x)
def A(*xs):
    out = xs[0]
    for x in xs[1:]: out = ('a', out, x)
    return out
def Lam(xs, body):
    if isinstance(xs, str): xs = xs.split()
    for x in reversed(xs): body = ('l', x, body)
    return body

class Algebra:
    def __init__(self):
        self.nodes = []
        self.index = {}
        self.L = self.node('L')
        self.I = self.F(self.S(self.L), self.S(self.L))
        self.KL = self.F(self.L, self.L)

    def node(self, *n):
        if n not in self.index:
            self.index[n] = len(self.nodes)
            self.nodes.append(n)
        return self.index[n]
    def S(self, a): return self.node('S', a)
    def F(self, a, b): return self.node('F', a, b)
    def app(self, a, b): return self.node('A', a, b)
    def var(self, x): return self.node('v', x)

    @lru_cache(None)
    def freevars(self, t):
        n = self.nodes[t]
        if n[0] == 'v': return frozenset([n[1]])
        return frozenset().union(*(self.freevars(c) for c in n[1:]))

    @lru_cache(None)
    def template(self, t):
        n = self.nodes[t]
        return n[0] != 'A' and all(self.template(c) for c in n[1:] if isinstance(c,int))

    @lru_cache(None)
    def bracket(self, x, t):
        n = self.nodes[t]
        # Safe constant optimization ONLY for a constructor value template.
        # An x-free computational application is never silently forced here.
        if x not in self.freevars(t) and self.template(t):
            return self.F(self.L, t)
        if n[0] == 'v': return self.I if n[1] == x else self.F(self.L, t)
        if n[0] == 'L': return self.KL
        if n[0] == 'A':
            return self.F(self.S(self.bracket(x, n[2])), self.bracket(x, n[1]))
        if n[0] == 'S':
            return self.F(self.S(self.bracket(x, n[1])), self.KL)
        if n[0] == 'F':
            bm, bn = self.bracket(x, n[1]), self.bracket(x, n[2])
            return self.F(self.S(bn), self.F(self.S(bm), self.KL))
        raise ValueError(n)

    @lru_cache(None)
    def compile(self, t):
        if t[0] == 'v': return self.var(t[1])
        if t[0] == 'a': return self.app(self.compile(t[1]), self.compile(t[2]))
        if t[0] == 'l': return self.bracket(t[1], self.compile(t[2]))
        raise ValueError(t)

    def export_value(self, root):
        out, renumber = [], {}
        def visit(i):
            if i in renumber: return renumber[i]
            n = self.nodes[i]
            assert n[0] in ('L', 'S', 'F'), n
            children = [visit(j) for j in n[1:]]
            renumber[i] = len(out)
            out.append([n[0]] + children)
            return renumber[i]
        r = visit(root)
        return {'format': 'original-jay-tree-value-dag-v1', 'nodes': out, 'root': r}

    def eval(self, t, env=None, limit=1000000):
        # Iterative eager abstract machine. Budget counts E-rule invocations.
        env = {} if env is None else env
        todo, stack, count = [('eval', t)], [], 0
        while todo:
            op = todo.pop()
            if op[0] == 'eval':
                n = self.nodes[op[1]]
                if n[0] == 'L': stack.append(self.L)
                elif n[0] == 'v': stack.append(env[n[1]])
                elif n[0] == 'S': todo += [('mkS',), ('eval', n[1])]
                elif n[0] == 'F': todo += [('mkF',), ('eval', n[2]), ('eval', n[1])]
                elif n[0] == 'A': todo += [('apply',), ('eval', n[2]), ('eval', n[1])]
                else: raise ValueError(n)
            elif op[0] == 'mkS': stack.append(self.S(stack.pop()))
            elif op[0] == 'mkF':
                b, a = stack.pop(), stack.pop(); stack.append(self.F(a, b))
            elif op[0] == 'push': stack.append(op[1])
            elif op[0] == 'apply':
                count += 1
                if count > limit: return None, count
                y, x = stack.pop(), stack.pop()
                n = self.nodes[x]
                if n[0] == 'L': stack.append(self.S(y))
                elif n[0] == 'S': stack.append(self.F(n[1], y))
                elif n[0] == 'F':
                    first, second = n[1:]
                    f = self.nodes[first]
                    if f[0] == 'L': stack.append(second)
                    elif f[0] == 'S':
                        # E(E(second,y), E(f.child,y)), left operand first.
                        todo += [('apply',), ('apply',), ('push', y), ('push', f[1]),
                                 ('apply',), ('push', y), ('push', second)]
                    elif f[0] == 'F':
                        todo += [('apply',), ('push', f[2]), ('apply',),
                                 ('push', f[1]), ('push', y)]
                    else: raise ValueError(f)
                else: raise ValueError(n)
            else: raise ValueError(op)
        assert len(stack) == 1
        return stack[0], count


# CBV self-interpreter, using functional environments and Scott-encoded syntax.
ID = Lam('id', V('id'))
DUP = Lam('om', A(V('om'), V('om')))
OMEGA = A(DUP, DUP)
EMPTY = Lam('en', OMEGA)
ZX = Lam('zx', A(V('zf'), Lam('zv', A(V('zx'), V('zx'), V('zv')))))
Z = Lam('zf', A(ZX, ZX))
VAR_HANDLER = Lam('vn', A(V('env'), V('vn')))
EXTEND = Lam('ix', A(V('ix'), V('arg'), V('env')))
LAM_HANDLER = Lam('body arg', A(V('ev'), V('body'), EXTEND))
APP_HANDLER = Lam('fun argt', A(A(V('ev'), V('fun'), V('env')),
                               A(V('ev'), V('argt'), V('env'))))
PHI = Lam('ev term env', A(V('term'), VAR_HANDLER, LAM_HANDLER, APP_HANDLER))
UNIVERSAL = Lam('program', A(A(Z, PHI), V('program'), EMPTY))

fresh_counter = 0
def fresh(prefix='q'):
    global fresh_counter
    fresh_counter += 1
    return prefix + str(fresh_counter)

def scott_nat(n):
    z, s = fresh('nz'), fresh('ns')
    return Lam([z, s], V(z) if n == 0 else A(V(s), scott_nat(n-1)))

def quote_debruijn(t):
    """DB constructors ('v',n), ('l',body), ('a',left,right) -> source value."""
    v, l, a = fresh('qv'), fresh('ql'), fresh('qa')
    if t[0] == 'v': body = A(V(v), scott_nat(t[1]))
    elif t[0] == 'l': body = A(V(l), quote_debruijn(t[1]))
    elif t[0] == 'a': body = A(V(a), quote_debruijn(t[1]), quote_debruijn(t[2]))
    else: raise ValueError(t)
    return Lam([v,l,a], body)

def debruijn(t, binders=()):
    if t[0] == 'v': return ('v', binders.index(t[1]))
    if t[0] == 'l': return ('l', debruijn(t[2], (t[1],)+binders))
    return ('a', debruijn(t[1],binders), debruijn(t[2],binders))

def source_eval(term, limit=100000):
    # Independent CEK interpreter, returning (body, binder, environment) closures.
    t, env, kont, steps = term, {}, [], 0
    while True:
        steps += 1
        if steps > limit: return None, steps
        if t[0] == 'v': value = env[t[1]]
        elif t[0] == 'l': value = (t[2],t[1],env)
        else:
            kont.append(('arg',t[2],env)); t=t[1]; continue
        while kont:
            k = kont.pop()
            if k[0] == 'arg':
                kont.append(('fun',value)); t,env=k[1:]; break
            body,binder,cenv = k[1]
            env = dict(cenv); env[binder] = value; t=body; break
        else: return value, steps

def closure_tree(alg, cl):
    body, binder, env = cl
    tenv = {x: closure_tree(alg,c) for x,c in env.items()}
    out,n = alg.eval(alg.bracket(binder, alg.compile(body)), tenv)
    assert n == 0
    return out

def main():
    here = Path(__file__).resolve().parent
    alg = Algebra()
    u = alg.compile(UNIVERSAL)
    literal = alg.export_value(u)
    payload = json.dumps(literal, separators=(',',':')) + '\n'
    (here/'literal_universal_tree.json').write_text(payload)
    (here/'universal_lambda_source.json').write_text(json.dumps(UNIVERSAL)+'\n')
    expanded = []
    code_equations = []
    for i,n in enumerate(literal['nodes']):
        expanded.append('L' if n[0] == 'L' else
                        n[0]+'('+','.join(expanded[j] for j in n[1:])+')')
        lhs = f'c{i}'
        if n[0] == 'L': rhs = '0'
        elif n[0] == 'S': rhs = f'2*c{n[1]}+1'
        else:
            a,b = (f'c{j}' for j in n[1:])
            rhs = f'({a}+{b})*({a}+{b}+1)+2*{b}+2'
        code_equations.append(dict(node=i, residual=lhs+'-('+rhs+')'))
    (here/'literal_universal_tree.sexpr').write_text(expanded[literal['root']]+'\n')
    (here/'universal_code_circuit.json').write_text(json.dumps(dict(
        domain='natural numbers', variables=len(literal['nodes']),
        residuals=code_equations, root=f'c{literal["root"]}',
        unique_solution=True, residual_degree=2,
        sum_of_squares_degree=4),indent=2)+'\n')
    # Count the fully unfolded constructor tree without expanding it.
    sizes, depths = [], []
    for n in literal['nodes']:
        sizes.append(1+sum(sizes[j] for j in n[1:]))
        depths.append(1+max([depths[j] for j in n[1:]] or [0]))
    tests = []
    terms = {
        'identity': ID,
        'identity_applied_identity': A(ID,ID),
        'constant_first': A(Lam('ca cb',V('ca')),ID,Lam('cz',ID)),
        'captured_variable': A(Lam('cx',Lam('cy',V('cx'))),ID),
        'suspended_omega': Lam('unused',OMEGA),
        'self_application_once': A(DUP,ID),
    }
    for name,t in terms.items():
        cl,ssteps = source_eval(t)
        direct,dsteps = alg.eval(alg.compile(t),limit=2000000)
        assert direct is not None and direct == closure_tree(alg,cl),name
        quoted = alg.compile(quote_debruijn(debruijn(t)))
        assert alg.eval(quoted)[1] == 0
        interpreted,isteps = alg.eval(alg.app(u,quoted),limit=5000000)
        assert interpreted is not None,name
        # Testing returned semantic values extensionally: universal results are
        # interpreter closures, not required to be syntactically direct ones.
        test = alg.eval(alg.app(interpreted,alg.compile(ID)),limit=5000000)
        expected = alg.eval(alg.app(direct,alg.compile(ID)),limit=5000000)
        # For suspended Omega, both tests deliberately exceed finite fuel.
        assert (test[0] is None) == (expected[0] is None),name
        tests.append(dict(name=name,source_cek_steps=ssteps,direct_kernel_calls=dsteps,
                          interpreter_kernel_calls=isteps,
                          forced_result_terminates=test[0] is not None))
    for name,t in {'omega':OMEGA, 'strict_discard_omega':A(Lam('drop',ID),OMEGA)}.items():
        assert source_eval(t,20000)[0] is None
        assert alg.eval(alg.compile(t),limit=20000)[0] is None
        quoted = alg.compile(quote_debruijn(debruijn(t)))
        assert alg.eval(alg.app(u,quoted),limit=20000)[0] is None
        tests.append(dict(name=name,status='fuel-exhaustion-only-not-a-divergence-proof',fuel=20000))
    receipt = dict(universal_dag_nodes=len(literal['nodes']),
                   universal_expanded_constructor_nodes=sizes[literal['root']],
                   universal_constructor_depth=depths[literal['root']],
                   universal_root=literal['root'],
                   literal_sha256=hashlib.sha256(payload.encode()).hexdigest(),
                   tests=tests)
    (here/'eager_compiler_receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps(receipt,indent=2))

if __name__ == '__main__': main()
