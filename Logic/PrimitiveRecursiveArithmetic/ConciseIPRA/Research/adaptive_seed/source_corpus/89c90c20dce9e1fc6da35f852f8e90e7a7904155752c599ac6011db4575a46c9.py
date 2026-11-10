"""Untrusted proof compiler from Choice-DI to eliminator-only assumptions.

The checker imports none of this file.  This compiler first extracts a
finite old derivation, replaces object-language Q by a vacuous D, and
expands identity structurally.  It then emits the new depth-first packet.
"""
import ast
import copy
import json
import math
from pathlib import Path

HERE = Path(__file__).resolve().parent
BASE = HERE / 'choice_checker.py'
Z = ('z',)
serial = 0


def fresh(prefix='b'):
    global serial
    serial += 1
    return prefix + str(serial)


def V(x): return ('v', x)
def S(t): return ('s', t)
def I(n, a, u, h): return ('i', n, a, u, h)
def E(s, t): return ('e', s, t)
def Q(y, b): return ('q', y, b)
def D(x, y, b): return ('d', x, y, b)


def subst(a, x, t):
    tag = a[0]
    if tag == 'v': return t if a[1] == x else a
    if tag == 'z': return a
    if tag == 's': return S(subst(a[1], x, t))
    if tag == 'i':
        _, n, b, u, h = a
        return I(subst(n,x,t), subst(b,x,t), u, h if u == x else subst(h,x,t))
    if tag == 'e': return E(subst(a[1],x,t), subst(a[2],x,t))
    if tag == 'q': return a if a[1] == x else Q(a[1],subst(a[2],x,t))
    if tag == 'd': return a if x in a[1:3] else D(a[1],a[2],subst(a[3],x,t))
    raise ValueError(tag)


def instantiate(b, x, t, y=None, u=None):
    b = subst(b, x, t)
    return subst(b, y, u) if y is not None else b


class Decoder:
    def __init__(self, floor): self.floor = floor

    def n(self, a, env=(), hole=None):
        if type(a) is list:
            if not a: return Z
            if len(a) == 1: return S(self.n(a[0], (Z,) + env, hole))
            if len(a) == 2: return Z
            if len(a) == 3:
                u = fresh()
                return I(self.n(a[0], (Z,Z)+env, hole),
                         self.n(a[1], (Z,Z)+env, hole), u,
                         self.n(a[2], (V(u),V(u))+env, hole))
            raise ValueError('bad numerical arity')
        if not isinstance(a, (int,float)) or not math.isfinite(a):
            if hole is not None: return hole
            raise ValueError('bad numerical leaf')
        j = math.floor(a)
        if a >= self.floor and a < 2*len(env)+1:
            if j < 0: return V('old' + str(j))
            if j == 0: return Z
            return env[(j-1)//2]
        if hole is not None: return hole
        raise ValueError('unbound numerical coordinate')

    def f(self, a, env=(), hole=None):
        if type(a) is not list or not a: return E(Z,Z)
        if len(a) == 1:
            y = fresh()
            return Q(y, self.f(a[0], (V(y),)+env, hole))
        if len(a) == 2:
            return E(self.n(a[0],env,hole), self.n(a[1],env,hole))
        if len(a) == 3:
            x,y = fresh(),fresh()
            return D(x,y,self.f(a[2],(V(y),V(x))+env,hole))
        raise ValueError('bad formula arity')


def namespace(path):
    tree = ast.parse(Path(path).read_text())
    while isinstance(tree.body[-1], (ast.Try,ast.Expr)):
        tree.body.pop()
    ns = {}
    exec(compile(tree, str(path), 'exec'), ns)
    return ns


class Extract:
    def __init__(self, packet, focused=False):
        self.ns = namespace(BASE)
        self.ns['k'] = 0
        self.data = copy.deepcopy(packet)
        self.focused = focused

    def i(self, a, t=None, d=0): return self.ns['i'](a,t,d)
    def dec(self): return Decoder(self.ns['k'])

    def go(self,a,g):
        normal = self.i(a)
        goal = self.dec().f(a)
        if not self.focused and normal in g:
            return {'kind':'hyp','goal':goal,'index':g.index(normal)}
        m,t = self.data.pop()
        if m:
            if self.focused and self.i(m) in g:
                major = {'kind':'hyp','goal':self.dec().f(m),
                         'index':g.index(self.i(m))}
            else:
                major = self.go(m,g)
            dec = self.dec()
            if len(m) == 1:
                try: witness = dec.n(t)
                except ValueError: witness = Z
                assert self.i(m[0],t) == a
                minor = self.go(self.i(m[0],0),g)
                return {'kind':'qe','goal':goal,'major':major,'minor':minor,'witness':witness}
            if len(m) == 2:
                v = fresh('hole')
                template = dec.f(t,hole=V(v))
                assert self.i(t,m[1]) == a
                minor = self.go(self.i(t,m[0]),g)
                return {'kind':'tr','goal':goal,'major':major,'minor':minor,
                        'variable':v,'template':template}
            assert len(m) == 3
            self.ns['k'] -= 1
            a_name = 'old' + str(self.ns['k'])
            assumption = self.i(m[2:],self.ns['k'])
            minor = self.go(self.i(a,[self.ns['k']]), g+[assumption])
            return {'kind':'de','goal':goal,'major':major,'minor':minor,'eigen':a_name}
        if t:
            dec = self.dec()
            try: witness = dec.n(t)
            except ValueError: witness = Z
            opened = self.i(a[2],t,2)
            mode = 1 if len(opened)%2 == m else 0
            self.ns['k'] -= 1
            z = 'old' + str(self.ns['k'])
            assumption = self.i(opened,self.ns['k'] if mode else 0)
            minor = self.go(self.i(opened,[self.ns['k']]),g+[assumption])
            return {'kind':'di','goal':goal,'witness':witness,'mode':mode,'eigen':z,'minor':minor}
        (n,b,r),u = a
        if n:
            n, = n
            b = self.i(r,[n,b,r],1)
        assert u == b
        return {'kind':'comp','goal':goal}

    def run(self):
        goal = self.data.pop()
        return self.go(self.i(goal) if self.focused else goal,[])


def translate_formula(a):
    if a[0] == 'e': return a
    if a[0] == 'd': return D(a[1],a[2],translate_formula(a[3]))
    if a[0] == 'q': return D(fresh('unused'),a[1],translate_formula(a[2]))
    raise ValueError(a)


def P(kind,goal,**kw): return {'kind':kind,'goal':goal,**kw}
def ref(a): return P('ref',a)
def hyp(a): return P('eta',a)
def comp(a): return P('comp',a)


def tr(major,minor,v,template):
    assert major['goal'][0] == 'e'
    return P('tr',subst(template,v,major['goal'][2]),major=major,minor=minor,
             variable=v,template=template)


def refl(t):
    u,v = fresh(),fresh('hole')
    r = I(Z,t,u,Z)
    ax = comp(E(r,t))
    return tr(ax,ax,v,E(V(v),t))


def symmetry(major):
    v = fresh('hole')
    s,t = major['goal'][1:]
    return tr(major,refl(s),v,E(V(v),s))


def qe(clause,witness,minor):
    assert clause[0] == 'q'
    return P('qe',subst(clause[2],clause[1],witness),major=ref(clause),
             witness=witness,minor=minor)


def quote_clause(clause, goal=None):
    _,y,b = clause
    if goal is None: goal = D(fresh('unused'),y,b)
    x,y0,body = goal[1:]
    z = fresh('eig')
    # The witness coordinate is unused. One is truthy and needs no boxing.
    witness = S(Z)
    base = instantiate(body,x,witness,y0,Z)
    successor = qe(clause,S(V(z)),hyp(base))
    return P('di',goal,witness=witness,mode=0,eigen=z,minor=successor)


def translate(node, env=()):
    kind = node['kind']
    goal = translate_formula(node['goal'])
    if kind == 'hyp': return env[node['index']]
    if kind == 'comp': return comp(goal)
    if kind == 'tr':
        return tr(translate(node['major'],env),translate(node['minor'],env),
                  node['variable'],translate_formula(node['template']))
    if kind == 'qe':
        major = translate(node['major'],env)
        _,x,y,b = major['goal']
        a = fresh('eig')
        clause = Q(y,subst(b,x,V(a)))
        minor = qe(clause,node['witness'],translate(node['minor'],env))
        return P('de',goal,major=major,eigen=a,minor=minor)
    if kind == 'de':
        major = translate(node['major'],env)
        _,x,y,b = major['goal']
        a = node['eigen']
        clause = Q(y,subst(b,x,V(a)))
        provider = quote_clause(clause)
        minor = translate(node['minor'],env+(provider,))
        return P('de',goal,major=major,eigen=a,minor=minor)
    if kind == 'di':
        _,x,y,b = goal
        w,z,mode = node['witness'],node['eigen'],node['mode']
        eta = V(z) if mode else Z
        assumption = instantiate(b,x,w,y,eta)
        if w != Z:
            minor = translate(node['minor'],env+(hyp(assumption),))
            return P('di',goal,witness=w,mode=mode,eigen=z,minor=minor)
        # A zero witness must be syntactically nonempty. Box it by I0 and
        # transport both the retained hypothesis and the final conclusion.
        wbox = I(Z,Z,fresh(),Z)
        eq = comp(E(wbox,Z))
        v = fresh('hole')
        boxed_assumption = instantiate(b,x,wbox,y,eta)
        provider = tr(eq,hyp(boxed_assumption),v,instantiate(b,x,V(v),y,eta))
        minor = translate(node['minor'],env+(provider,))
        result = tr(symmetry(eq),minor,v,instantiate(b,x,V(v),y,S(V(z))))
        return P('di',goal,witness=wbox,mode=mode,eigen=z,minor=result)
    raise ValueError(kind)


def expand_identity(goal):
    if goal[0] == 'e':
        s,t = goal[1:]
        v = fresh('hole')
        return tr(ref(goal),refl(s),v,E(s,V(v)))
    if goal[0] == 'd':
        _,x,y,b = goal
        a,z = fresh('eig'),fresh('eig')
        clause = Q(y,subst(b,x,V(a)))
        base = instantiate(b,x,V(a),y,Z)
        minor = qe(clause,S(V(z)),hyp(base))
        introduction = P('di',goal,witness=V(a),mode=0,eigen=z,minor=minor)
        return P('de',goal,major=ref(goal),eigen=a,minor=introduction)
    raise ValueError('Identity expansion is for Eq/D object formulas only')


class Emitter:
    def __init__(self):
        self.floor = 0
        self.names = {}
        self.instructions = []
        self.identity_expansions = 0

    def n(self,a,env=(),hole=None):
        tag = a[0]
        if tag == 'z': return 0
        if tag == 'v':
            name = a[1]
            if name in env: return 2*env.index(name)+1
            if name == hole: return 2*len(env)+1
            if name in self.names: return self.names[name]
            if name.startswith('old'): return 0
            raise ValueError('unallocated name '+name)
        if tag == 's': return [self.n(a[1],(None,)+env,hole)]
        if tag == 'i':
            _,n,b,u,h = a
            return [self.n(n,(None,None)+env,hole),
                    self.n(b,(None,None)+env,hole),
                    self.n(h,(u,u)+env,hole)]
        raise ValueError(tag)

    def f(self,a,env=(),hole=None):
        tag = a[0]
        if tag == 'e': return [self.n(a[1],env,hole),self.n(a[2],env,hole)]
        if tag == 'q': return [self.f(a[2],(a[1],)+env,hole)]
        if tag == 'd': return [0,0,self.f(a[3],(a[2],a[1])+env,hole)]
        raise ValueError(tag)

    def allocate(self,name):
        self.floor -= 1
        if name in self.names:
            # Duplicated proof subtrees may reuse a local schematic name.
            # Its scope does not escape that subtree; this shadows it.
            pass
        self.names[name] = self.floor

    def member(self,a,g): return self.f(a) in [self.f(b) for b in g]

    def major(self,p,g):
        if self.member(p['goal'],g): return
        if p['kind'] == 'ref': raise ValueError('Missing referenced assumption')
        self.go(p,g)

    def go(self,p,g=()):
        kind,goal = p['kind'],p['goal']
        if kind in ('eta','ref'):
            if not self.member(goal,g):
                raise ValueError('Identity requested outside context')
            self.identity_expansions += 1
            return self.go(expand_identity(goal),g)
        if kind == 'comp':
            self.instructions.append([0,0]); return
        if kind == 'tr':
            self.instructions.append([self.f(p['major']['goal']),self.f(p['template'],hole=p['variable'])])
            self.major(p['major'],g)
            self.go(p['minor'],g)
            return
        if kind == 'qe':
            self.instructions.append([self.f(p['major']['goal']),self.n(p['witness'])])
            self.major(p['major'],g)
            self.go(p['minor'],g)
            return
        if kind == 'de':
            self.instructions.append([self.f(p['major']['goal']),0])
            self.major(p['major'],g)
            self.allocate(p['eigen'])
            _,x,y,b = p['major']['goal']
            clause = Q(y,subst(b,x,V(p['eigen'])))
            self.go(p['minor'],g+(clause,))
            return
        if kind == 'di':
            witness = self.n(p['witness'])
            assert witness
            self.instructions.append([0 if p['mode'] else [],witness])
            self.allocate(p['eigen'])
            _,x,y,b = goal
            at = V(p['eigen']) if p['mode'] else Z
            assumption = instantiate(b,x,p['witness'],y,at)
            self.go(p['minor'],g+(assumption,))
            return
        raise ValueError(kind)

    def run(self,p):
        goal = self.f(p['goal'])
        self.go(p)
        return list(reversed(self.instructions)) + [goal]


class OldEmitter(Emitter):
    """Serialize the same derivation for the independently frozen old checker."""
    def go(self,p,g=()):
        if self.member(p['goal'],g): return
        return super().go(p,g)


def compile_packet(packet):
    source = Extract(packet).run()
    target = translate(source)
    emitter = Emitter()
    result = emitter.run(target)
    return result, {'instructions':len(emitter.instructions),
                    'fresh_parameters':-emitter.floor,
                    'identity_expansions':emitter.identity_expansions}


def run_packet(path,packet,focused=None):
    if focused is None:
        focused = Path(path).name != 'choice_checker.py'
    ns = namespace(path)
    ns['k'] = 0
    data = copy.deepcopy(packet)
    try:
        ns['q'] = data.pop
        goal = ns['i'](data.pop()) if focused else data.pop()
        value = bool(ns['c'](goal,[]))
        return value,ns['k'],len(data)
    except Exception as exc:
        return False,ns['k'],len(data) if hasattr(data,'__len__') else 0,type(exc).__name__


if __name__ == '__main__':
    import sys
    source = json.loads(Path(sys.argv[1]).read_text())
    packet = source.get('packet',source) if isinstance(source,dict) else source
    result,metadata = compile_packet(packet)
    output = Path(sys.argv[2])
    output.write_text(json.dumps(result,separators=(',',':'))+'\n')
    print(json.dumps(metadata,indent=2))
    print(run_packet(HERE/'kernel_bytes.py',result))
