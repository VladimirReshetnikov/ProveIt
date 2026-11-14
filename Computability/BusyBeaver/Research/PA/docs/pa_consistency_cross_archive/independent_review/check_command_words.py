#!/usr/bin/env python3
"""Generic m-head command identities for the two new combined AX emitters.

Head and gate expressions are abstract values of residue zero. The source
review independently binds the actual expressions to those positions. Opaque
stack tails are never inspected. Unknown arithmetic equalities raise errors.
"""
from dataclasses import dataclass
from itertools import product
import json

@dataclass(frozen=True)
class Expr:
    kind: str
    args: tuple

def E(kind, *args):
    return Expr(kind, args)

def var(name, fact='arbitrary'):
    return E('var', name, fact)

def plus(a, b):
    if a == 0:
        return b
    if b == 0:
        return a
    if isinstance(a, int) and isinstance(b, int):
        return a + b
    return E('add', a, b)

def I(a, b):
    return 0 if a == b == 0 else E('imp', a, b)

def U(a, b):
    return E('forall', a, b)

def gamma(a):
    return I(a, U(a, a))

def residue(a):
    if isinstance(a, int):
        return a % 4
    return {'imp':0, 'head':0, 'rho':0, 'gate8':0, 'gate9':0, 'forall':2}.get(a.kind)

def positive(a):
    if isinstance(a, int):
        return a > 0
    if a.kind == 'forall':
        return True
    if a.kind in ('imp', 'add'):
        return any(positive(x) for x in a.args)
    return a.kind == 'var' and a.args[1] == 'positive'

def equal(a, b):
    if a == b:
        return True
    if isinstance(a, int) and isinstance(b, int):
        return False
    ra, rb = residue(a), residue(b)
    if ra is not None and rb is not None and ra != rb:
        return False
    if a == 0 and positive(b) or b == 0 and positive(a):
        return False
    for x, y in ((a, b), (b, a)):
        if x == 1 and isinstance(y, Expr) and y.kind == 'var' and y.args[1] == 'not_one':
            return False
    raise ValueError(('Unresolved symbolic equality', a, b))

@dataclass(frozen=True)
class Stack:
    prefix: tuple = ()
    tail: str = 'w'
    def push(self, values):
        return Stack(tuple(values) + self.prefix, self.tail)
    def pop(self):
        if not self.prefix:
            raise ValueError('Attempted to inspect opaque arbitrary stack tail')
        return self.prefix[0], Stack(self.prefix[1:], self.tail)

@dataclass(frozen=True)
class Store:
    top: object
    stack: Stack
    offset: object
    cache: object

SHIFT = ('shift',)
def AX(c=0, x=0, y=0):
    return ('ax', c, x, y)
def MP(x=0):
    return ('mp', x)

def head_values(m, D, H, c, d, h):
    old = tuple(E('head', j, D, H, c) for j in range(1, 7)) + (E('rho', D, c, H, d), U(d, h))
    return ((gamma(c),) + old) if m == 9 else old

def gate(m, H, D, c):
    # Includes the guarded-zero case; no positivity or nonzero fact is used.
    return E('gate' + str(m), H, D, c)

def run(m, word, s):
    for command in word:
        if s is None:
            break
        if command[0] == 'shift':
            if equal(s.cache, 1):
                s = None
            else:
                head, tail = s.stack.pop()
                s = Store(s.cache, tail, s.offset, head)
        elif command[0] == 'mp':
            y = plus(s.offset, command[1])
            if equal(I(s.top, y), s.cache):
                s = Store(0, s.stack, 0, y)
            else:
                s = Store(0, s.stack, y, 0)
        elif command[0] == 'ax':
            _, c, x, y = command
            D, H = plus(s.offset, x), plus(s.cache, y)
            s = Store(gate(m, H, D, c), s.stack.push(head_values(m,D,H,c,s.offset,s.cache)+(s.top,)), 0, 0)
        else:
            raise ValueError('Unknown command')
    return s

def pop(m):
    return [AX()] + [SHIFT] * (m + 2)
def push(m):
    return [AX()] + [SHIFT] * m + [MP()]
def discard(m):
    return [MP(1), AX(1)] + [SHIFT] * (m + 1) + [MP()]
def offset(i):
    return [] if i == 0 else [MP(i)]
def generalize(m, i):
    return push(m) + offset(i) + [SHIFT, AX(i)] + [SHIFT] * (m + 1)
def select(m, j, D, H, c):
    return discard(m) + [AX(c,D,H)] + [SHIFT] * (j + 1) + pop(m) * (m - j)
def rho_select(m, a, b, c, u):
    return discard(m) + offset(u) + [AX(b,a-u,c)] + [SHIFT] * m + pop(m)
def gate_select(m, a, b, c):
    return discard(m) + [AX(c,b,a)] + pop(m) * (m + 1)
def mp_suffix(b):
    return [SHIFT, SHIFT, MP(b), SHIFT]

def check(m):
    count = 0
    def verify(name, actual, expected):
        nonlocal count
        if actual != expected:
            raise ValueError((m, name, actual, expected))
        count += 1
    w = Stack()
    t, a, b = [var(z, 'not_one') for z in ('t','a','b')]
    d, h, c, x, y = [var(z) for z in ('d','h','c','x','y')]
    for top in (0, 1, t):
        s = Store(top,w,d,h)
        verify('AX then m shifts', run(m,[AX(c,x,y)]+[SHIFT]*m,s),
               Store(E('rho',plus(d,x),c,plus(h,y),d),w.push((top,)),0,U(d,h)))
        verify('AX then m+1 shifts', run(m,[AX(c,x,y)]+[SHIFT]*(m+1),s),Store(U(d,h),w,0,top))
        verify('push',run(m,push(m),s),Store(0,w.push((top,)),0,0))
        verify('pop',run(m,pop(m),Store(top,w.push((a,)),d,h)),None if top==1 else Store(top,w,0,a))
        verify('discard',run(m,discard(m),Store(top,w,0,0)),Store(0,w,0,0))
        for i in (0,1,var('i','positive')):
            verify('generalize',run(m,generalize(m,i),Store(top,w,0,0)),Store(U(i,top),w,0,0))
        generated = head_values(m,x,y,c,0,0)
        for j in range(1,m-1):
            verify('primitive head selector',run(m,select(m,j,x,y,c),Store(top,w,0,0)),Store(generated[j-1],w,0,0))
        for u in range(3):
            verify('restricted rho selector',run(m,rho_select(m,4,7,9,u),Store(top,w,0,0)),Store(E('rho',4,7,9,u),w,0,0))
        verify('gate selector',run(m,gate_select(m,a,b,c),Store(top,w,0,0)),Store(gate(m,a,b,c),w,0,0))
    for aa,bb in product((0,1,a),(0,1,b)):
        s=Store(0,w.push((aa,I(aa,bb),0)),0,0)
        verify('MP suffix',run(m,mp_suffix(bb),s),None if aa==1 or bb==1 else Store(bb,w,0,0))
    verify('unconditional halt suffix from top1',run(m,pop(m),Store(1,w,d,h)),None)
    return {'m_generated_formulas':m,'total_pushed_including_saved_top':m+1,
            'symbolic_identities_checked':count,'pop_shift_count':m+2,
            'push_shift_count':m,'post_AX_generalization_shift_count':m+1,'status':'PASS'}

if __name__ == '__main__':
    print(json.dumps({'status':'PASS','cases':[check(8),check(9)],
                     'scope':'Symbolic finite-word identities with arbitrary opaque stack tails. Combined with the written induction, supports command proof compilation; no binary-tape or Lean theorem claimed.'},indent=2))
