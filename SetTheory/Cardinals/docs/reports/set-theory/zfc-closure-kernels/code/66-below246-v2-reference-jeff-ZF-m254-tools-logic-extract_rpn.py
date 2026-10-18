"""Extract the word list of axioms() (and mp/drop/nip/main) from source_local.py by stubbing the
TMBuilder primitives (no hand transcription), then evaluate the RPN symbolically.

Symbolic stack: tw = top, ws = list (ws[-1] = next below tw).  Initial stack symbols: T (topwff at
entry), S1, S2, ... (wffstack entries from the top).  Parameters p1, p2, p3 (param3 = axiomcode),
r (read into param2), q (literal read into topwff).

Usage: python extract_rpn.py      prints the token list, the resulting formula and the gate ops.
"""
import sys, os
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', '..', 'ext', 'turing_machine_explorer'))
sys.path.insert(0, HERE)
import source_local

class Sym(source_local.ZF2):
    pass

WORDS = ['v_0', 'v_1', 'v_2', 'v_3', 'v_4', 'par1', 'par2', 'par3', 'weq', 'wel', 'wim', 'wn', 'wal',
         'wex', 'wa', 'pushwff', 'load_5', 'select', 'cons', 'gen', 'times', 'times_from_scratch']
for w in WORDS:
    setattr(Sym, w, (lambda w: lambda self: (w,))(w))
Sym.read = lambda self, r: (('read', str(r)),)
Sym.pop = lambda self, r: (('pop', str(r)),)
Sym.unpair = lambda self, a, b, c: (('unpair', str(a), str(b), str(c)),)
Sym.pair = lambda self, a, b, c: (('pair', str(a), str(b), str(c)),)
Sym.while_decnz = lambda self, var, body: (('while_decnz', str(var), flat(body)),)
Sym.if_eq = lambda self, a, b, body: (('if_eq', str(a), str(b), flat(body)),)
Sym.if_not_decnz = lambda self, var, body: (('if_not_decnz', str(var), flat(body)),)
Sym.label = lambda self, name, seq: (('label', name, flat(seq)),)

def flat(x):
    """flatten nested lists/tuples of tokens; a token is a str or a tuple whose head is a str."""
    if isinstance(x, str):
        return [x]
    if isinstance(x, tuple) and x and isinstance(x[0], str) and len(x) > 1 and not all(isinstance(t, str) for t in x):
        return [x]
    out = []
    for e in x:
        if isinstance(e, tuple) and len(e) == 1 and isinstance(e[0], str):
            out.append(e[0])
        elif isinstance(e, tuple) and e and isinstance(e[0], str) and len(e) > 1:
            out.append(e)
        else:
            out.extend(flat(e))
    return out

def undecorated(method):
    f = getattr(source_local.ZF2, method)
    if f.__closure__:          # @subroutine wrapper: the original function is the closure cell
        for c in f.__closure__:
            if callable(c.cell_contents):
                return c.cell_contents
    return f

def raw_tokens(method):
    return flat(undecorated(method)(Sym()))

for _m in ['main', 'mp', 'drop', 'nip', 'axioms']:
    setattr(Sym, _m, (lambda m: lambda self: undecorated(m)(self))(_m))

# ---- symbolic formulas: tuples ('Imp',a,b) ('All',x,a) ('Eq',x,y) ('Rel',x,y), leaves str or int
def show(f):
    if isinstance(f, (str, int)):
        return str(f)
    h = f[0]
    if h == 'Imp' and f[2] == 1:
        return f'~{show(f[1])}'
    if h == 'Imp':
        return f'({show(f[1])} -> {show(f[2])})'
    if h == 'All':
        return f'A.{show(f[1])} {show(f[2])}'
    if h == 'Eq':
        return f'{show(f[1])}={show(f[2])}'
    if h == 'Rel':
        return f'R({show(f[1])},{show(f[2])})'
    raise ValueError(f)

def show2(f):
    """pretty-print with derived connectives recognised: ~A, A/\\B, E.x A."""
    if isinstance(f, (str, int)):
        return {1: 'F', 0: 'TT'}.get(f, str(f)) if isinstance(f, int) else f
    h = f[0]
    if h == 'Imp' and f[2] == 1:
        a = f[1]
        # wa: ~(A -> ~B)
        if isinstance(a, tuple) and a[0] == 'Imp' and isinstance(a[2], tuple) and a[2][0] == 'Imp' and a[2][2] == 1:
            return f'({show2(a[1])} /\\ {show2(a[2][1])})'
        # wex: ~A.x ~B
        if isinstance(a, tuple) and a[0] == 'All' and isinstance(a[2], tuple) and a[2][0] == 'Imp' and a[2][2] == 1:
            return f'E.{show2(a[1])} {show2(a[2][1])}'
        return f'~{show2(a)}'
    if h == 'Imp':
        return f'({show2(f[1])} -> {show2(f[2])})'
    if h == 'All':
        return f'A.{show2(f[1])} {show2(f[2])}'
    if h == 'Eq':
        return f'{show2(f[1])}={show2(f[2])}'
    if h == 'Rel':
        return f'R({show2(f[1])},{show2(f[2])})'
    raise ValueError(f)

def symrun(toks, env, ninit=6):
    """Run the RPN words symbolically. env maps param names to symbols. Returns (tw, ws, log)."""
    tw = 'T'
    ws = [f'S{i}' for i in range(ninit, 0, -1)]   # ws[-1] = S1
    log = []
    def push(x):
        nonlocal tw
        ws.append(tw); tw = x
    def cons(tag):
        nonlocal tw
        x = ws.pop(); tw = (tag, x, tw)
    for t in toks:
        if t == 'pushwff' or t == 'v_0': push(0)
        elif t in ('v_1', 'v_2', 'v_3', 'v_4'): push(int(t[2]))
        elif t in ('par1', 'par2', 'par3'): push(env[t[3]])
        elif t == 'wim': cons('Imp')
        elif t == 'wel': cons('Rel')
        elif t == 'weq': cons('Eq')
        elif t == 'wal': cons('All')
        elif t == 'wn': push(1); cons('Imp')
        elif t == 'wex':
            push(1); cons('Imp'); cons('All'); push(1); cons('Imp')
        elif t == 'wa':
            push(1); cons('Imp'); cons('Imp'); push(1); cons('Imp')
        else:
            log.append((t, show(tw)))
            if isinstance(t, tuple) and t[0] == 'read' and t[1] == 'param2':
                env['2'] = f"({env['2']}+r)"
            elif isinstance(t, tuple) and t[0] == 'unpair' and t[3] == 'prooflist':
                pass
            elif isinstance(t, tuple) and t[0] == 'while_decnz' and t[1] == 'scratch1' and t[2] == ['3.topwff.inc']:
                tw = 'q'   # tw was 0 (pushwff); now tw := literal read q
    return tw, ws, log

if __name__ == '__main__':
    for m in ['main', 'mp', 'drop', 'nip', 'axioms']:
        s = Sym()
        print(m, raw_tokens(m))

def axioms_symbolic(ninit=8):
    toks = raw_tokens('axioms')
    env = {'1': 'a', '2': 'b', '3': 'c'}
    tw = 'T'; ws = [f'S{i}' for i in range(ninit, 0, -1)]
    def push(x):
        nonlocal tw
        ws.append(tw); tw = x
    def cons(tag):
        nonlocal tw
        x = ws.pop(); tw = (tag, x, tw)
    gates = []
    for t in toks:
        if t in ('pushwff', 'v_0'): push(0)
        elif t in ('v_1', 'v_2', 'v_3', 'v_4'): push(int(t[2]))
        elif t in ('par1', 'par2', 'par3'): push(env[t[3]])
        elif t == 'wim': cons('Imp')
        elif t == 'wel': cons('Rel')
        elif t == 'weq': cons('Eq')
        elif t == 'wal': cons('All')
        elif t == 'wn': push(1); cons('Imp')
        elif t == 'wex': push(1); cons('Imp'); cons('All'); push(1); cons('Imp')
        elif t == 'wa': push(1); cons('Imp'); cons('Imp'); push(1); cons('Imp')
        elif t == ('read', 'param2'): env['2'] = 'B'          # B = b + r
        elif t == ('unpair', 'scratch1', 'scratch2', 'prooflist'): pass
        elif t == ('while_decnz', 'scratch2', ['3.prooflist.inc']): pass
        elif t == ('while_decnz', 'scratch1', ['3.topwff.inc']):
            assert tw == 0; tw = 'q'                           # literal read
        else:
            gates.append(t)
    return tw, ws, gates

def conjuncts(f):
    """split nested wa-conjunctions ~(A -> ~B)."""
    if isinstance(f, tuple) and f[0] == 'Imp' and f[2] == 1:
        a = f[1]
        if isinstance(a, tuple) and a[0] == 'Imp' and isinstance(a[2], tuple) and a[2][0] == 'Imp' and a[2][2] == 1:
            return conjuncts(a[1]) + conjuncts(a[2][1])
    return [f]

if __name__ == '__main__':
    tw, ws, gates = axioms_symbolic()
    print('remaining stack below tw:', ws)
    print('gates:', gates)
    for i, c in enumerate(conjuncts(tw)):
        print(i, show2(c))
