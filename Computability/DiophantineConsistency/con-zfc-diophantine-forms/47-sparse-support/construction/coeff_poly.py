"""Small exact four-port polynomial parser, using no third-party libraries."""
import ast

def parse_poly(expression,names):
    zero=(0,)*len(names)
    def add(a,b,sgn=1):
        out=dict(a)
        for e,c in b.items():
            out[e]=out.get(e,0)+sgn*c
            if not out[e]: del out[e]
        return out
    def mul(a,b):
        out={}
        for e,c in a.items():
            for f,d in b.items():
                k=tuple(x+y for x,y in zip(e,f));out[k]=out.get(k,0)+c*d
        return {e:c for e,c in out.items() if c}
    def visit(t):
        if isinstance(t,ast.Constant) and type(t.value) is int:
            return {zero:t.value} if t.value else {}
        if isinstance(t,ast.Name) and t.id in names:
            e=list(zero);e[names.index(t.id)]=1;return {tuple(e):1}
        if isinstance(t,ast.UnaryOp) and isinstance(t.op,ast.USub):
            return {e:-c for e,c in visit(t.operand).items()}
        if isinstance(t,ast.BinOp):
            if isinstance(t.op,ast.Add):return add(visit(t.left),visit(t.right))
            if isinstance(t.op,ast.Sub):return add(visit(t.left),visit(t.right),-1)
            if isinstance(t.op,ast.Mult):return mul(visit(t.left),visit(t.right))
            if isinstance(t.op,ast.Pow) and isinstance(t.right,ast.Constant) and type(t.right.value) is int and 0<=t.right.value<=8:
                v=visit(t.left);r={zero:1}
                for _ in range(t.right.value):r=mul(r,v)
                return r
        raise ValueError('Unsupported coefficient expression: '+ast.dump(t))
    return visit(ast.parse(expression,mode='eval').body)
