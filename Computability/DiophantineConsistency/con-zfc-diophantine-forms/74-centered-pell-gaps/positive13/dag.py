"""Shared binary arithmetic DAG helper; no polynomial semantics."""
PORTS = ["beta","K0","MC","MF"]

class DAG:
    def __init__(self): self.rows=[]; self.cache={}
    def g(self,op,x,y,name=None):
        if op in ('+','*') and str(x)>str(y): x,y=y,x
        key=(op,x,y)
        if key in self.cache: return self.cache[key]
        name=name or 'g'+str(len(self.rows))
        if any(r[0]==name for r in self.rows): raise ValueError(name)
        self.rows.append([name,op,x,y]); self.cache[key]=name; return name
    def add(self,x,y,name=None): return self.g('+',x,y,name)
    def sub(self,x,y,name=None): return self.g('-',x,y,name)
    def mul(self,x,y,name=None): return self.g('*',x,y,name)
    def sq(self,x,name=None): return self.mul(x,x,name)
    def live(self,roots):
        needed=set(roots)
        for name,op,x,y in reversed(self.rows):
            if name in needed: needed.update((x,y))
        return [r for r in self.rows if r[0] in needed],needed


