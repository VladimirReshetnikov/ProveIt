#!/usr/bin/env python3
"""Own read-only literal constructor audit; never executes supplied code."""
from pathlib import Path
import hashlib,json,re
ROOT=Path(__file__).resolve().parent
def sha(b):
    return hashlib.sha256(b).hexdigest()

def tokens(s):
    return re.findall(r'[A-Za-z_][A-Za-z_0-9.]*|τ|≼|[()]', s)

def imp(a, b):
    return ('imp', a, b)

def subst(t, env):
    return tuple(subst(x, env) for x in t) if isinstance(t, tuple) else env.get(t, t)

class Reader:
    def __init__(self, s, env=None, facts=None):
        self.ts = tokens(s)
        self.i = 0
        self.env = env or {}
        self.facts = facts or {}

    def pop(self, want=None):
        x = self.ts[self.i]
        self.i += 1
        assert want is None or x == want, (want, x, self.ts[self.i:])
        return x

    def group(self, fn):
        if self.ts[self.i] == '(':
            self.pop('(')
            out = fn()
            self.pop(')')
            return out
        return fn()

    def term(self):
        return self.group(self.atom)

    def atom(self):
        x = self.pop()
        if x in ('wim', 'L.imp'):
            return imp(self.term(), self.term())
        assert re.fullmatch(r'v\d+|[a-z]|τ|_', x), x
        return self.env.get(x, x)

    def guard(self, expected):
        def core():
            name = self.pop()
            u, a = expected
            if name == 'L.refl':
                val = self.term()
                assert u == a and (val == '_' or val == a), (name, expected, val)
            elif name == 'le_l':
                y = self.term()
                assert isinstance(a, tuple) and a[0] == 'imp' and a[2] == y
                self.guard((u, a[1]))
            elif name == 'le_r':
                x = self.term()
                assert isinstance(a, tuple) and a[0] == 'imp' and a[1] == x
                self.guard((u, a[2]))
            else:
                assert self.facts[name] == expected, (name, self.facts, expected)
            return expected
        return self.group(core)

    def proof(self):
        def core():
            name = self.pop()
            if name == 'h.mp':
                major, minor = self.proof(), self.proof()
                assert isinstance(major, tuple) and major[0] == 'imp'
                assert major[1] == minor, ('MP mismatch', major[1], minor)
                counts['mp'] += 1
                return major[2]
            if name == 'h.rho8':
                a, b, c, u = [self.term() for _ in range(4)]
                self.guard((u, a))
                counts['restricted_rows'] += 1
                return imp(imp(imp(c, u), a), imp(imp(a, c), imp(b, c)))
            if name == 'h.truth':
                counts['seed_uses'] += 1
                return 'τ'
            if name == 'under_antecedent':
                self.pop('h')
                z, xy = self.term(), self.proof()
                assert isinstance(xy, tuple) and xy[0] == 'imp'
                return imp(imp(z, xy[1]), imp(z, xy[2]))
            if name in schemas:
                self.pop('h')
                args, conclusion, guards = schemas[name]
                env = dict(zip(args, [self.term() for _ in args]))
                for guard in guards:
                    self.guard(subst(guard, env))
                return subst(conclusion, env)
            assert name in self.facts, name
            return self.facts[name]
        return self.group(core)

    def end(self):
        assert self.i == len(self.ts), self.ts[self.i:]


def audit(text, count):
    global schemas, counts
    schemas={};counts={'mp':0,'restricted_rows':0,'seed_uses':0}
    ms=list(re.finditer(r'private theorem (d\d+)\b',text)); rows=[]
    assert len(ms)==count
    for j,m in enumerate(ms):
        name=m.group(1); assert name=='d'+str(j+1)
        end=ms[j+1].start() if j+1<len(ms) else text.index('/-- Restricted rows',m.end())
        block=text[m.end():end];header,body=block.split(':=',1)
        args=[]
        for group in re.findall(r'\(([^():]+) : A\)',header):args.extend(group.split())
        guards=[]
        for g in re.findall(r'\(hb\d+ : (.*?)\)\s*:',header,re.S):
            r=Reader(g);u=r.term();r.pop('≼');a=r.term();r.end();guards.append((u,a))
        r=Reader(re.split(r':\s*T\s+',header)[-1]);target=r.term();r.end()
        r=Reader(body,facts={f'hb{i}':g for i,g in enumerate(guards)})
        actual=r.proof();r.end();assert actual==target,(name,actual,target)
        schemas[name]=(args,target,guards);rows.append({'name':name,'formula':target,'guards':guards})
    assert counts['seed_uses']==0
    return rows,counts.copy()

source=(ROOT/'inputs/DominatedImplication.upstream.lean').read_text()
old=(ROOT/'inputs/DominatedImplication.phase10.lean').read_text()
rows,counts=audit(source,58)
for word in ['WithSeed','h.truth','wim00','Nat.','sorry','native_decide']:
    assert word not in source,word
assert len(re.findall(r'\bh.mp\b',source))==59  # 58 steps plus public lift
assert source[source.index('universe v'):source.index('section\n')]==old[old.index('universe v'):old.index('private structure WithSeed')]
# Public headers differ only in whether the same explicit h binder is supplied
# by the section. Reconstitute that binder before exact text comparison.
for name in ['rho8_all','composition','lift_right']:
    pat=rf'(?m)^theorem {name}\b.*?:='
    a=re.search(pat,old,re.S).group()
    b=re.search(pat,source,re.S).group().replace('theorem '+name,'theorem '+name+' (h : Restricted L T)',1)
    assert a==b,(name,a,b)
for name in ['rho8_all','composition','lift_right']:
    assert '#print axioms '+name in source
# Extract old numbered formulas without executing their proof bodies.
oldrows=[]
for m in re.finditer(r'private theorem (d\d+)\b',old):
    h=old[m.end():].split(':=',1)[0]
    r=Reader(re.split(r':\s*T\s+',h)[-1]);t=r.term();r.end()
    oldrows.append((m.group(1),t))
oldmap={json.dumps(t):n for n,t in oldrows}
shared=[];new=[]
for row in rows:
    n=oldmap.get(json.dumps(row['formula']))
    (shared if n else new).append({'new':row['name'],'old':n,'formula':row['formula']})
record={'status':'PASS_INERT_FREE_CONSTRUCTOR_AND_API_READ','upstream_core_sha256':sha(source.encode()),'phase10_core_sha256':sha(old.encode()),'upstream_bytes':len(source.encode()),'upstream_lines':len(source.splitlines()),'phase10_bytes':len(old.encode()),'phase10_lines':len(old.splitlines()),'saved_bytes':len(old.encode())-len(source.encode()),'saved_lines':len(old.splitlines())-len(source.splitlines()),'checked_private_steps':58,'counts':counts,'public_lift_extra_mp':1,'same_public_interfaces_after_section_binder_expansion':True,'language_rho8_restricted_definitions_exact':True,'shared_numbered_formula_count':len(shared),'new_numbered_formula_count':len(new),'formula_mapping':shared,'new_formulas':new,'compiler_or_supplied_generator_execution':False}
(ROOT/'source-audit.json').write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps({k:v for k,v in record.items() if k not in ['formula_mapping','new_formulas']},indent=2))
