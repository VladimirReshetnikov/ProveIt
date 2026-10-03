#!/usr/bin/env python3
"""Literal direct three-register membrane frontend; no prime packing or exponent loader."""
from pathlib import Path
from collections import Counter
import json
ROOT=Path(__file__).resolve().parent

class Program:
    def __init__(self): self.rows={}; self.alias={}
    def add(self,l,r,n): self.put(l,('ADD',r,n))
    def sub(self,l,r,n,z): self.put(l,('SUB',r,n,z))
    def put(self,l,row):
        assert l not in self.rows and l not in self.alias,l
        self.rows[l]=row
    def link(self,l,n):
        assert l not in self.rows and l not in self.alias,l
        self.alias[l]=n
    def resolve(self,l):
        seen=set()
        while l in self.alias:
            assert l not in seen,l
            seen.add(l);l=self.alias[l]
        assert l in self.rows or l=='HALT',l
        return l
    def literal(self):
        return {l: [row[0],row[1],*(self.resolve(n) for n in row[2:])]
                for l,row in self.rows.items()}

def read_tm():
    source=(ROOT/'source/UniversalTM15x2.tm.txt').read_text().splitlines()[0]
    pieces=source.split('_'); assert len(pieces)==15
    out={}
    for qi,piece in enumerate(pieces):
        assert len(piece)==6
        for s in (0,1):
            cell=piece[3*s:3*s+3];q=chr(65+qi)
            if cell=='---':out[f'{q}{s}']=None
            else:
                w,d,n=cell;assert w in '01' and d in 'LR' and 'A'<=n<='O'
                out[f'{q}{s}']=[int(w),d,n]
    assert [k for k,v in out.items() if v is None]==['J1']
    return out

def virtual_program(tm):
    P=Program();cert=[]
    # A finite prologue makes every raw positive A meaningful, even when v_5(A)>0.
    P.sub('init_clear_T',2,'init_clear_T','tm_A0')
    for state,row in tm.items():
        ent='tm_'+state
        if row is None:P.link(ent,'HALT');continue
        w,d,qn=row;X=0 if d=='L' else 1;Y=1-X;T=2
        a=ent+'_';P.link(ent,a+'pop0')
        P.sub(a+'pop0',X,a+'pop1',a+'back0')
        P.sub(a+'pop1',X,a+'pair',a+'back1')
        P.add(a+'pair',T,a+'pop0')
        for r in (0,1):
            b=a+str(r)+'_'
            P.link(a+'back'+str(r),b+'back')
            P.sub(b+'back',T,b+'back_add',b+'push')
            P.add(b+'back_add',X,b+'back')
            P.sub(b+'push',Y,b+'twice1',b+'restore')
            P.add(b+'twice1',T,b+'twice2')
            P.add(b+'twice2',T,b+'push')
            P.sub(b+'restore',T,b+'restore_add',b+'write')
            P.add(b+'restore_add',Y,b+'restore')
            if w:P.add(b+'write',Y,'tm_'+qn+str(r))
            else:P.link(b+'write','tm_'+qn+str(r))
        cert.append({'state':state,'entry':a+'pop0','movement_register':X,
                     'other_register':Y,'write':w,'next_state':qn,
                     'phases_prefix':a})
    rows=P.literal();cuts={s:P.resolve('tm_'+s) for s in tm}
    return rows,cuts,cert


def membrane_rules(program):
    rules=[];seen=set();register_labels=[str(i+1) for i in range(len(program['registers']))]
    def emit(kind,label,a,out=(),other=()):
        z={'kind':kind,'label':label,'consume':a,'produce':list(out)}
        if kind=='divide':z.update({'other':list(other),'elementary':True})
        key=json.dumps(z,sort_keys=True)
        if key not in seen:seen.add(key);rules.append(z)
    def one(x):return [(x,1)]
    for l,row in program['rows'].items():
        op,r,*dest=row;i=str(r+1);u=l+'$1';v=l+'$2'
        if op=='ADD':
            emit('in',i,l,one(l));emit('divide',i,l,one(u),one('t'));emit('out',i,u,one(dest[0]))
        else:
            for h in ('skin','s'):emit('evolve',h,l,[('d',1),('b'+i,1),(u,1)])
            emit('in',i,u,one(u));emit('dissolve',i,u,one(dest[0]));emit('in','s',u,one(v))
            for h in ('s','skin'):emit('out',h,v,one(dest[1]))
    for i in register_labels:
        emit('evolve',i,'t');emit('in',i,'b'+i,one('b'+i));emit('out',i,'b'+i,one('t'))
        for h in ('skin','s',i):emit('evolve',h,'b'+i,one('#'))
        emit('evolve',i,'#',one('#'))
    emit('in','s','d',one('t'))
    for h in ('skin','s'):
        emit('evolve',h,'t');emit('evolve',h,'d',one('#'));emit('evolve',h,'#',one('#'))
    symbols=sorted({z['consume'] for z in rules}|{s for z in rules for k in ('produce','other') for s,n in z.get(k,[])})
    return rules,symbols

def build():
    tm=read_tm();rows,cuts,cert=virtual_program(tm)
    program={'registers':['L','R','T'],'entry':'init_clear_T','halt':'HALT','tm_cuts':cuts,'rows':rows}
    def dump(name,data): (ROOT/name).write_text(json.dumps(data,indent=2)+'\n')
    dump('tm_table.json',tm);dump('virtual3.json',program);dump('macro_certificates.json',{'tm_macros':cert})
    lines=['# Literal ADD/SUB natural-register program; registers L,R,T. HALT has no row.']
    for l,row in rows.items():lines.append(l+': '+' '.join([row[0],program['registers'][row[1]],*row[2:]]))
    (ROOT/'virtual3.txt').write_text('\n'.join(lines)+'\nHALT: HALT\n')
    rules,symbols=membrane_rules(program)
    with (ROOT/'membrane_rules.jsonl').open('w') as f:
        for i,z in enumerate(rules):f.write(json.dumps({'id':i,**z},separators=(',',':'))+'\n')
    (ROOT/'object_alphabet.txt').write_text('\n'.join(symbols)+'\n')
    count=Counter(row[0] for row in rows.values());B=count['ADD']+2*count['SUB']
    meta={'labels':['skin','1','2','3','s'],'entry_object':program['entry'],
        'input':{'L':'natural half-tape integer','R':'natural half-tape integer','scratch_T':0,
                 'counter_membrane_multiplicities':['L+1','R+1',1],'delay_membranes':1,'skin_membranes':1},
        'expanded_initial_membranes':'L+R+5',
        'acceptance':'Existence of a globally halting maximally parallel run, equivalent to U15,2 halting from state A, scanned symbol 0, half tapes L,R.',
        'counts':{'registers':3,'instructions':len(rows),'ADD':count['ADD'],'SUB':count['SUB'],'membrane_rules':len(rules),'object_symbols':len(symbols),'labels':5,'semantic_branches':B},
        'shared_support_rules':28,
        'quadratic_fixed_time':{'time_unit':'literal three-register instruction','natural_witnesses_per_step':4*B-count['SUB'],'affine_squares_per_step':5,'additional_terminal_square':1,'products_per_step':B,'degree_at_most':2},
        'rule_kind_counts':dict(Counter(r['kind'] for r in rules))}
    dump('frontend_metadata.json',meta)
    return meta
if __name__=='__main__':print(json.dumps(build(),indent=2))
