#!/usr/bin/env python3
"""Build a literal ADD/SUB-only machine and its finite active-membrane rule set.
No execution predicate, arithmetic oracle, or variable-length macro remains in exports.
Python 3 standard library. Rebuilding is deterministic.
"""
from pathlib import Path
from collections import Counter
import json, hashlib
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

def physical_program(virtual):
    P=Program();cert=[]
    for lab,row in virtual.items():
        op,vreg,*dest=row;p=(2,3,5)[vreg];a='v_'+lab+'_'
        entry='v_'+lab
        if op=='ADD':
            P.link(entry,a+'drain')
            P.sub(a+'drain',0,a+'mul0',a+'restore')
            for j in range(p):P.add(a+'mul'+str(j),1,a+'mul'+str(j+1) if j+1<p else a+'drain')
            P.sub(a+'restore',1,a+'put',('HALT' if dest[0]=='HALT' else 'v_'+dest[0]))
            P.add(a+'put',0,a+'restore')
        else:
            P.link(entry,a+'rem0')
            for r in range(p):
                P.sub(a+'rem'+str(r),0,a+'rem'+str(r+1) if r+1<p else a+'group',
                      a+'quo' if r==0 else a+'recover'+str(r))
            P.add(a+'group',1,a+'rem0')
            P.sub(a+'quo',1,a+'qput',('HALT' if dest[0]=='HALT' else 'v_'+dest[0]))
            P.add(a+'qput',0,a+'quo')
            for r in range(1,p):
                b=a+'r'+str(r)+'_'
                P.link(a+'recover'+str(r),b+'drain')
                P.sub(b+'drain',1,b+'put0',b+'tail0')
                for j in range(p):P.add(b+'put'+str(j),0,b+'put'+str(j+1) if j+1<p else b+'drain')
                for j in range(r):P.add(b+'tail'+str(j),0,b+'tail'+str(j+1) if j+1<r else ('HALT' if dest[1]=='HALT' else 'v_'+dest[1]))
        cert.append({'virtual_label':lab,'op':op,'prime':p,'prefix':a,'entry_alias':entry,'destinations':dest})
    rows=P.literal();cuts={lab:P.resolve('v_'+lab) for lab in virtual}
    return rows,cuts,cert

def membrane_rules(physical):
    """Theorem 4.1, deterministic ADD, no output instructions; conservative role split.
    Every source s-labelled evolution/send-out rule is present at both s and skin.
    Sparse object outputs contain pairs (symbol,multiplicity).
    """
    rules=[];seen=set()
    def emit(kind,label,a,out=(),other=()):
        z={'kind':kind,'label':label,'consume':a,'produce':list(out)}
        if kind=='divide':z.update({'other':list(other),'elementary':True})
        key=json.dumps(z,sort_keys=True)
        if key not in seen:seen.add(key);rules.append(z)
    def one(x):return [(x,1)]
    usedsub=set()
    for l,row in physical.items():
        op,r,*dest=row;i=str(r+1);u=l+'$1';v=l+'$2'
        if op=='ADD':
            emit('in',i,l,one(l));emit('divide',i,l,one(u),one('t'))
            emit('out',i,u,one(dest[0]))
        else:
            usedsub.add(i)
            for h in ('skin','s'):emit('evolve',h,l,[('d',1),('b'+i,1),(u,1)])
            emit('in',i,u,one(u));emit('dissolve',i,u,one(dest[0]))
            emit('in','s',u,one(v))
            for h in ('s','skin'):emit('out',h,v,one(dest[1]))
    for i in ('1','2'):emit('evolve',i,'t')
    for i in sorted(usedsub):
        emit('in',i,'b'+i,one('b'+i));emit('out',i,'b'+i,one('t'))
        for h in ('skin','s',i):emit('evolve',h,'b'+i,one('#'))
        emit('evolve',i,'#',one('#'))
    emit('in','s','d',one('t'))
    for h in ('skin','s'):
        emit('evolve',h,'t');emit('evolve',h,'d',one('#'));emit('evolve',h,'#',one('#'))
    symbols=sorted({z['consume'] for z in rules}|{s for z in rules for k in ('produce','other') for s,n in z.get(k,[])})
    return rules,symbols

def write_json(path,obj):path.write_text(json.dumps(obj,indent=2)+'\n')
def text_table(rows,registers):
    lines=['# Literal instruction table; natural registers '+','.join(registers),
           '# ADD r q increments r then goes to q. SUB r q z decrements/goes to q if positive, else goes to z.',
           '# HALT has no instruction. No aliases or macros in this table.']
    lines += [f'{l}: '+ ' '.join([r[0],registers[r[1]],*r[2:]]) for l,r in rows.items()]
    lines.append('HALT: HALT');return '\n'.join(lines)+'\n'

def build():
    tm=read_tm();v,tc,vc=virtual_program(tm);p,pc,pcert=physical_program(v);mr,sy=membrane_rules(p)
    write_json(ROOT/'tm_table.json',tm)
    write_json(ROOT/'virtual3.json',{'registers':['L','R','T'],'entry':'init_clear_T','halt':'HALT','tm_cuts':tc,'rows':v})
    write_json(ROOT/'literal2.json',{'registers':['A','B'],'entry':pc['init_clear_T'],'halt':'HALT','virtual_cuts':pc,'rows':p})
    (ROOT/'virtual3.txt').write_text(text_table(v,['L','R','T']))
    (ROOT/'literal2.txt').write_text(text_table(p,['A','B']))
    write_json(ROOT/'macro_certificates.json',{'tm_macros':vc,'prime_macros':pcert})
    with (ROOT/'membrane_rules.jsonl').open('w') as f:
        for i,z in enumerate(mr):f.write(json.dumps({'id':i,**z},separators=(',',':'))+'\n')
    (ROOT/'object_alphabet.txt').write_text('\n'.join(sy)+'\n')
    meta={'labels':['skin','1','2','s'],'entry_object':pc['init_clear_T'],
          'acceptance':'Global quiescence (no applicable rule), existential over maximally parallel runs; HALT occurrence alone is not acceptance.',
          'raw_input':{'domain':'A is a positive natural, B=0','skin_objects':[[pc['init_clear_T'],1]],
                       'elementary_children':[{'label':'1','multiplicity':'A+1','objects':[]},
                                              {'label':'2','multiplicity':1,'objects':[]},
                                              {'label':'s','multiplicity':1,'objects':[]}]},
          'initial_expanded_membranes':'A+4 including skin','counts':{'tm_defined_rows':len(tm)-1,'virtual_instructions':len(v),'physical_instructions':len(p),'membrane_rules':len(mr),'object_symbols':len(sy),'membrane_labels':4},
          'physical_instruction_counts':dict(Counter(r[0] for r in p.values())),
          'membrane_rule_counts':dict(Counter(r['kind'] for r in mr))}
    write_json(ROOT/'frontend_metadata.json',meta)
    return meta
if __name__=='__main__':print(json.dumps(build(),indent=2))
