#!/usr/bin/env python3
"""Rebuild the new zero-branch machines from the frozen source and physical compiler.

Python 3.10+, standard library, assertions enabled. No network is used.
The construction checker uses the inherited, unchanged arithmetic-block lemmas;
verification/check_literal.py separately rederives list lemmas from literal rows.
"""
from pathlib import Path
import argparse, hashlib, json, time
import compiler as c

HERE=Path(__file__).resolve().parent
PACKAGE=HERE.parent
START,HALT=74,254
ORIGINAL_MACHINE,ORIGINAL_NODES=c.machine,c.raw_nodes
COMBINED={(38,0):(0,True,11),(38,1):(1,True,122),(164,1):(1,True,130),
          (214,0):(0,True,312),(214,1):(1,True,20),(312,0):(0,True,188)}
SYMMETRIC={(214,1):(1,True,30),(310,1):(1,True,330),
           (330,0):(0,True,63),(330,1):(1,False,73)}
FAMILIES={'PA194F':(3553,6,2066,21),'PA194A':(26,3,27,17),'PA194X':(26,6,27,21)}
sha=lambda b:hashlib.sha256(b).hexdigest()

def dump(path,obj):path.write_text(json.dumps(obj,indent=2)+'\n')
def table_text(rows):
    return ''.join(f'{q} {b} {w} {"R" if d else "L"} {t}\n' for (q,b),(w,d,t) in sorted(rows.items()))
def read_table(path):
    rows={}
    for line in path.read_text().splitlines():
        q,b,w,d,t=line.split();key=int(q),int(b)
        assert key not in rows and d in ('L','R')
        rows[key]=int(w),d=='R',int(t)
    return rows

def nodes(reg=None):
    ns=ORIGINAL_NODES()
    ns['node163']=('node6','node147')
    ns['node170']=(('node36',('node167','node145')),'node56')
    ns['node171']=('node170',(('leaf','inc',5),('leaf','continueTo',3)))
    if reg is not None:ns['node22']=(('leaf','dec',8),('leaf','dec',reg))
    return ns

def final_zero(t):
    if t==('leaf','breakTo',1):return ('leaf','dec',6)
    return tuple(final_zero(x) for x in t) if c.isnode(t) else t

def grammar_json(t):
    rules={};names={}
    def rec(x):
        if not c.isnode(x):return list(x) if isinstance(x,tuple) else x
        if x in names:return names[x]
        name='g'+str(len(names));names[x]=name
        rules[name]=[rec(x[0]),rec(x[1])]
        return name
    root=rec(t)
    return {'root':root,'rules':rules}

def fold(rows,folds):
    alias={a:b for a,b,actions in folds};acts={b:actions for a,b,actions in folds}
    assert len({q for a,b,_ in folds for q in (a,b)})==2*len(folds)
    result={}
    for (q,bit),action in rows.items():
        if q in alias:continue
        w,d,t=acts[q][bit] if q in acts else action
        result[q,bit]=w,bool(d),alias.get(t,t)
    return result,alias

def check_folds(raw,child,alias,folds):
    incoming={}
    for (q,bit),(w,d,t) in raw.items():incoming.setdefault(t,[]).append((q,bit,w,d))
    cases=[]
    for a,b,_ in folds:
        assert START not in (a,b)
        assert {(w,d) for _,_,w,d in incoming[a]}=={(0,True)}
        assert {(w,d) for _,_,w,d in incoming[b]}=={(1,True)}
        for old,h in ((a,0),(b,1)):
            for bit in (0,1):
                w,d,t=raw[old,bit]
                target=(alias.get(t,t),1 if d else -1,{-1:h,0:w})
                q=b;pos=0;tape={-1:h,0:bit};trace=[]
                for ticks in range(1,31):
                    assert pos in (-1,0)
                    wr,dr,q2=child[q,tape[pos]]
                    trace.append([q,pos,tape[pos],wr,int(dr),q2])
                    tape[pos]=wr;pos+=1 if dr else -1;q=q2
                    if (q,pos,tape)==target:break
                else:raise AssertionError(('fold failed',old,bit))
                cases.append({'old':old,'history':h,'read':bit,'duration':ticks,'trace':trace})
    return {'cases':cases,'case_count':len(cases),'max_duration':max(x['duration'] for x in cases)}

def dense(rows):
    states={q for q,b in rows};assert len(states)==194
    assert set(rows)=={(q,b) for q in states for b in (0,1)}
    assert {t for w,d,t in rows.values()}-states=={HALT}
    order=[START];index={START:0}
    for q in order:
        for b in (0,1):
            t=rows[q,b][2]
            if t!=HALT and t not in index:index[t]=len(order);order.append(t)
    assert set(order)==states
    result={(index[q],b):(w,d,194 if t==HALT else index[t]) for (q,b),(w,d,t) in rows.items()}
    return result,order+[HALT]

def startup(rows,path):
    head=-2;expected={head-1,head+48}
    expected.update(head+i for i,b in enumerate(path) if b)
    values=[0,0,0,0,0,0,2,0,0]+[1]*26;pos=head+49
    for v in values:
        pos+=1;expected.update(range(pos,pos+v+1));pos+=v+1
    q=START;h=0;ones=set()
    for ticks in range(1,1000001):
        w,d,q=rows[q,int(h in ones)]
        (ones.add if w else ones.discard)(h);h+=1 if d else -1
        assert q!=HALT,('early blank halt',ticks)
        if (q,h,ones)==(84,head,expected):
            return {'steps':ticks,'state':q,'head':h,'source_site':25,
                    'logical_registers':[2]+[0]*8,'spare_values':[1]*26,
                    'one_cells':sorted(ones),'complete_tape_equality':True}
    raise AssertionError('Whole clean source frame was not reached')

def build(family,out,full=True):
    started=time.monotonic();site,reg,row,target=FAMILIES[family]
    c.raw_nodes=lambda:nodes()
    inc=('leaf','inc',1);c.MACROS[(inc,inc)]=99;c.MACROS[((inc,inc),(inc,inc))]=190
    c.MACROS[('leaf','dec',6)]=21
    def fixed():
        rows,labels=ORIGINAL_MACHINE();rows.update(COMBINED);rows.update(SYMMETRIC)
        return rows,labels
    c.machine=fixed
    tree=c.read_grammar(PACKAGE/'inputs/pa194.grammar.json')
    oldsites,oldins,oldcontracts=c.source(tree)
    parent,idx,shape=c.build(tree)
    folds=json.loads((PACKAGE/'inputs/pa194.folds.json').read_text())+[[41,330,[[0,False,31],[1,False,46]]]]
    old,aliases=fold(parent,folds)
    assert old==read_table(PACKAGE/'inputs/pa194CS.native.tm')
    assert json.loads(json.dumps(oldins))==json.loads((PACKAGE/'inputs/pa194CS.instructions.json').read_text())
    assert [[''.join(map(str,p)),op,a] for p,op,a in oldsites]==json.loads((PACKAGE/'inputs/pa194CS.sites.json').read_text())
    if family=='PA194F':tree=final_zero(tree)
    else:
        c.raw_nodes=lambda:nodes(reg)
        def fixed_new():
            rows,labels=fixed();rows[27,1]=(1,True,target);return rows,labels
        c.machine=fixed_new
    sites,instructions,contracts=c.source(tree)
    raw,index,shape=c.build(tree)
    assert len(shape)==67 and len(raw)==404
    child,aliases=fold(raw,folds)
    assert [(key,old[key],child[key]) for key in old if old[key]!=child[key]]==[((row,1),(0,False,302 if family=='PA194F' else 40),(1,True,target))]
    changes=[(i,a,b) for i,(a,b) in enumerate(zip(oldins,instructions)) if a!=b]
    assert len(changes)==1 and changes[0][0]==site
    assert len(sites)==3646 and len(contracts)==4746
    original,_=ORIGINAL_MACHINE()
    assert all(child[q,b]==original[q,b] for q in c.BOXSTATES for b in (0,1))
    local=check_folds(raw,child,aliases,folds)
    valid=c.validate(child,contracts) if full else {'performed':False}
    if full:assert valid['ok'],valid
    seed=startup(child,sites[25][0]);dtable,labels=dense(child)
    out.mkdir(parents=True,exist_ok=True)
    for name,rows in [('machine.native.tm',child),('machine.tm',dtable),('unfolded202.native.tm',raw)]:
        (out/name).write_text(table_text(rows))
    dump(out/'labels.json',labels);dump(out/'grammar.json',grammar_json(tree))
    dump(out/'sites.json',[[''.join(map(str,p)),op,a] for p,op,a in sites])
    dump(out/'instructions.json',instructions);dump(out/'folds.json',folds);dump(out/'local_folds.json',local)
    dump(out/'blank_seed.json',seed)
    receipt={'family':family,'status':'PASS','working_states':194,'transition_rows':388,
             'raw_controls':202,'fixed_controls_before_quotient':135,'axiom_readers':67,
             'simultaneous_folds':8,'local_cases':local['case_count'],'source_sites':len(sites),
             'source_outcomes':len(contracts),'source_changes':changes,
             'universal_contracts':valid,'startup':seed,
             'native_sha256':sha(table_text(child).encode()),'dense_sha256':sha(table_text(dtable).encode()),
             'source_object_sha256':sha(json.dumps(instructions,separators=(',',':')).encode()),
             'arithmetic_box_rows_unchanged':True,'kernel_checked':False,
             'elapsed_seconds':round(time.monotonic()-started,3)}
    dump(out/'construction_receipt.json',receipt)
    print(json.dumps({k:v for k,v in receipt.items() if k!='startup'},indent=2),flush=True)
    return receipt

if __name__=='__main__':
    if not __debug__:raise SystemExit('Run without Python -O or PYTHONOPTIMIZE.')
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--family',choices=list(FAMILIES)+['all'],default='PA194F')
    ap.add_argument('--output',type=Path,default=PACKAGE/'machines')
    a=ap.parse_args()
    for family in FAMILIES:
        if a.family in (family,'all'):build(family,a.output/family)
