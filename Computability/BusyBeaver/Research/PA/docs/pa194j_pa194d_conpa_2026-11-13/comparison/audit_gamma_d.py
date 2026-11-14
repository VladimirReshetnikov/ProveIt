#!/usr/bin/env python3
"""Portable independent graph and AX-word audit for the Gamma(D) candidates.

No allocator, source compiler, physical runtime, or logical audit is imported.
The macro interpreter acts in a free algebra; its source binding is to the
literal supplied and new grammar files. This is not a PA-calibration proof.
"""
import argparse,hashlib,itertools,json
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent

TOKENS={'node49':['push'],'node55':['D'],'node58':['H'],'node70':['A'],
        'node65':['cons'],'node72':['readH'],'node75':['readDCons'],
        'node142':['copyGuard'],'node150':['compareGuard'],
        'node60':['inc']*2,'node61':['inc']*4}

def sha(b):return hashlib.sha256(b).hexdigest()
def parse(b):
    rows={}
    for line in b.decode().splitlines():
        if not line.strip() or line.lstrip().startswith(('#','//',';')):continue
        q,r,w,d,n=line.split();key=int(q),int(r)
        assert key not in rows and r in ('0','1') and w in ('0','1') and d in ('L','R')
        rows[key]=int(w),d,int(n)
    states={q for q,b in rows};assert len(rows)==2*len(states)
    assert set(rows)=={(q,b)for q in states for b in (0,1)}
    halts={n for w,d,n in rows.values()}-states;assert len(halts)==1
    return rows,states,next(iter(halts))
def canon(table,root,mirror=False,flip=False):
    rows,states,halt=table;ids={root:0};queue=[root];result=[]
    for q in queue:
        entries=[]
        for bit in (0,1):
            w,d,n=rows[q,bit ^ int(flip)]
            if flip:w^=1
            if mirror:d='L'if d=='R'else'R'
            if n==halt:target=-1
            else:
                if n not in ids:ids[n]=len(queue);queue.append(n)
                target=ids[n]
            entries.append([w,d,target])
        result.append(entries)
    if len(queue)!=len(states):return None
    return json.dumps(result,separators=(',',':')).encode()
def graphs(table):
    out={}
    for m,f in itertools.product((False,True),repeat=2):
        vals=[v for q in table[1]if(v:=canon(table,q,m,f))is not None]
        assert vals
        out[f'{int(m)}{int(f)}']=sha(min(vals))
    return out

def word(path):
    data=json.loads(path.read_text());rules=data['rules'];active=set()
    def flatten(x):
        if isinstance(x,str):
            if x in TOKENS:return list(TOKENS[x])
            assert x not in active,'cyclic grammar'
            active.add(x);out=flatten(rules[x]);active.remove(x);return out
        if x==['leaf','inc',1]:return ['inc']
        if x==['leaf','breakTo',1]:return ['close']
        if x==['leaf','dec',4]:return ['closeDecD']
        assert len(x)==2,x
        return flatten(x[0])+flatten(x[1])
    return flatten(data['root'])

# Terms use0, ('succ',term), ('I',left,right), ('add',left,right), and atoms.
def succ(t):return ('succ',t)
def imp(a,b):return ('I',a,b)
def all_(a,b):return succ(succ(imp(b,a)))
def gamma(a):return imp(a,all_(a,a))

def interpret(tokens):
    stack=[];top='oldT';A='a';D='d';H='h';fields=iter(('y','x'));reads=[]
    assert tokens[-3:-1]==['copyGuard','compareGuard']
    assert tokens[-1]in('close','closeDecD')
    for op in tokens[:-3]:
        if op=='push':stack.append(top);top=0
        elif op in ('A','D','H'):
            stack.append(top);top={'A':A,'D':D,'H':H}[op]
        elif op=='cons':assert stack;top=imp(stack.pop(),top)
        elif op=='inc':top=succ(top)
        elif op=='readH':
            field=next(fields);reads.append(field);H=('add',H,field)
        elif op=='readDCons':
            field=next(fields);reads.append(field);D=('add',D,field);top=imp(top,D)
        else:raise ValueError(op)
    assert reads==['y','x'] and len(stack)==10
    return stack,top,{'A':A,'D':D,'H':H},reads

def abstract_parameters(t,env):
    for k,v in env.items():
        if t==v:return k
    return tuple(abstract_parameters(x,env)for x in t)if isinstance(t,tuple)else t

def rename(t,permutation):
    if isinstance(t,str):return permutation.get(t,t)
    return tuple(rename(x,permutation)for x in t)if isinstance(t,tuple)else t

def value(t,env):
    if isinstance(t,int):return t
    if isinstance(t,str):return env[t]
    if t[0]=='succ':return value(t[1],env)+1
    if t[0]=='add':return value(t[1],env)+value(t[2],env)
    assert t[0]=='I';a=value(t[1],env);b=value(t[2],env)
    return 4*((a+b)*(a+b+1)//2+b)

def candidate_files(dense):
    """Accept either delivered machine stems or raw candidate.tm filenames."""
    stem = dense.name[:-3]
    native = dense.with_name(stem + '.native.tm')
    def metadata(suffix):
        for path in (dense.with_name(stem + '.' + suffix), dense.with_name(suffix)):
            if path.is_file():
                return path
        raise FileNotFoundError('Missing ' + suffix + ' beside ' + str(dense))
    return native, dense, metadata('instructions.json'), metadata('sites.json')

def main():
    assert __debug__, 'Run Python without -O.'
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--old-grammar',type=Path,default=ROOT/'construction/inputs/pa194.grammar.json')
    ap.add_argument('--new-grammar',type=Path,default=ROOT/'logical_emitter/inputs/winner.grammar.json')
    ap.add_argument('--cz',type=Path,default=ROOT/'logical_emitter/machine/pa194d.tm',help='Dense CZ table; native table and source metadata must be alongside it.')
    ap.add_argument('--csz-a',type=Path,default=ROOT/'research/gamma_d_csza/candidate.tm',help='Dense CSZ_A sibling table; native table and source metadata must be alongside it.')
    ap.add_argument('--old-frontier',type=Path,default=HERE/'frontier194.json')
    ap.add_argument('--j-receipt',type=Path,default=HERE/'new_variants_novelty.json')
    ap.add_argument('--output',type=Path,help='Optional JSON output; by default print the receipt without modifying the packet.')
    a=ap.parse_args()
    oldword=word(a.old_grammar);newword=word(a.new_grammar)
    assert len(oldword)==len(newword)==190
    diffs=[{'token_index':i,'parent':u,'new':v}for i,(u,v)in enumerate(zip(oldword,newword))if u!=v]
    changed_copy=[r for r in diffs if r['token_index']!=189]
    assert len(changed_copy)==3 and all(r['parent']=='A'and r['new']=='D'for r in changed_copy)
    assert diffs[-1]=={'token_index':189,'parent':'close','new':'closeDecD'}
    oldstack,oldgate,env,reads=interpret(oldword);newstack,newgate,env2,reads2=interpret(newword)
    assert env==env2 and reads==reads2 and oldgate==newgate
    assert oldstack[:-1]==newstack[:-1]
    assert oldstack[-1]==gamma(env['A']) and newstack[-1]==gamma(env['D'])
    assert oldstack[-1]!=newstack[-1]
    oldbody=abstract_parameters(tuple(oldstack[3:]+[oldgate]),env)
    newbody=abstract_parameters(tuple(newstack[3:]+[newgate]),env)
    matches=[]
    for p in itertools.permutations(('A','D','H')):
        ren=dict(zip(('A','D','H'),p))
        if rename(oldbody,ren)==newbody:matches.append(ren)
    assert not matches
    witness={'a':0,'d':1,'h':0,'x':0,'y':0,'oldT':0}
    oldv=value(oldstack[-1],witness);newv=value(newstack[-1],witness)
    assert oldv==20 and newv==832
    frontier=json.loads(a.old_frontier.read_text());j=json.loads(a.j_receipt.read_text())
    old_signatures={r['name']:r['cosmetic_class_sha256']for r in frontier['classes']}
    j_signatures={r['name']:r['cosmetic_class_sha256']for r in j['variants']}
    assert len(set(old_signatures.values()))==8 and len(set(j_signatures.values()))==4
    candidates=[]
    for mode,dense in (('CZ',a.cz),('CSZ_A',a.csz_a)):
        native,dense,instructions,site_path=candidate_files(dense)
        t=parse(native.read_bytes());dt=parse(dense.read_bytes());assert len(t[1])==194
        assert canon(t,74)==canon(dt,0)
        hs=graphs(t);sig=min(hs.values())
        oldmatches=[k for k,v in old_signatures.items()if v==sig];jmatches=[k for k,v in j_signatures.items()if v==sig]
        assert not oldmatches and not jmatches
        ins=json.loads(instructions.read_text());sites=json.loads(site_path.read_text())
        assert len(ins)==len(sites)
        candidates.append({'mode':mode,'states':194,'source_sites':len(ins),'source_outcomes':sum(2 if r[0]=='dec'else 1 for r in ins),'native_sha256':sha(native.read_bytes()),'dense_sha256':sha(dense.read_bytes()),'instructions_sha256':sha(instructions.read_bytes()),'root_free_transformation_hashes':hs,'cosmetic_class_sha256':sig,'old_eight_class_matches':oldmatches,'new_J_family_matches':jmatches})
    assert len({r['cosmetic_class_sha256']for r in candidates})==2
    out={'scope':'Independent literal table graph comparison plus free-term AX macro-word evaluation from grammar files. No construction/compiler/runtime module imported. The graph comparison is stronger than rooted renaming; physical source/table binding and PA calibration require separate certificates.','candidates':candidates,'both_novel_against_old_eight_and_new_four_J_variants':True,'candidates_mutually_distinct':True,'emitter':{'tokens':190,'token_differences':diffs,'complete_pushed_items':10,'all_other_nine_pushed_items_equal':True,'final_gate_equal':True,'guard_and_parameter_reads_equal':True,'old_last_head':oldstack[-1],'new_last_head':newstack[-1],'last_head_change':'Gamma(A) -> Gamma(D)','matches_under_any_global_ADH_parameter_permutation':matches,'concrete_witness':{'inputs':witness,'old_head_code':oldv,'new_head_code':newv},'old_grammar_sha256':sha(a.old_grammar.read_bytes()),'new_grammar_sha256':sha(a.new_grammar.read_bytes())},'inputs':{'old_frontier_sha256':sha(a.old_frontier.read_bytes()),'J_receipt_sha256':sha(a.j_receipt.read_bytes())}}
    if a.output:
        a.output.write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps(out,indent=2))

if __name__=='__main__':main()
