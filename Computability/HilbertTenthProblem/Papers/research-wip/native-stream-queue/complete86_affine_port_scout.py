#!/usr/bin/env python3
"""Finite exact affine/local rewrites of the authenticated complete86 DAG.

CLI research receipt only; not a public compiler or a circuit lower bound.
"""
import argparse
from collections import Counter
from fractions import Fraction
from hashlib import sha256
from itertools import permutations
import json
from pathlib import Path
import random
import tempfile

if not __debug__:
    raise RuntimeError('optimized Python is unsupported')

PINS = {
'complete86_factored_first_root.py': '29cf4100b846bcbabb05185550b7d9ead6b572746048b94998a13c83eeaff40f',
'complete86_factored_first_root.json': '2dfe46fe9c5537ff51eb3c542806c58242238363e6018f9daab7eabf0b6fe61e',
'complete86_factored_first_root.md': '9f2b50449e0724e523e9dd5d022f229b77504976f23ee52ca2917cf11ceb322b',
'complete87_shared_coefficient_scout.md': '0b131c7bf0d474b4a69942dc47113f8bbf9a8ae2f3c8ed7a0540128dc8dca75a',
'complete86_joint_strong_auxiliary_scout.py': '24728e3c3bd4f3b24a929ad816b9a4b4110678923ca50499dcf02c96eb6ac61f',
'complete86_joint_strong_auxiliary_scout.json': 'dc2d26d1f88144bf92fe5e867c78669531a5f117075ab691d98486f60254e810',
'complete86_joint_strong_auxiliary_scout.md': '1501ac846c4d617d37df8db144ae0388b4826c69355c0da3f18f3bafc475f9c6',
'complete87_discriminant_shear_scout.md': '9ef454b65cf75ace91c232d1b0ac643b8c0a00f39c43e16f0ead0666ba414765',
'complete87_joint_norm_scout.md': '681a06e6f280b9b17a723ab9046012f66ffcdeb963930e33d745b47ff044d1bf',
'complete87_new_scout.md': 'f0df0c5b8679f0d3dc40ada56793ea7ff26476bbe1bdb5430d90084b20254f53',
'complete87_strong_norm_composition_scout.md': '34984de9b84c51673be3daf3b56c650ce4ba6ceaadfb15d68c4fe1b5b30255bb',
'complete75_independent_gamma87_period.md': 'dfe1c4a9c438bfe3907b187a3d407280616a5a7eaaf3aa68048de9938b8ac784',
}
FACTORS = ['norm_first','norm_main','norm_input','norm_aux','norm_index','norm_transport','norm_strong','norm_linear']


def require(ok, message):
    if not ok: raise ValueError(message)


def exact(a,b):
    if type(a) is not type(b): return False
    if isinstance(a,dict): return a.keys()==b.keys() and all(exact(a[k],b[k]) for k in a)
    if isinstance(a,list): return len(a)==len(b) and all(exact(x,y) for x,y in zip(a,b))
    return a==b


def digest(value):
    return sha256(json.dumps(value,sort_keys=True,separators=(',',':')).encode()).hexdigest()


def read(root,name):
    p=Path(root)/name
    data=p.read_bytes()
    require(sha256(data).hexdigest()==PINS[name], 'source pin mismatch: '+str(p))
    return data


class Graph:
    def __init__(self):
        self.nodes=[]; self.ids={}
    def intern(self,key):
        if key not in self.ids:
            self.ids[key]=len(self.nodes); self.nodes.append(key)
        return self.ids[key]
    def leaf(self,x):
        require(type(x) in (int,str),'bad leaf')
        return self.intern(('c' if type(x) is int else 'v',x))
    def op(self,op,a,b):
        require(op in ('+','-','*'),'bad operation')
        ca=self.nodes[a];cb=self.nodes[b]
        if ca[0]=='c' and cb[0]=='c':
            return self.leaf(ca[1]+cb[1] if op=='+' else ca[1]-cb[1] if op=='-' else ca[1]*cb[1])
        zero=self.leaf(0);one=self.leaf(1)
        if op=='+':
            if a==zero:return b
            if b==zero:return a
        elif op=='-':
            if b==zero:return a
            if a==b:return zero
        else:
            if a==zero or b==zero:return zero
            if a==one:return b
            if b==one:return a
        if op in ('+','*') and a>b:a,b=b,a
        return self.intern((op,a,b))
    def literal(self,rows):
        env={}
        for name,op,a,b in rows:
            require(name not in env,'duplicate register')
            env[name]=self.op(op,env[a] if type(a) is str and a in env else self.leaf(a),env[b] if type(b) is str and b in env else self.leaf(b))
        return env
    def substitute(self,out,changes):
        memo={}; active=set()
        def go(v):
            if v in memo:return memo[v]
            require(v not in active,'cyclic replacement')
            active.add(v)
            if v in changes:
                r=go(changes[v])
            else:
                n=self.nodes[v]
                r=self.op(n[0],go(n[1]),go(n[2])) if n[0] in ('+','-','*') else v
            active.remove(v);memo[v]=r
            return r
        return go(out)
    def emit(self,out):
        rows=[];memo={};leaves=set()
        def go(v):
            if v in memo:return memo[v]
            n=self.nodes[v]
            if n[0] in ('c','v'):
                if n[0]=='v':leaves.add(n[1])
                return n[1]
            a=go(n[1]);b=go(n[2]);name='g'+str(len(rows));rows.append([name,n[0],a,b]);memo[v]=name
            return name
        output=go(out)
        return {'source':rows,'output':output,'free_ports':sorted(leaves),'M':sum(r[1]=='*' for r in rows),'A':sum(r[1]!='*' for r in rows),'operations':len(rows),'all_gates_live':True}
    def proof(self,left,right,cuts):
        """Exact sparse expansion at computed-port cuts; expand overlap if needed."""
        cuts={v for v in cuts if self.nodes[v][0]!='c'}
        initial_cuts=set(cuts)
        def has_cut_below(v):
            n=self.nodes[v]
            if n[0] not in ('+','-','*'): return False
            return any(u in initial_cuts or has_cut_below(u) for u in n[1:])
        for attempt in range(2):
            memo={}
            def p(v):
                if v in memo:return memo[v]
                n=self.nodes[v]
                if n[0]=='c':r={():n[1]} if n[1] else {}
                elif v in cuts or n[0]=='v':r={(v,):1}
                else:
                    a=p(n[1]);b=p(n[2]);r=dict(a) if n[0]!='*' else {}
                    if n[0]=='*':
                        for x,c in a.items():
                            for y,d in b.items():
                                z=tuple(sorted(x+y));r[z]=r.get(z,0)+c*d
                    else:
                        for z,c in b.items():r[z]=r.get(z,0)+(c if n[0]=='+' else -c)
                    r={z:c for z,c in r.items() if c}
                memo[v]=r;return r
            a=p(left);b=p(right)
            if a==b:return {'cut_count':len(cuts),'terms':len(a)}
            cuts={v for v in initial_cuts if not has_cut_below(v)}
        raise ValueError('local polynomial identity failed')


def moves(g,root):
    """All stated single-site moves of one canonical emitted source."""
    seen=set()
    def walk(v):
        if v in seen:return
        seen.add(v);n=g.nodes[v]
        if n[0] in ('+','-','*'):
            walk(n[1]);walk(n[2])
    walk(root)
    one=g.leaf(1)
    for v in sorted(seen):
        n=g.nodes[v]
        if n[0] not in ('+','-','*'):continue
        op,a,b=n; an=g.nodes[a];bn=g.nodes[b]
        answers=[]
        if op in ('+','-'):
            sign=1 if op=='+' else -1
            if an[0] in ('+','-'):
                answers.append(('add_associate',[(an[1],1),(an[2],1 if an[0]=='+' else -1),(b,sign)]))
            if bn[0] in ('+','-'):
                answers.append(('add_associate',[(a,1),(bn[1],sign),(bn[2],sign*(1 if bn[0]=='+' else -1))]))
            for kind,terms in answers:
                for t in permutations(terms):
                    if t[0][1]!=1:continue
                    (x,_),(y,sy),(z,sz)=t
                    l=g.op('+' if sz==1 else '-',g.op('+' if sy==1 else '-',x,y),z)
                    r=g.op('+' if sy==1 else '-',x,g.op('+' if sz*sy==1 else '-',y,z))
                    for w in (l,r):
                        if w!=v:yield kind,v,w,[x,y,z]
            af=[(an[1],an[2]),(an[2],an[1])] if an[0]=='*' else [(a,one)]
            bf=[(bn[1],bn[2]),(bn[2],bn[1])] if bn[0]=='*' else [(b,one)]
            for common,x in af:
                for common2,y in bf:
                    if common==common2:
                        w=g.op('*',common,g.op(op,x,y))
                        if w!=v:yield 'factor',v,w,[common,x,y]
            if op=='-' and an[0]=='*' and an[1]==an[2] and bn[0]=='*' and bn[1]==bn[2]:
                x=an[1];y=bn[1]
                w=g.op('*',g.op('-',x,y),g.op('+',x,y))
                if w!=v:yield 'difference_of_squares',v,w,[x,y]
        else:
            for inner,other in ((an,b),(bn,a)):
                if inner[0]=='*':
                    x,y=inner[1:]
                    for u,vv,ww in ((x,y,other),(y,x,other),(other,x,y)):
                        w=g.op('*',u,g.op('*',vv,ww))
                        if w!=v:yield 'multiply_associate',v,w,[x,y,other]
                if inner[0] in ('+','-'):
                    x,y=inner[1:]
                    w=g.op(inner[0],g.op('*',x,other),g.op('*',y,other))
                    if w!=v:yield 'distribute',v,w,[x,y,other]
            # Both orientations of the exact conjugate product.
            for plus,minus in ((an,bn),(bn,an)):
                if plus[0]=='+' and minus[0]=='-' and set(plus[1:])==set(minus[1:]):
                    x,y=minus[1:]
                    w=g.op('-',g.op('*',x,x),g.op('*',y,y))
                    if w!=v:yield 'conjugate_product',v,w,[x,y]


def validate_source(packet):
    rows=packet['source'];known=set(packet['free_ports']);defs={}
    for r in rows:
        require(type(r) is list and len(r)==4,'bad literal row')
        name,op,a,b=r
        require(type(name) is str and name not in known and op in ('+','-','*'),'bad gate')
        for x in (a,b):
            require(type(x) is int or type(x) is str and x in known,'source not closed')
        known.add(name);defs[name]=r
    require(packet['output'] in defs,'no final output gate')
    live=set();stack=[packet['output']]
    while stack:
        v=stack.pop()
        if v in live or v not in defs:continue
        live.add(v)
        stack.extend(x for x in defs[v][2:] if type(x) is str)
    require(live==set(defs),'dead gate')
    M=sum(r[1]=='*' for r in rows);A=len(rows)-M
    require((M,A,len(rows))==(packet['M'],packet['A'],packet['operations']),'literal ledger')


def eval_source(packet,assignment):
    env=dict(assignment)
    for name,op,a,b in packet['source']:
        a=env[a] if type(a) is str else a;b=env[b] if type(b) is str else b
        env[name]=a+b if op=='+' else a-b if op=='-' else a*b
    return env[packet['output']]


def seed_graphs(g,env):
    """Six explicitly declared joint root schedules, not all linear circuits."""
    h=env['a4m5'];a=env['D1'];b=env['exponent_partial']
    rho=g.leaf('rho');sigma=g.leaf('sigma')
    u=g.op('*',rho,h);v=g.op('*',sigma,h);w=g.op('*',g.op('+',rho,sigma),h)
    mu=g.op('+',b,u)
    roots=[
        ('original',g.op('+',a,w),mu),
        ('distributed_left',g.op('+',g.op('+',a,u),v),mu),
        ('distributed_right',g.op('+',a,g.op('+',u,v)),mu),
        ('through_input_left',g.op('+',g.op('+',mu,g.op('-',a,b)),v),mu),
        ('through_input_right',g.op('+',mu,g.op('+',g.op('-',a,b),v)),mu),
        ('recover_rho_product',g.op('+',a,w),g.op('+',b,g.op('-',w,v))),
    ]
    for name,main,inp in roots:
        proofs=[g.proof(env['R14'],main,[a,b,h,rho,sigma]),g.proof(env['exponent_rhs'],inp,[a,b,h,rho,sigma])]
        changes={old:new for old,new in ((env['R14'],main),(env['exponent_rhs'],inp)) if old!=new}
        yield name,g.substitute(env['polynomial'],changes),proofs


def verify(root):
    blobs={n:read(root,n) for n in PINS}
    receipt=json.loads(blobs['complete86_factored_first_root.json'])
    require(receipt['source_sha256']==PINS['complete86_factored_first_root.py'],'receipt/source pin')
    form=receipt['forms'][0]
    require(form['normalized'] is True and form['ledger']['operations']==86,'wrong parent selection')
    g=Graph();env=g.literal(form['source']);baseline=g.emit(env['polynomial'])
    require(baseline['operations']==86 and baseline['M']==48 and baseline['A']==38,'baseline fairness')
    require(set(baseline['free_ports'])==set(form['witnesses']+form['ledger']['fixed_numerals']+['x']),'interface closure')
    # Literal semantic cuts are pinned and independently checked here.
    rows={r[0]:r[1:] for r in form['source']}
    for name,row in {
        'gamma_sum':['+','rho','sigma'],'gam':['*','gamma_sum','a4m5'],
        'R14':['+','D1','gam'],'modulus_multiple':['*','rho','a4m5'],
        'exponent_rhs':['+','exponent_partial','modulus_multiple'],
        'q_minus_F':['-','q','F'],'q_minus_FZ':['-','q_minus_F','Z'],
        'gap_product':['*','repunit','q_minus_F'],'gap':['+','gap_product','q_minus_FZ'],
        'repunit':['*','Bm1','Jrep'],'q':['+','repunit',1],
        'polynomial':['-','eight_units',1],
    }.items():require(rows[name]==row,'literal port changed: '+name)
    require([r[0] for r in form['source'] if 'F' in r[2:]]==['q_minus_F'],'F privacy changed')
    seeds=[];records=[];all_packets={};proofs=0;raw_moves=0
    rng=random.Random(8619)
    assignments=[]
    for i in range(12):
        ass={n:rng.randrange(1,8) for n in baseline['free_ports']}
        ass.update(Bm1=15,Kconstant=83,twice_cell_bits=8,inner_bits=3,MC=14,MF=19)
        if i>=4:
            ass.update({n:(-v if (j+i)%3==0 else v) for j,(n,v) in enumerate(ass.items())})
        if i>=8:ass={n:Fraction(v,2+(j%3)) for j,(n,v) in enumerate(ass.items())}
        assignments.append(ass)
    expected=[eval_source(baseline,a) for a in assignments]
    seen_identities=set()
    for name,out,seedproofs in seed_graphs(g,env):
        packet=g.emit(out);require(packet['free_ports']==baseline['free_ports'],'seed interface')
        validate_source(packet)
        seedrec={'name':name,'packet':packet,'root_identities':seedproofs}
        seeds.append(seedrec); proofs+=2
        candidates=[('seed',out,None)]
        move_records=[]
        for kind,old,new,cuts in list(moves(g,out)):
            raw_moves+=1
            key=(old,new,tuple(sorted(set(cuts))))
            if key not in seen_identities:
                g.proof(old,new,cuts);seen_identities.add(key);proofs+=1
            changed=g.substitute(out,{old:new})
            candidates.append((kind,changed,{'changed_gate':old,'replacement_gate':new,'cuts':sorted(set(cuts))}))
        local_seen=set()
        for kind,changed,certificate in candidates:
            p=g.emit(changed);h=digest(p)
            if h in local_seen:continue
            local_seen.add(h)
            require(p['free_ports']==baseline['free_ports'],'candidate interface')
            validate_source(p)
            # emit's DFS constructs a closed source with every gate on an output path.
            for a,y in zip(assignments,expected):require(eval_source(p,a)==y,'complete supplemental identity')
            all_packets.setdefault(h,p)
            move_records.append({'kind':kind,'source_sha256':h,'M':p['M'],'A':p['A'],'operations':p['operations']})
        counts=Counter(r['operations'] for r in move_records)
        records.append({'seed':name,'distinct_complete_sources':len(move_records),'cost_histogram':{str(k):v for k,v in sorted(counts.items())},'census_sha256':digest(move_records),'best':min(r['operations'] for r in move_records)})
    minimum=min(p['operations'] for p in all_packets.values())
    best={h:p for h,p in all_packets.items() if p['operations']==minimum}
    # Explicit gap refactoring is algebraically valid only after expanding q=repunit+1.
    gap_new=g.op('-',g.op('*',env['q'],env['q_minus_F']),g.leaf('Z'))
    gap_proof=g.proof(env['gap'],gap_new,[env['repunit'],env['q_minus_F'],g.leaf('Z')])
    gap_packet=g.emit(g.substitute(env['polynomial'],{env['gap']:gap_new}))
    require(gap_packet['operations']==86,'unexpected gap cost')
    validate_source(gap_packet)
    for a,y in zip(assignments,expected):require(eval_source(gap_packet,a)==y,'gap whole output')
    # The tempting 85-gate coordinate substitution is NOT a positive-domain result.
    u=g.leaf('complement_u')
    complement=g.emit(g.substitute(env['polynomial'],{env['q_minus_F']:u}))
    require(complement['operations']==85 and 'F' not in complement['free_ports'],'complement syntactic count')
    validate_source(complement)
    for i,a in enumerate(assignments):
        aa=dict(a);aa['complement_u']=i+1;aa.pop('F')
        bb=dict(a);bb['F']=a['Bm1']*a['Jrep']+1-aa['complement_u']
        require(eval_source(complement,aa)==eval_source(baseline,bb),'complement graph identity')
    pin_rejections=0
    with tempfile.TemporaryDirectory(prefix='complete86-affine-pin-') as tmp:
        for name,data in blobs.items():
            path=Path(tmp)/name;path.write_bytes(data+b' ')
            try: read(tmp,name)
            except ValueError: pin_rejections+=1
            else: raise ValueError('changed provenance bytes accepted')
    require(pin_rejections==len(PINS),'pin regression count')
    positive_bad=dict(assignments[0]);positive_bad.pop('F')
    positive_bad['complement_u']=positive_bad['Bm1']*positive_bad['Jrep']+2
    positive_bad_output=eval_source(complement,positive_bad)
    require(positive_bad_output!=0,'unexpected complete zero: investigate inverse')
    return {
        'status':'PASS','scope':'finite exact same-polynomial affine/local grammar; no circuit lower bound',
        'source_sha256':sha256(Path(__file__).read_bytes()).hexdigest(),'pins':PINS,
        'parent':{'operations':86,'M':48,'A':38,'positive_witnesses':19,'exact_degree':179,'ordinary_input':'x','fixed_numerals':form['ledger']['fixed_numerals']},
        'seeds':seeds,'census':records,'distinct_complete_sources_across_seeds':len(all_packets),
        'raw_generated_moves':raw_moves,'exact_local_cut_proofs':proofs,'distinct_best_sources':len(best),
        'minimum':minimum,'best_ledger_histogram':dict(sorted(Counter(str(p['M'])+'M+'+str(p['A'])+'A' for p in best.values()).items())),'best_source_hashes':sorted(best),'one_best_complete_source':best[min(best)],
        'strict_pin_rejections':pin_rejections,
        'complete_evaluations':12*sum(r['distinct_complete_sources'] for r in records)+24,
        'assignments_per_source':{'positive_integer':4,'signed_integer':4,'rational':4},
        'gap_refactoring':{'proof':gap_proof,'packet':gap_packet},
        'complement_coordinate_unproved':{'syntactic_packet':complement,'operations':85,'signed_graph_identity':'F=(Bm1*Jrep+1)-complement_u','missing_obligation':'F>0 on every new positive full zero before invoking the parent theorem','not_a_certified_bound':True,'positive_offzero_inverse_example':{'assignment':positive_bad,'restored_F':-1,'complete_output':positive_bad_output}},
        'limitations':['One local move after one of six explicit root schedules; no iterative search.', 'Constants, additions, subtractions and all nontrivial scalar products are paid.', 'No new universal zero was materialized; exact rewrite identities provide the proof.', 'The existing joint strong/auxiliary and independent-gamma families are not repeated.'],
    }


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root',type=Path,default=Path(__file__).resolve().parent)
    parser.add_argument('--output',type=Path)
    parser.add_argument('--expect',type=Path)
    a=parser.parse_args();result=verify(a.root)
    normalized=json.loads(json.dumps(result,sort_keys=True))
    if a.expect:require(exact(normalized,json.loads(a.expect.read_text())),'saved receipt mismatch')
    if a.output:a.output.write_text(json.dumps(normalized,indent=2,sort_keys=True)+'\n')
    print(json.dumps({k:normalized[k] for k in ('status','minimum','distinct_complete_sources_across_seeds','exact_local_cut_proofs','complete_evaluations')},sort_keys=True))

if __name__=='__main__':main()
