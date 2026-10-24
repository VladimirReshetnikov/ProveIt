#!/usr/bin/env python3
"""Independent semantic-interface and positivity audit of the final direct builder.

Checks literal rows and arithmetic nodes for all power, binomial, factorial,
shared-Pell, global-bound, and common-radix interfaces. The mathematical
theorems connecting those interfaces are reviewed in FINAL_SEMANTIC_REVIEW.md.
"""
import argparse
from collections import defaultdict
from hashlib import sha256
import json
import importlib.util
from pathlib import Path
import sys


def require(ok,message):
    if not ok: raise ValueError(message)


class Audit:
    def __init__(self,b):
        self.b=b; self.c=0; self.lower_known={}; self.positive=[]
        self.names={v['name']:('v',i) for i,v in enumerate(b.variables)}
        require(len(self.names)==len(b.variables),'duplicate raw variable name')
        self.arith={value:key for key,value in b.cache.items()}
        self.labels=defaultdict(list)
        for row in b.rows: self.labels[row['label']].append(row['terms'])

    def leaf(self,name):
        require(name in self.names,'missing variable '+name); return self.names[name]

    def add(self,a,b):
        if a==('c',0): return b
        if b==('c',0): return a
        if a[0]==b[0]=='c': return ('c',a[1]+b[1])
        a,b=sorted((a,b)); key=('add',a,b)
        require(key in self.b.cache,'missing literal addition'); return self.b.cache[key]

    def mul(self,a,b):
        if ('c',0) in (a,b): return ('c',0)
        if a==('c',1): return b
        if b==('c',1): return a
        if a[0]==b[0]=='c': return ('c',a[1]*b[1])
        a,b=sorted((a,b)); key=('mul',a,b)
        require(key in self.b.cache,'missing literal product'); return self.b.cache[key]

    def sum(self,atoms):
        out=('c',0)
        for atom in atoms: out=self.add(out,atom)
        return out

    @staticmethod
    def normalize(terms):
        result=defaultdict(int)
        for coefficient,atoms in terms:
            mon=[]
            for kind,value in atoms:
                if kind=='c': coefficient*=value
                else: mon.append(value)
            result[tuple(sorted(mon))]+=coefficient
        return [[c,list(m)] for m,c in sorted(result.items()) if c]

    def row(self,label,terms):
        expected=self.normalize(terms)
        require(self.labels[label]==[expected],'literal interface row mismatch: '+label)
        self.c+=1

    def eq(self,label,left,right): self.row(label,[(1,[left]),(-1,[right])])

    def norm(self,label,a,x,y):
        ay=self.mul(a,y)
        self.row(label,[(1,[x,x]),(1,[y,y]),(-1,[ay,ay]),(-1,[])])

    def lower(self,atom,memo=None):
        if atom[0]=='c': return min(2,atom[1])
        if atom in self.lower_known: return self.lower_known[atom]
        if memo is None: memo={}
        if atom in memo:return memo[atom]
        if atom not in self.arith:return 0
        op,a,b=self.arith[atom]; x,y=self.lower(a,memo),self.lower(b,memo)
        out=min(2,x+y if op=='add' else x*y);memo[atom]=out;return out

    def check_macros(self):
        b=self.b; one=('c',1); two=('c',2)
        L=b.shared_digit_limit; q=b.shared_digit_base
        self.eq_atom_L=self.add(self.leaf('digit.limit_minus1'),one)
        require(L==self.eq_atom_L,'common positive limit binding')
        require((two,L) in b.powers,'missing common binary radix power')
        require(q==self.add(b.powers[(two,L)],one),'common q=2^L+1 binding')
        qplus=self.add(q,one)
        common=b.shared_pell
        index_users=defaultdict(int)
        for macro in b.macro_log:
            kind=macro['macro']; output=macro['output']
            tag=b.variables[output[1]]['name'].removesuffix('.output')
            if kind=='power':
                n,k=macro['base'],macro['exponent']
                nlower,klower=self.lower(n),self.lower(k)
                require(nlower>=1 and klower>=1,'unproved positive power inputs at '+tag)
                require(b.powers[(n,k)]==output,'power-cache interface')
                require(k in b.pell_indices,'missing index certificate')
                X,Y=b.pell_indices[k]; A=common['A']
                T=self.sum([output,self.leaf(tag+'.gap'),one])
                left=self.add(X,self.mul(Y,n))
                right=self.sum([self.mul(Y,A),output,self.mul(T,self.leaf(tag+'.quotient'))])
                self.eq(tag+'.power_congruence',left,right)
                self.row(tag+'.T_definition',[(2,[A,n]),(-1,[T]),(-1,[n,n]),(-1,[])])
                self.positive.append({'tag':tag,'base':list(n),'exponent':list(k),
                                      'base_lower':nlower,'exponent_lower':klower})
                self.lower_known[output]=1;index_users[k]+=1
            elif kind=='binomial':
                n,k=macro['n'],macro['k']
                require(self.lower(n)>=1 and self.lower(k)>=1,'binomial arguments lack positivity')
                require(self.lower(q)>=1,'common radix lacks positivity')
                require(n in b.binomial_upper_arguments,'binomial omitted from global radix bound')
                numerator=b.powers[(qplus,n)]; denominator=b.powers[(q,k)]
                h,r,rs,os=[self.leaf(tag+'.'+s) for s in ('high','remainder','rslack','oslack')]
                rhs=self.add(self.mul(denominator,self.add(self.mul(q,h),output)),r)
                self.eq(tag+'.digit_division',numerator,rhs)
                self.eq(tag+'.remainder_bound',denominator,self.sum([r,rs,one]))
                self.eq(tag+'.digit_bound',q,self.sum([output,os,one]))
                # A binomial can vanish. No positive output lower bound is assumed.
            elif kind=='factorial':
                n=macro['n'];require(self.lower(n)>=1,'factorial input lacks positivity')
                require(self.lower(output)==0,'self-bounding factorial output was assumed positive too early')
                radius=self.mul(output,self.mul(n,n))
                c=b.binomials[(self.add(radius,n),n)]
                numerator=b.powers[(self.add(radius,one),n)]
                r,s=self.leaf(tag+'.remainder'),self.leaf(tag+'.slack')
                self.eq(tag+'.ceiling',self.add(numerator,c),self.sum([self.mul(c,output),r,one]))
                self.eq(tag+'.remainder_bound',c,self.sum([r,s,one]))
                # The reviewed self-bounding factorial lemma now gives output=n!>=1.
                self.lower_known[output]=1
            else: raise ValueError('unknown semantic macro '+kind)
        require(len(self.positive)==len(b.powers)==25,'final power graph count')
        require(len(index_users)==len(b.pell_indices)==20,'final index sharing count')
        return {'power_calls':self.positive,'factorial_outputs_not_assumed_positive':2,
                'binomial_graphs':len(b.binomials),'distinct_indices':len(index_users)}

    def check_shared_environment(self):
        b=self.b;c=b.shared_pell;one=('c',1);four=('c',4)
        W,A,Z,U,V,B,qB=[c[s] for s in ('W','A','Z','U','V','B','qB')]
        args=[(m['base'],m['exponent']) for m in b.macro_log if m['macro']=='power']
        require(args==b.power_arguments and len(args)==len(set(args))==25,'global bound call inventory')
        raw=[(1,[W])]
        for n,k in args:raw.extend([(-1,[n]),(-1,[k])])
        self.row('shared_pell.global_bound',raw)
        self.norm('shared_pell.auxiliary_norm',A,U,V)
        self.norm('shared_pell.growth_norm',self.add(W,one),A,self.mul(W,Z))
        self.eq('shared_pell.B_mod_U',B,self.add(A,self.mul(U,qB)))
        binomial_upper=[m['n'] for m in b.macro_log if m['macro']=='binomial']
        require(binomial_upper==b.binomial_upper_arguments and len(binomial_upper)==14,
                'global radix bound binomial inventory')
        self.row('shared_digits.global_limit',[(1,[b.shared_digit_limit])] +
                 [(-1,[n]) for n in binomial_upper])
        records=[]
        for ordinal,(k,(X,Y)) in enumerate(b.pell_indices.items()):
            tag='index'+str(ordinal)
            require(X==self.leaf(tag+'.X'),'index X binding')
            require(Y==self.add(k,self.leaf(tag+'.yk')),'index Y=k+yk binding')
            S,R=self.leaf(tag+'.S'),self.leaf(tag+'.R')
            fourY=self.mul(four,Y)
            self.norm(tag+'.normA',A,X,Y);self.norm(tag+'.normB',B,S,R)
            self.eq(tag+'.B_mod_4Y',B,self.add(one,self.mul(fourY,self.add(self.leaf(tag+'.q4minus1'),one))))
            self.eq(tag+'.V_multiple',V,self.mul(self.mul(Y,Y),self.add(self.leaf(tag+'.Vquotient_minus1'),one)))
            self.eq(tag+'.S_mod_U',S,self.add(X,self.mul(U,self.leaf(tag+'.Squotient'))))
            self.eq(tag+'.R_mod_4Y',R,self.add(k,self.mul(fourY,self.leaf(tag+'.Rquotient'))))
            records.append({'tag':tag,'exponent':list(k),'X':list(X),'Y':list(Y)})
        return {'global_bound_powers':len(args),'global_bound_terms_before_collection':51,
                'global_radix_limit_upper_arguments':14,
                'shared_index_certificates':records}

    def semantic_dependencies(self):
        b=self.b;semantic={}
        for m in b.macro_log:
            args=(m['base'],m['exponent']) if m['macro']=='power' else (m['n'],m['k']) if m['macro']=='binomial' else (m['n'],)
            semantic[m['output']]=args
        memo={};active=set()
        def roots(atom):
            if atom[0]=='c':return frozenset()
            if atom in memo:return memo[atom]
            require(atom not in active,'cyclic semantic macro arguments')
            active.add(atom)
            args=semantic.get(atom)
            if args is None and atom in self.arith:args=self.arith[atom][1:]
            out=frozenset([atom]) if args is None else frozenset().union(*(roots(a) for a in args))
            active.remove(atom);memo[atom]=out;return out
        limit=self.leaf('digit.limit_minus1')
        allowed={'t0','x','y','m0','M0','digit.limit_minus1','crt.extra_bound'} | {
            'crt.encoded.'+s for s in ('p','q','v','a','b','c','d','S','Sp','u','vq')}
        records=[]
        for m in b.macro_log:
            if m['macro'] not in ('power','binomial','factorial'):continue
            dependencies=frozenset().union(*(roots(a) for a in semantic[m['output']]))
            names=sorted(b.variables[a[1]]['name'] for a in dependencies)
            require(set(names)<=allowed,'private arithmetic/Pell witness in semantic arguments')
            if m['macro']=='binomial':require(limit not in dependencies,'binomial inputs depend on shared digit limit')
            records.append({'macro':m['macro'],'output':b.variables[m['output'][1]]['name'],
                            'roots':names,'limit_independent':limit not in dependencies})
        return {'acyclic_after_semantic_erasure':True,
                'all_binomial_arguments_independent_of_limit':True,
                'all_power_arguments_independent_of_private_pell_coordinates':True,
                'records':records}


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--source-dir',type=Path,default=Path('research/optimized'))
    parser.add_argument('--artifacts',type=Path,default=None)
    parser.add_argument('--source-proof-helper',type=Path,default=Path(__file__).parent/'improved/audit_reductions.py')
    parser.add_argument('--original-source',type=Path,default=Path(__file__).parent/'shared/con_zfc_shared_certificates/direct/direct_calculus.py')
    parser.add_argument('--output',type=Path,default=Path('agent_repo_audit/FINAL_SEMANTIC_AUDIT.json'))
    args=parser.parse_args();directory=args.source_dir.resolve()
    sys.path.insert(0,str(directory))
    import base_builder
    from shared_power_builder import SharedPowerBuilder
    base_builder.Builder=SharedPowerBuilder
    source=json.loads((directory/'wire_eliminated_source.json').read_text())
    builder=base_builder.construct(source);builder.finalize()
    artifacts=args.artifacts.resolve() if args.artifacts else directory/'final'
    raw_path=artifacts/'raw_builder.json'
    raw=json.loads(raw_path.read_text())
    # Compare JSON-normalized exact inventories, independent of the exporter.
    def asjson(value):return json.loads(json.dumps(value))
    require(raw['variables']==builder.variables and raw['rows']==builder.rows,
            'frozen raw rows differ from audited builder')
    require(raw['macro_log']==asjson(builder.macro_log),
            'frozen semantic macro list differs from audited builder')
    require(raw['power_arguments']==asjson(builder.power_arguments),
            'frozen positive-power arguments differ from audited builder')
    require(raw['shared_pell']==asjson(builder.shared_pell),
            'frozen shared environment differs from audited builder')
    expected_powers=[{'base':n,'exponent':k,'output':m} for (n,k),m in builder.powers.items()]
    expected_indices=[{'exponent':k,'X':xy[0],'Y':xy[1]} for k,xy in builder.pell_indices.items()]
    require(raw['powers']==asjson(expected_powers) and raw['pell_indices']==asjson(expected_indices),
            'frozen power/index inventory differs from audited builder')
    helper_path=args.source_proof_helper
    spec=importlib.util.spec_from_file_location('independent_source_audit',helper_path)
    helpers=importlib.util.module_from_spec(spec);spec.loader.exec_module(helpers)
    cert=json.loads((artifacts/'envelope_certificate.json').read_text())
    oldsource=args.original_source
    source_checks={'syntax':helpers.source_change(oldsource,directory/'direct_calculus.py'),
                   'envelope':helpers.envelope_check(cert)|helpers.source_envelope_binding(directory,cert),
                   'final_literal':helpers.literal_check(artifacts)}
    audit=Audit(builder)
    receipt={'status':'PASS','positive_and_local_interfaces':audit.check_macros(),
             'shared_environment':audit.check_shared_environment(),
             'semantic_dependencies':audit.semantic_dependencies(),
             'literal_interface_rows_checked':audit.c,
             'raw_builder_sha256':sha256(raw_path.read_bytes()).hexdigest(),
             'frozen_raw_builder_exact_match':True,
             'source_and_final_literal':source_checks,
             'code_sha256':{name:sha256((directory/name).read_bytes()).hexdigest() for name in
                            ('base_builder.py','power_builder.py','shared_power_builder.py','direct_calculus.py','build.py')},
             'scope':'Exact finite interface and dependency audit; unbounded mathematical review is separate'}
    args.output.write_text(json.dumps(receipt,indent=2,sort_keys=True)+'\n')
    print(json.dumps({'status':receipt['status'],'literal_interface_rows_checked':audit.c,
                      'positive_power_calls':len(audit.positive),'shared_indices':len(builder.pell_indices),
                      'binomials':len(builder.binomials),'factorials':len(builder.factorials),
                      'code_sha256':receipt['code_sha256']},indent=2))


if __name__=='__main__':main()
