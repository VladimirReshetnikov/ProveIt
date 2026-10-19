#!/usr/bin/env python3
"""Independently replay the pinned upstream L-only derivation of K, S, P.

The Coq file is parsed as finite data, never executed. Each declaration is
checked from earlier universally quantified declarations by substitution
and modus ponens, with the sole initial schema rho8. The theorem names at
the end are then checked against K, S and Peirce exactly.
"""
import hashlib
import json
from pathlib import Path
import re

def C(a,b):return ('C',a,b)
def L(a,b,c,u):return C(C(C(c,u),a),C(C(a,c),C(b,c)))

def parse(text):
    tokens=re.findall(r'[A-Za-z_][A-Za-z_0-9]*|[0-9]+|[()]',text)
    assert ''.join(tokens)==re.sub(r'\s+','',text)
    i=0
    def one():
        nonlocal i
        token=tokens[i];i+=1
        if token!='(':return token
        out=[]
        while tokens[i]!=')':out.append(one())
        i+=1
        return tuple(out)
    result=one()
    assert i==len(tokens)
    return result

def form(term,env):
    if isinstance(term,str):
        assert term in env or term=='0'
        return env.get(term,term)
    assert len(term)==3 and term[0]=='wim'
    return C(form(term[1],env),form(term[2],env))

def run(path):
    text=path.read_text()
    declarations=re.findall(r'Lemma (\w+) \(([^()]*) : nat\) : thm254 (.*?)\.\s*Proof\. exact (.*?)\. Qed\.',text,re.S)
    assert len(declarations)==111
    known={}
    mp_count=0
    def proof(term,env):
        nonlocal mp_count
        assert isinstance(term,tuple)
        name,*args=term
        if name=='T_r8':
            assert len(args)==4
            return L(*(form(x,env) for x in args))
        if name=='T_mp':
            assert len(args)==4 and args[:2]==['_','_']
            minor,major=proof(args[2],env),proof(args[3],env)
            assert isinstance(major,tuple) and major[0]=='C' and major[1]==minor
            mp_count+=1
            return major[2]
        assert name in known
        parameters,formula=known[name]
        assert len(args)==len(parameters)
        instance=dict(zip(parameters,(form(x,env) for x in args)))
        return form(formula,instance)
    for name,params,conclusion,body in declarations:
        assert name not in known
        parameters=params.split()
        env={x:x for x in parameters}
        formula=parse(conclusion)
        assert proof(parse(body),env)==form(formula,env),name
        known[name]=parameters,formula
    p,q,r='p','q','r'
    targets=dict(thm_K=C(p,C(q,p)),
                 thm_P=C(C(C(p,q),p),p),
                 thm_S=C(C(p,C(q,r)),C(C(p,q),C(p,r))))
    for name,target in targets.items():
        params,formula=known[name]
        assert form(formula,{x:x for x in params})==target
    return dict(status='PASS',source_file='CD254.v',source_sha256=hashlib.sha256(path.read_bytes()).hexdigest(),
                declarations_checked=len(declarations),modus_ponens_checks=mp_count,
                initial_schema='Lukasiewicz rho8 only',
                targets=['K','S','Peirce'],
                note='Universally quantified lemma instances checked by explicit formula substitution; no Coq execution')

def main():
    root=Path(__file__).resolve().parent
    local=root/'vendor/busy-beaver/ZF/m254/coq/logic/CD254.v'
    result=run(local)
    (root/'upstream_lukasiewicz_check.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))

if __name__=='__main__':main()
