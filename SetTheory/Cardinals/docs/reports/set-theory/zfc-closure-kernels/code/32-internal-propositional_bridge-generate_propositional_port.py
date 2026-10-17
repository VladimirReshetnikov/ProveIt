"""Port Jeff's exact CD254 MP certificates to named-formula Lean.

Input is pinned upstream ZF/m254/coq/logic/CD254.v, commit
297ab8df7e5de329605c3875b4934643b371a5e3 (Jeff / Mira-Cult project).
Only syntax and the premise order of MP change; no search is performed.
"""
from pathlib import Path
import re, json, hashlib

ROOT = Path(__file__).resolve().parent
SRC = ROOT / 'CD254.v'
OUT = ROOT / 'Computability/BusyBeaver/Lean/BusyBeaver/ZFC/Lukasiewicz.lean'

def sexpr(text):
    toks=re.findall(r'\(|\)|[^()\s]+',text)
    def go(i):
        if toks[i]!='(':return toks[i],i+1
        xs=[];i+=1
        while toks[i]!=')':
            x,i=go(i);xs.append(x)
        return xs,i+1
    x,i=go(0)
    if i!=len(toks):raise ValueError('Trailing expression tokens')
    return x

def term(x):
    if isinstance(x,str):return 'bot' if x=='0' else x
    if x[0]!='wim' or len(x)!=3:raise ValueError(x)
    return '(imp '+term(x[1])+' '+term(x[2])+')'

def proof(x):
    if x[0]=='T_mp':
        if len(x)!=5 or x[1:3]!=['_','_']:raise ValueError(x)
        return '(Thm.mp '+proof(x[4])+' '+proof(x[3])+')'
    if x[0].startswith('cd_'):return '('+x[0]+' '+' '.join(term(y) for y in x[1:])+')'
    raise ValueError(x)

def formula(x,env):
    if isinstance(x,str):return env.get(x,x)
    if x[0]!='wim' or len(x)!=3:raise ValueError(x)
    return (formula(x[1],env),formula(x[2],env))

def checkproof(x,lemmas,env):
    if x[0]=='T_mp':
        minor=checkproof(x[3],lemmas,env);major=checkproof(x[4],lemmas,env)
        if not isinstance(major,tuple) or major[0]!=minor:raise ValueError('MP mismatch')
        return major[1]
    variables,form=lemmas[x[0]]
    if len(variables)!=len(x)-1:raise ValueError('Arity mismatch')
    return formula(form,dict(zip(variables,(formula(y,env) for y in x[1:]))))

def main():
    data=SRC.read_bytes()
    gitsha=hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()
    if gitsha!='78dcc05ec4cd22e19b9ef12003b93eb787a408bc':raise ValueError('Unexpected CD254.v input')
    items=re.findall(r'Lemma (cd_\d+) \((.*?) : nat\) : thm254 (.*?)\.\nProof\. exact (.*?)\. Qed\.',data.decode())
    if len(items)!=107:raise ValueError('Wrong certificate length')
    out=['import BusyBeaver.ZFC.TarskiCalculus','import BusyBeaver.ZFC.Kalmar','', '/-!',
         'Attribution: the 107 cd_0--cd_106 derivations below are a syntax port of',
         'Jeff\'s published ZF/m254/coq/logic/CD254.v, upstream commit',
         '297ab8df7e5de329605c3875b4934643b371a5e3. The upstream file credits',
         'cdgen.py and cdsearch.py for generating its condensed-detachment proofs.',
         'This port changes natural codes to NF, wim to imp, dummy 0 to bot,',
         'and reverses MP premise order. No new propositional proof is claimed.',
         'The extra ex-falso bridge at the end uses rho6, not rho8 alone.',
         '-/','', 'namespace SetTheory.BusyBeaver.ZFC.Tarski','open NF','variable {Ax : NF → Prop}',
         '', 'namespace PropositionalCertificate','']
    lemmas={}
    for name,vars_,form,prf in items:
        form=sexpr(form);prf=sexpr(prf);variables=vars_.split()
        if name=='cd_0':
            if prf!=['T_r8','v2','v3','v0','v1']:raise ValueError('Unexpected rho8 parameter order')
            rendered='Thm.rho8 v0 v1 v2 v3'
        else:
            if checkproof(prf,lemmas,{})!=formula(form,{}):raise ValueError('Conclusion mismatch '+name)
            rendered=proof(prf)
        lemmas[name]=(variables,form)
        out+=['theorem '+name+' ('+' '.join(variables)+' : NF) : Thm Ax '+term(form)+' :=',
              '  '+rendered,'']
    out+=['end PropositionalCertificate','', 'open PropositionalCertificate','',
          'theorem row_k (a b : NF) : Thm Ax (imp a (imp b a)) := cd_16 a b','',
          'theorem row_s (a b c : NF) :',
          '    Thm Ax (imp (imp a (imp b c)) (imp (imp a b) (imp a c))) := cd_106 a b c','',
          'theorem row_peirce (a b : NF) : Thm Ax (imp (imp (imp a b) a) a) := cd_25 a b','',
          '/-- Primitive falsity is explosive using K, S, MP and rho6. -/',
          'theorem row_efq (p : NF) : Thm Ax (imp bot p) := by',
          '  let q := ex 0 (all 0 p)',
          '  have hbq : Thm Ax (imp bot q) := row_k bot (all 0 (neg (all 0 p)))',
          '  have hqp : Thm Ax (imp q p) := Thm.rho6 0 p',
          '  have hbqp : Thm Ax (imp bot (imp q p)) := Thm.mp (row_k (imp q p) bot) hqp',
          '  exact Thm.mp (Thm.mp (row_s bot q p) hbqp) hbq','',
          '/-- The emitted rows discharge every propositional hypothesis of TarskiComplete. -/',
          'theorem classical_from_rows (Ax : NF → Prop) : Kalmar.Classical imp bot (Thm Ax) :=',
          '  { mp := Thm.mp, k := row_k, s := row_s, peirce := row_peirce, efq := row_efq }','',
          'end SetTheory.BusyBeaver.ZFC.Tarski','',
          '#print axioms SetTheory.BusyBeaver.ZFC.Tarski.row_k',
          '#print axioms SetTheory.BusyBeaver.ZFC.Tarski.row_s',
          '#print axioms SetTheory.BusyBeaver.ZFC.Tarski.row_peirce',
          '#print axioms SetTheory.BusyBeaver.ZFC.Tarski.row_efq',
          '#print axioms SetTheory.BusyBeaver.ZFC.Tarski.classical_from_rows','']
    OUT.write_text('\n'.join(out))
    print(json.dumps({'upstream_git_blob':gitsha,'lemmas':len(items),'checked_mp_steps':len(items)-1,'output':str(OUT),'sha256':hashlib.sha256(OUT.read_bytes()).hexdigest()},indent=2))

if __name__=='__main__':main()
