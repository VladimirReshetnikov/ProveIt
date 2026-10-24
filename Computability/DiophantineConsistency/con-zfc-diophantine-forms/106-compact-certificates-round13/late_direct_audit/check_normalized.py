#!/usr/bin/env python3
"""Independent diagonal sign-orbit, sign-closure, guard and polynomial audit."""
import argparse
import collections
import json
from pathlib import Path
import sys
sys.path.insert(0,str(Path(__file__).resolve().parent.parent/'direct_audit'))
from check_exact import Audit,need,add,mul,clean,sparse,key,sha

def inspect_integer(A,path,certificate_override=None):
    raw=A.c;eq=json.loads((path/'equation.json').read_text());poly=json.loads((path/'expanded_polynomial.json').read_text());cert=certificate_override if certificate_override is not None else json.loads((path/'normalization_certificate.json').read_text())
    free=set(raw['bindings']['unrestricted_integer_quotients']);allowed={};expected=set()
    for m in raw['macros']:
        if m['kind']=='integer_congruence':
            i=m['quotient'][1];expected.add(i);allowed[i]={m['label']+'.integer'}
        if m['kind']=='power':
            need(m.get('parametric'),'sign audit expects parametric power')
            for q,label in zip(m['quotients'],['B_mod_U','S_definition','R_definition','power_mod_T']):
                i=q[1];expected.add(i);allowed[i]={m['tag']+'.'+label}
    need(free==expected==set(cert['unrestricted_integer_quotients']),'incorrect free quotient exemptions')
    dependency={}
    for i in range(len(A.vars)):
        if i in free:dependency[i]={i}
        elif i in A.gates:dependency[i]=set().union(*(dependency[j] for mon in A.gate_rhs(i) for j in mon))
        else:dependency[i]=set()
    for label,row in A.named.items():
        affected=set().union(*(dependency[j] for mon in row for j in mon))
        need(all(label in allowed[i] for i in affected),'signed quotient leaks to another constraint')
    required={i for i,v in enumerate(A.vars) if v['kind']!='gate' and i not in free}
    need(required==set(cert['required_semantic_variables']),'wrong required semantic set')
    seed=set(cert['raw_seed_indices']);pivots=set(cert['normalized_pivots'])
    need(seed<=required and pivots<=required and not seed&pivots,'invalid seed/pivot separation')
    canonical={A.names[m['tag']+'.'+name] for m in A.macro if m['kind']=='power' for name in ['U','Z']}
    need(pivots==canonical,'not exactly the indexed Pell U/Z pivots')
    names=[v['name'] for v in A.e['variables']];mapping={A.names[n]:i for i,n in enumerate(names)}
    need(len(cert['actions'])==len(pivots),'action count')
    observed=set()
    def parity(mon,flips):return sum(i in flips for i in mon)%2
    for action in cert['actions']:
        pivot=action['pivot'];flips=set(action['raw_flips']);observed.add(pivot)
        need(pivot in pivots and action['name']==A.vars[pivot]['name'],'wrong action pivot')
        need(flips&required=={pivot} and not flips&seed,'sign action changes another required coordinate')
        raw_signs=[]
        for r in A.rows:
            values={parity(mon,flips) for c,mon in r['terms']}
            need(len(values)==1,'raw residual not equivariant under sign action')
            raw_signs.append(next(iter(values)))
        need(raw_signs==action['raw_row_parities'],'wrong raw parity certificate')
        exported={mapping[i] for i in flips if i in mapping}
        need(exported==set(action['exported_flips']),'wrong exported sign action')
        export_signs=[]
        for r in A.e['residuals']:
            values={parity(mon,exported) for c,mon in r['terms']}
            need(len(values)==1,'exported residual not equivariant')
            export_signs.append(next(iter(values)))
        need(export_signs==action['exported_row_parities'],'wrong exported parity certificate')
    need(observed==pivots,'missing sign normalization pivot')
    rules=[]
    for r in cert['rules']:
        idx=r['row'];i=r['variable'];d=r['positive_divisor'];q=sparse(A.rows[idx]['terms'])
        need((i,) in q and abs(q[(i,)])==d and d>0,'invalid sign divisor')
        need(all(i not in mon for mon in q if mon!=(i,)),'sign variable occurs on right')
        direction=1 if q[(i,)]>0 else -1
        rhs={mon:-direction*c for mon,c in q.items() if mon!=(i,)}
        need(all(c>=0 for c in rhs.values()),'negative sign-rule coefficient')
        deps={j for mon,c in rhs.items() if c for j,exponent in collections.Counter(mon).items() if exponent%2}
        need(deps==set(r['dependencies']),'wrong odd-power dependency')
        rules.append((i,deps))
    known=seed|pivots
    for k in cert['application_order']:
        need(0<=k<len(rules),'bad sign rule index');i,deps=rules[k]
        need(deps<=known,'sign rule applied too early');known.add(i)
    need(required<=known and known==set(cert['known_nonnegative_variables']),'incomplete normalized sign closure')
    base_count=len(names);need(eq['variables'][:base_count]==A.e['variables'],'integer core prefix changed')
    expected_rows=list(A.e['residuals']);aux=base_count;guardmap=[]
    for old in sorted(seed):
        i=mapping[old];row={(i,):2};indices=[]
        for j in range(aux,aux+3):
            row[(j,)]=-1;row[(j,j)]=-1;indices.append(j)
            need(eq['variables'][j]=={'name':'triangular.'+str(i)+'.'+str(j-aux),'kind':'integer_auxiliary'},'triangular variable mismatch')
        aux+=3;expected_rows.append({'label':'nonnegative.'+str(i),'terms':[[c,list(m)] for m,c in row.items()]})
        guardmap.append({'raw':old,'exported':i,'auxiliaries':indices})
    need(guardmap==cert['guard_map'],'guard map mismatch')
    need(collections.Counter((r['label'],key(sparse(r['terms']))) for r in expected_rows)==collections.Counter((r['label'],key(sparse(r['terms']))) for r in eq['residuals']),'integer guard row mismatch')
    P=collections.defaultdict(int);used=set()
    for r in eq['residuals']:
        q=sparse(r['terms']);need(all(len(m)<=2 for m in q),'integer residual is not quadratic')
        used.update(i for mon in q for i in mon)
        for mon,c in mul(q,q).items():P[mon]+=c
    P=clean(P);need(P==sparse(poly['terms']),'integer SOS coefficient mismatch')
    need(aux==len(eq['variables'])==poly['variable_count'] and used==set(range(aux)),'integer variable mismatch')
    metrics={'integer_variables':aux,'quadratic_residuals':len(eq['residuals']),'degree':max(map(len,P)),'monomials':len(P),'coefficient_height':max(map(abs,P.values())),
             'nonnegativity_seeds':len(seed),'normalized_semantic_pivots':len(pivots),'unrestricted_integer_quotients':len(free)}
    need(metrics==eq['metrics'] and metrics['degree']==4,'integer metrics mismatch')
    return {'status':'PASS','metrics':metrics,'required_semantic_signs':len(required),'exact_sign_actions':len(pivots),'validated_sign_rules':len(rules),'applied_sign_rules':len(cert['application_order']),
            'sha256':{n:sha(path/n) for n in ['equation.json','expanded_polynomial.json','normalization_certificate.json']},
            'scope':'exact diagonal zero-set automorphisms, sign normalization and closure, complete guard identities and SOS expansion; not pointwise original positivity or kernel certification'}

def main():
    p=argparse.ArgumentParser();p.add_argument('core',type=Path);p.add_argument('integer',type=Path);p.add_argument('--output',type=Path);args=p.parse_args()
    a=Audit(args.core);core=a.run();result=inspect_integer(a,args.integer);result['core_audit']=core
    text=json.dumps(result,indent=2,sort_keys=True)+'\n'
    if args.output:args.output.write_text(text)
    print(text,end='')
if __name__=='__main__':main()
