#!/usr/bin/env python3
"""Independent exact replay of the exported direct polynomials.

Imports the independent rational-SOS checker, never the generator/optimizer.
Also checks the entire raw-to-affine export, all collected coefficients,
majorant ledgers, source pins, liveness, and deliberate corruptions.
"""
from pathlib import Path
from hashlib import sha256
from collections import defaultdict
import importlib.util
import json
import subprocess
import sys
from copy import deepcopy

ROOT=Path(__file__).resolve().parents[1]

def need(ok, message):
    if not ok:
        raise ValueError(message)

def read(path): return json.loads((ROOT/path).read_bytes())

def collect(terms):
    result=defaultdict(int)
    for c,m in terms:
        need(type(c) is int and all(type(v) is int for v in m), 'literal integer data')
        result[tuple(sorted(m))]+=c
    return {m:c for m,c in result.items() if c}

def dumped(poly):return [[c,list(m)] for m,c in sorted(poly.items()) if c]

def multiply(a,b):
    return collect((c*d,m+n) for m,c in a.items() for n,d in b.items())

def substitute(poly, env):
    terms=[]
    for m,c in poly.items():
        p={():c}
        for i in m:p=multiply(p,env[i])
        terms.extend((c,m)for m,c in p.items())
    return collect(terms)

def expand_sos(eq):
    result=defaultdict(int)
    for row in eq['residuals']:
        p=collect(row['terms'])
        need(all(len(m)<=2 for m in p),'quadratic residual')
        for m,c in multiply(p,p).items():result[m]+=c
    return dumped(result)

def affine_replay(raw, source):
    """Prove all omitted raw wires restore nonnegatively and all rows match."""
    rows=raw['rows']; variables=raw['variables']
    definitions={r['gate']:(i,r)for i,r in enumerate(rows)if r.get('gate')is not None}
    need(len(definitions)==sum(r.get('gate')is not None for r in rows),'unique gate definitions')
    env={}; deleted=set(); eliminated=set()
    for v in range(len(variables)):
        env[v]={(v,):1}
        if v not in definitions:continue
        rid,row=definitions[v]; p=collect(row['terms'])
        if any(len(m)>1 for m in p):continue
        need(p.get((v,))==1,'monic affine pivot')
        rest={m:-c for m,c in p.items()if m!=(v,)}
        need(all(j<v for m in rest for j in m),'triangular affine definition')
        restored=substitute(rest,env)
        need(all(c>=0 and len(m)<=1 for m,c in restored.items()),'nonnegative affine inverse')
        if len(restored)<=4:
            env[v]=restored;deleted.add(rid);eliminated.add(v)
    remaining=[i for i in range(len(variables))if i not in eliminated]
    need([variables[i]for i in remaining]==source['variables'],'entire retained coordinate list')
    rename={old:new for new,old in enumerate(remaining)}
    expected=[]
    for rid,row in enumerate(rows):
        p=substitute(collect(row['terms']),env)
        if rid in deleted:
            need(not p,'deleted defining row restored to zero')
            continue
        need(p,'no unaccounted zero source row')
        need(all(j in rename for m in p for j in m),'no missing restored variable')
        expected.append(dict(label=row['label'],terms=dumped({tuple(rename[j]for j in m):c for m,c in p.items()})))
    need(expected==source['residuals'],'every complete raw residual after affine inverse')
    need(len(eliminated)==599 and len(remaining)==633,'raw export counts')
    return dict(raw_variables=len(variables),raw_rows=len(rows),affine_eliminations=len(eliminated),
                retained_variables=len(remaining),retained_rows=len(expected))

def check_majorants(raw):
    results={}
    for key,expected in [('label_majorant',3445908),('local_majorant',6893253)]:
        ledger=raw[key]; degrees={}
        def weight(atom):
            kind,value=atom
            if kind=='c':return max(0,(value-1).bit_length())
            return degrees.get(value,1)
        seen=set()
        for gate in ledger['gates']:
            out=gate['output'];need(out not in seen,'unique bound gate')
            a,c=weight(gate['left']),weight(gate['right'])
            value=max(a,c)+1 if gate['operation']=='add' else a+c
            need(value==gate['exponent'],'every majorant arithmetic exponent')
            degrees[out]=value;seen.add(out)
        need(weight(ledger['output'])==ledger['exponent']==expected,'final majorant exponent')
        results[key]=dict(gates=len(ledger['gates']),exponent=expected)
    need(3445908<=4194304 and 2*4194304>=6893253,'shared exponent dominates both bounds')
    return results

def check_all():
    source=read('direct/source/equation.json');raw=read('direct/raw_complete.json')
    need(source['domain']=='nonnegative integers','declared natural domain')
    original=(ROOT/'upstream/engine/upstream/provenance/upstream/wire_eliminated_source.json').read_bytes()
    need(sha256(original).hexdigest()==source['wire_eliminated_source_sha256'],'complete C222 source binding')
    affine=affine_replay(raw,source)
    need(expand_sos(source)==read('direct/source/polynomial.json')['terms'],'complete source expansion')
    majorants=check_majorants(raw)
    spec=importlib.util.spec_from_file_location('independent_psd_checker',ROOT/'upstream/engine/code/psd_contract/check.py')
    checker=importlib.util.module_from_spec(spec);spec.loader.exec_module(checker)
    receipt={}
    for name,count,rows,terms in [('natural361',361,278,6759),('natural358',358,275,8229)]:
        eq=read('direct/'+name+'/equation.json');cert=read('direct/'+name+'/projection.json')
        proof,expanded=checker.verify(source,eq,cert)
        need(expanded==read('direct/'+name+'/polynomial.json')['terms'],'every recorded quartic coefficient')
        used={v for c,m in expanded for v in m}
        need(used==set(range(count)),'all final variables live')
        need((proof['variables'],proof['rows'],proof['exact_degree'],proof['expanded_monomials'])==
             (count,rows,4,terms),'exact final metrics')
        bad=deepcopy(eq);bad['residuals'][0]['terms'][0][0]+=1
        badcert=deepcopy(cert)
        badcert['target_equation_sha256']=sha256(checker.canonical(bad)).hexdigest()
        try:checker.verify(source,bad,badcert)
        except ValueError:pass
        else:raise ValueError('altered row accepted after updating target hash')
        proof['changed_row_rejected_after_rehash']=True
        receipt[name]=proof
    # This is the same checked raw system independently produced during research.
    prototype=read('checks/PROTOTYPE_BINDING.json')
    need(sha256(encoded_without_interface(raw)).hexdigest()==prototype['raw_without_interface_sha256'],
         'portable construction equals independently reviewed raw system')
    companion=read('direct/integer_companion.json')
    need(companion['domain']=='unrestricted integers' and companion['variable_count']==1074,
         'integer companion domain and dimension')
    need(companion['parent']=='natural358/equation.json' and
         companion['parent_sha256']==sha256((ROOT/'direct/natural358/equation.json').read_bytes()).hexdigest(),
         'integer companion exact parent binding')
    need(companion['variables']==[str(v)+str(i) for i in range(358) for v in ('a','b','c')],
         'integer companion coordinate order')
    need(len(companion['substitutions'])==358,'complete integer substitution count')
    for i, entry in enumerate(companion['substitutions']):
        a,b,c=3*i,3*i+1,3*i+2
        need(entry['parent_coordinate']==i and
             collect(entry['terms'])=={(a,a):1,(b,b):1,(c,c):1,(c,):1},
             'literal a^2+b^2+c(c+1) substitution')
    need(companion['exact_degree']==8,'integer companion declared degree')
    return dict(status='PASS',optimized=not __debug__,affine_export=affine,majorants=majorants,
                equations=receipt,integer_companion='All 358 substitutions and parent binding checked',
                scope='Exact finite identities and coefficients; ordinary unbounded proof is separate.')

def encoded_without_interface(raw):
    d=dict(raw);d.pop('interface',None)
    return (json.dumps(d,sort_keys=True,separators=(',',':'))+'\n').encode()

def main():
    result=check_all()
    flag=['-O'] if not __debug__ else []
    for script in ['code/check_latent_index.py','supplement/check.py']:
        done=subprocess.run([sys.executable,'-B']+flag+[str(ROOT/script)],capture_output=True,text=True)
        need(done.returncode==0,'independent child check '+script+'\n'+done.stdout+done.stderr)
    result['latent_index_and_full_supplement']='PASS'
    path=ROOT/'checks'/('VERIFY_OPTIMIZED.json'if not __debug__ else 'VERIFY.json')
    path.write_text(json.dumps(result,sort_keys=True,indent=2)+'\n')
    print(json.dumps(result,sort_keys=True,indent=2))

if __name__=='__main__':main()
