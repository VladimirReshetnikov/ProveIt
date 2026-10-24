#!/usr/bin/env python3
"""Exact generic norm identities and whole literal-source re-evaluation."""
import argparse
from copy import deepcopy
import hashlib
import json
from pathlib import Path
import sys
from build import build,cleared_norm4,DAG,Ref
from compact_norms import cleared_norm5
from exact_polynomial import Ring
from univariate import evaluate_univariate,load_constants

ROOT=Path(__file__).resolve().parent
def need(ok,message):
    if not ok:raise ValueError(message)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()

def evaluate(p,values):
    v=dict(values)
    for row in p['nodes']:
        a,b=[x if isinstance(x,int) else v[x] for x in row['args']]
        v[row['id']]=a+b if row['op']=='add' else a-b if row['op']=='sub' else a*b
    return p['output'] if isinstance(p['output'],int) else v[p['output']]

def encode(poly):
    return json.dumps([[list(m),c] for m,c in sorted(poly.terms.items())],separators=(',',':')).encode()

def cut_term(p,out,cuts,pool):
    """Exact term interning, with no digest or polynomial sampling involved."""
    byid={r['id']:r for r in p['nodes']};memo={}
    def intern(key):
        if key not in pool:pool[key]=len(pool)
        return pool[key]
    def go(x):
        if isinstance(x,int):return intern(('integer',x))
        if x in cuts:return intern(('formal',cuts[x]))
        if x in memo:return memo[x]
        need(x in byid,'no unapproved input below the declared norm cut')
        row=byid[x];a,b=map(go,row['args'])
        if row['op'] in ('add','mul') and a>b:a,b=b,a
        result=intern((row['op'],a,b));memo[x]=result;return result
    return go(out)

def literal_cut_check(old,new):
    roots=old['root_count'];names=['x','a','b','c']+(['d'] if roots==5 else [])+['C','delta']
    registers=['norm_z','rad_A','rad_B','rad_D']+(['rad_G'] if roots==5 else [])+['Cnum','delta']
    cuts={new['named_registers'][r]:n for r,n in zip(registers,names)}
    original=json.loads((ROOT/f'parent/forms/norm{roots}_cleared_dag.json').read_text());pool={}
    need(cut_term(old,old['norm_output'],cuts,pool)==cut_term(original,original['output'],dict(zip(original['inputs'],names)),pool),'actual parent norm equals pinned generic Taylor term')
    d=DAG(names);v=[Ref(d,n) for n in names]
    out=(cleared_norm5 if roots==5 else cleared_norm4)(*v)
    template=d.finish(out,{})
    need(cut_term(new,new['norm_output'],cuts,pool)==cut_term(template,template['output'],dict(zip(names,names)),pool),'actual new norm equals compact generic term')
    if roots==4:
        d=DAG(['N','G']);N,G=Ref(d,'N'),Ref(d,'G');final=d.finish((1+4*N)*(1+4*G)-1,{})
        norm_guard_cuts={new['norm_output']:'N',new['named_registers']['guard']:'G'}
        need(cut_term(new,new['output'],norm_guard_cuts,pool)==cut_term(final,final['output'],{'N':'N','G':'G'},pool),'literal finalizer unchanged')
    else:need(new['output']==new['norm_output'] and old['output']==old['norm_output'],'pure five-root norm finalizer')
    return {'old_norm_term_matches_pinned_template':True,'new_norm_term_matches_compact_template':True,'finalizer_term_matches':True,'method':'exact shared term interning modulo commutative operand order; no hashes'}

def generic_check(n):
    names=['x','a','b','c']+(['d'] if n==5 else [])+['C','delta'];r=Ring(names)
    v=[r.var(x) for x in names]
    actual=(cleared_norm5 if n==5 else cleared_norm4)(*v)
    old=json.loads((ROOT/f'parent/forms/norm{n}_cleared_dag.json').read_text())
    expected=evaluate(old,dict(zip(old['inputs'],v)))
    need(actual.terms==expected.terms,'exact free-radicand Taylor/compact identity')
    if n==5:
        expanded=json.loads((ROOT/'parent/five_square_norm_expanded.json').read_text())
        truth={tuple(m[:5]+[m[5],16-m[5]]):c for m,c in expanded['terms']}
        need(actual.terms==truth,'independent full32-conjugate polynomial')
    # The modification keeps node topology and operation count unchanged.
    corrupt=deepcopy(old)
    found=False
    for row in corrupt['nodes']:
        if any(x==64 for x in row['args']):
            row['args']=[65 if x==64 else x for x in row['args']];found=True;break
    if not found:
        row=corrupt['nodes'][-1];row['op']='add' if row['op']=='sub' else 'sub'
    wrong=evaluate(corrupt,dict(zip(corrupt['inputs'],v)))
    need(wrong.terms!=actual.terms,'same-operation-count corrupted norm rejected')
    return {'roots':n,'free_variables':names,'monomials':len(actual.terms),'all_integer_coefficients_equal':True,
        'coefficient_sha256':hashlib.sha256(encode(actual)).hexdigest(),'operation_preserving_mutation_rejected':True}

def prefix_check(parent,new):
    b=new['unchanged_prefix_boundary'];old={row['id']:row for row in parent['nodes'] if int(row['id'][1:])<b}
    got={row['id']:row for row in new['nodes'] if int(row['id'][1:])<b}
    need(old==got,'all original live prefix nodes retained exactly')
    need(parent['prefix_abbreviations']==new['prefix_abbreviations'],'all named polynomial definitions unchanged')
    need(parent['variables']==new['variables'] and parent['inputs']==new['inputs'],'variable and fixed-port order')
    # The program's finalizer still uses exactly the parent's guard. Its
    # norm equality holds for free radicands, so substitution is universal.
    need(parent['root_count']==new['root_count'] and parent['denominator_exponent']==new['denominator_exponent'],'same norm/clearing exponent')
    return {'literal_prefix_nodes':len(old),'all_nodes_identical':True,'coefficient_and_variable_order_identical':True}

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--output',type=Path,default=ROOT/'CHECKS.json');args=ap.parse_args()
    if (ROOT/'MANIFEST.json').exists():
        for row in json.loads((ROOT/'MANIFEST.json').read_text())['files']:
            p=ROOT/row['path'];need(p.stat().st_size==row['bytes'] and sha(p)==row['sha256'],'sealed candidate file')
    pins=json.loads((ROOT/'SOURCE_PINS.json').read_text())
    for p in pins['files']:need(sha(ROOT/p['path'])==p['sha256'],'pinned parent/source module')
    constants=load_constants(ROOT);receipts=[]
    for path in sorted((ROOT/'parent/forms').glob('integer*.json')):
        old=json.loads(path.read_text());p=build(old);file=ROOT/(p['name']+'.json')
        need(file.read_text()==json.dumps(p,indent=2)+'\n','deterministic literal re-evaluation')
        rec=evaluate_univariate(p,constants);rec['prefix']=prefix_check(old,p);rec['literal_cut']=literal_cut_check(old,p)
        rec['original_operations']=old['live_binary_operations'];rec['saved_operations']=old['live_binary_operations']-p['live_binary_operations']
        rec['circuit_sha256']=sha(file);receipts.append(rec)
    generic=[generic_check(4),generic_check(5)]
    result={'status':'PASS','python_optimization':sys.flags.optimize,'scope':'Exact equality of whole fixed polynomials; inherited ordinary semantic proof unchanged. No Lean/internal-model claim.',
        'generic_norm_identities':generic,'literal_equations':receipts,
        'whole_source34_binding_sha256':sha(ROOT/'coefficients/BINDING.json'),
        'source_pins_sha256':sha(ROOT/'SOURCE_PINS.json')}
    args.output.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
    print(json.dumps({'status':'PASS','generic_monomials':[r['monomials'] for r in generic],
          'circuits':[{k:r[k] for k in ('name','degree','live_binary_operations','saved_operations')} for r in receipts]}),flush=True)

if __name__=='__main__':main()
