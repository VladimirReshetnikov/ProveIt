"""Bind the inherited small-operation templates to the new complete tuple."""
from pathlib import Path
import hashlib
import json

HERE = Path(__file__).resolve().parent
PIN = '8c6eec9d19ef80538c8e61ff6e0180040583446a'

def make(which):
    src = HERE/'upstream'/(which+'.original.json')
    old = json.loads(src.read_text())
    aliases = {'Jrep':'J','tau_root':'tau','transport_quotient':'z',
               'auxiliary_quotient':'T','y_aux':'y','Bm1':'beta',
               'Kconstant':'K0'} if which == 'product67' else {}
    def rename(x):
        return aliases.get(x,x) if isinstance(x,str) else x
    rows = [[rename(n),op,rename(a),rename(b)] for n,op,a,b in old['source']]
    witnesses = [rename(x) for x in old['witnesses']]
    ports = [rename(x) for x in old['fixed_numerals']]
    out = dict(name=which+'_compact115',witness_domain='strictly positive integers',
               witnesses=witnesses,fixed_numerals=ports,source=rows,
               coefficient_binding={'file':'../coefficients/COEFFICIENT_BINDING.json',
                   'aliases':{'beta':'beta','K0':'K','MC':'MC','MF':'MF_source'},
                   'warning':'All four ports must use the new complete tuple; MF is shifted.'},
               provenance={'pin':PIN,'input':str(src.relative_to(HERE)),
                   'sha256':hashlib.sha256(src.read_bytes()).hexdigest(),
                   'change':'Witness/port aliases only; arithmetic unchanged. Entire coefficient tuple rebound.'},
               proof='../proofs/INHERITED_'+('P67' if which=='product67' else 'RETAINED59')+'_PROOF.md')
    if 'output' in old:
        out['output']=rename(old['output'])
        out['exact_degree']=old['exact_degree']
        roots=[out['output']]
    else:
        out['comparisons']=[[rename(a),rename(b)] for a,b in old['comparisons']]
        out['residual_exact_degrees']=old['residual_exact_degrees']
        out['exact_maximum_degree']=old['exact_maximum_degree']
        roots=[x for pair in out['comparisons'] for x in pair if isinstance(x,str)]
    names=set(witnesses+ports)
    for n,op,a,b in rows:
        assert n not in names and op in ('+','-','*')
        assert all(isinstance(x,int) or x in names for x in (a,b))
        names.add(n)
    live=set(roots)
    for n,op,a,b in reversed(rows):
        assert n in live
        live.update(x for x in (a,b) if isinstance(x,str))
    assert set(witnesses+ports)<=live
    out['ledger']={'operations':len(rows),
                   'multiplications':sum(op=='*' for _,op,_,_ in rows),
                   'additions_subtractions':sum(op!='*' for _,op,_,_ in rows),
                   'all_gates_live':True,'all_ports_live':True}
    return out

def main():
    for name,count in [('product67',67),('retained16_system59',59)]:
        obj=make(name)
        assert obj['ledger']['operations']==count
        (HERE/(name+'.json')).write_text(json.dumps(obj,indent=2)+'\n')
        print(name,obj['ledger'])

if __name__=='__main__':
    main()
