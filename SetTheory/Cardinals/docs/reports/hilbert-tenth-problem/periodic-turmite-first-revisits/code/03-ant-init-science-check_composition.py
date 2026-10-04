#!/usr/bin/env python3
"""Own-code off-solution residual checks of the literal topological splice."""
if not __debug__:raise RuntimeError('Optimized mode unsupported: checks require assertions')
import argparse,contextlib,copy,io,json,pathlib,random,tempfile
from bridge_dag import build_uniform_wrapper
from compose_initialization import PairSource,Spliced,compose,output_destination,save_new_output
from check_bridge import Evaluated

def run(path):
    pair=PairSource(path);raw=json.loads(pathlib.Path(path).read_text());rng=random.Random(421740)
    cases=0
    for W in [-1,0,1]:
      for trial in range(16):
        d=Spliced(pair,period_y=7,emit=True)
        out=io.StringIO()
        with contextlib.redirect_stdout(out):build_uniform_wrapper(7,dag=d)
        z={name:rng.randrange(-3,4) for name in d.inputs}
        z['W']=W
        z.update({'C:0':0,'C:1':1,'C:2':2,'C:3':3,'C:4':4})
        for c in ['Cx','Cu','C198','Cbase']:z['C:'+c]=rng.randrange(-3,4)
        for c,n in [('tile',7),('first',7),('anchor',584)]:
            for j in range(n):z[f'C:{c}:{j}']=rng.randrange(-3,4)
        values=[];residuals=[]
        def val(x):return values[x] if type(x) is int else z[x]
        for line in out.getvalue().splitlines():
            row=json.loads(line)
            if row[0]=='eq':residuals.append(val(row[1])-val(row[2]));continue
            ident,op,a,b=row;assert ident==len(values)
            a,b=val(a),val(b);values.append(a*b if op=='*' else a+b if op=='+' else a-b)
        rec={w:z['Recoder:'+w] for w in pair.witnesses}
        rec.update(G=W**7,RawLeft=z['RawLeft'],RawRight=z['RawRight'])
        def rv(x):return x if type(x) is int else rec[x]
        for name,op,a,b in pair.nodes:
            a,b=rv(a),rv(b);rec[name]=a*b if op=='*' else a+b if op=='+' else a-b
        rec_res=[rv(a)-rv(b) for a,b in pair.equations[:-3]]
        aliases={key:rv(value) for key,value in pair.outputs.items()}
        z.update({'Dilation'+key:value for key,value in aliases.items()})
        wrapper=Evaluated(z);build_uniform_wrapper(7,dag=wrapper)
        assert residuals==wrapper.residuals[:3]+rec_res+wrapper.residuals[3:]
        assert all(val(d.aliases['Dilation'+key])==value for key,value in aliases.items())
        assert d.shared_radix_calls==1 and len(d.witnesses)==396
        cases+=1
    bad=[]
    x=copy.deepcopy(raw);x['nodes'][0][1]='/';bad.append(x)
    x=copy.deepcopy(raw);x['nodes'][0][2]='unknown';bad.append(x)
    x=copy.deepcopy(raw);x['nodes'][0][0]='not_g0';bad.append(x)
    x=copy.deepcopy(raw);x['outputs']['wrong_output']=x['outputs'].pop('T');bad.append(x)
    x=copy.deepcopy(raw);x['outputs']['T']='unknown';bad.append(x)
    x=copy.deepcopy(raw);x['witnesses'].append(x['witnesses'][0]);bad.append(x)
    x=copy.deepcopy(raw);x['nodes'][0][2]=True;bad.append(x)
    x=copy.deepcopy(raw);x['witnesses'][0]='G';bad.append(x)
    with tempfile.TemporaryDirectory() as t:
        for i,obj in enumerate(bad):
            p=pathlib.Path(t)/f'bad{i}.json';p.write_text(json.dumps(obj))
            try:PairSource(p)
            except (AssertionError,ValueError):pass
            else:raise AssertionError(('accepted tamper',i))
    receipt=compose(path)
    return {'status':'PASS','signed_off_solution_splice_cases':cases,'malformed_source_cases':len(bad),'literal_composition':receipt,'scope':'Exact DAG topology/count/residual identity checks; recoder equivalence and parent history theorem reviewed separately'}

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--pair-dag',required=True);p.add_argument('--output',type=pathlib.Path);a=p.parse_args()
    if a.output:output_destination(a.output)
    result=run(a.pair_dag);payload=json.dumps(result,indent=2)+'\n'
    if a.output:save_new_output(a.output,payload)
    print(payload,end='')
