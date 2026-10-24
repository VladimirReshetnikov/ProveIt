#!/usr/bin/env python3
"""Replay the independent exact audit and verify literal binary evaluators."""
from pathlib import Path
from collections import Counter
import ast
import gzip
import json
import random
import subprocess
import sys

ROOT=Path(__file__).resolve().parent
NAMES=['sextic31','octic26','degree10_24','degree12_25','degree12_23','degree14_22']


def require(ok, message):
    if not ok:raise RuntimeError(message)


def eval_expression(expression, values, modulus):
    def walk(n):
        if isinstance(n,ast.Constant) and type(n.value)==int:return n.value%modulus
        if isinstance(n,ast.Name):return values[n.id]%modulus
        if isinstance(n,ast.UnaryOp) and isinstance(n.op,ast.USub):return -walk(n.operand)%modulus
        if isinstance(n,ast.BinOp):
            if isinstance(n.op,ast.Pow):
                require(isinstance(n.right,ast.Constant) and type(n.right.value)==int
                        and n.right.value>=0,'only fixed nonnegative powers')
                return pow(walk(n.left),n.right.value,modulus)
            x,y=walk(n.left),walk(n.right)
            if isinstance(n.op,ast.Add):return (x+y)%modulus
            if isinstance(n.op,ast.Sub):return (x-y)%modulus
            if isinstance(n.op,ast.Mult):return x*y%modulus
        raise ValueError('not a permitted polynomial node: '+ast.dump(n))
    return walk(ast.parse(expression,mode='eval').body)


def eval_circuit(nodes, values, modulus):
    out=[]
    for i,node in enumerate(nodes):
        if node['op']=='const':v=node['value']%modulus
        elif node['op']=='symbol':v=values[node['name']]%modulus
        else:
            require(len(node['args'])==2 and all(0<=j<i for j in node['args']),
                    'acyclic, exactly binary arithmetic node')
            x,y=(out[j] for j in node['args'])
            if node['op']=='add':v=(x+y)%modulus
            elif node['op']=='sub':v=(x-y)%modulus
            elif node['op']=='mul':v=x*y%modulus
            else:raise ValueError('unknown arithmetic operation')
        out.append(v)
    return out


def main():
    # The exact source restoration has its own independently implemented ring.
    python=[sys.executable]+(['-O'] if sys.flags.optimize else [])
    proc=subprocess.run(python+[str(ROOT/'independent_check.py'),str(ROOT)],
                        cwd=ROOT,check=True,capture_output=True,text=True)
    independent=json.loads(proc.stdout)
    require(independent['status']=='PASS','independent exact source restoration')
    ext_proc=subprocess.run(python+[str(ROOT/'independent_extensions.py'),str(ROOT)],
                            cwd=ROOT,check=True,capture_output=True,text=True)
    extensions=json.loads(ext_proc.stdout)
    require(extensions['status']=='PASS','independent exact row-operation extensions')
    binding=json.loads((ROOT/'coefficients/BINDING.json').read_text())
    coefficients={key:int.from_bytes(gzip.decompress((ROOT/'coefficients'/rec['file']).read_bytes()),'little')
                  for key,rec in binding['payloads'].items()}
    diagnostics=[]
    for name in NAMES:
        packet=json.loads((ROOT/(name+'.json')).read_text())
        graph=json.loads((ROOT/(name+'_circuit.json')).read_text())
        require(packet['variables']==graph['variables'],'same variable ordering: '+name)
        require(packet['fixed_numerals']==graph['fixed_numerals'],'same fixed ports: '+name)
        require(len(packet['residuals'])==len(graph['residual_outputs']),
                'same residual count: '+name)
        live=set()
        def visit(i):
            if i not in live:
                live.add(i)
                for j in graph['nodes'][i].get('args',[]):visit(j)
        visit(graph['output'])
        require(len(live)==len(graph['nodes']),'every node is live: '+name)
        counts=Counter(node['op'] for node in graph['nodes'] if node['op'] in {'add','sub','mul'})
        require(dict(counts)==graph['binary_operation_counts'],'exact gate recount: '+name)
        require(sum(counts.values())==graph['total_binary_operations'],'total gate count: '+name)
        rng=random.Random(237526)
        trials=0
        for modulus in [(1<<61)-1,(1<<127)-1]:
            for _ in range(40):
                values=dict(coefficients)
                values.update({v:rng.randrange(-20,21) for v in packet['variables']})
                direct=[eval_expression(row,values,modulus) for row in packet['residuals']]
                evaluated=eval_circuit(graph['nodes'],values,modulus)
                require(direct==[evaluated[i] for i in graph['residual_outputs']],
                        'circuit/direct residual diagnostic: '+name)
                require(sum(x*x for x in direct)%modulus==evaluated[graph['output']],
                        'literal sum of squares output diagnostic: '+name)
                trials+=1
        diagnostics.append({'name':name,'variables':len(packet['variables']),
            'exact_degree':packet['exact_degree'],'binary_operations':sum(counts.values()),
            'binary_counts':dict(counts),'literal_modular_evaluation_diagnostics':trials})
    result={'status':'PASS','independent_source_restoration':independent,
            'independent_extensions':extensions,
            'circuit_replays':diagnostics,
            'boundary':'modular samples are additional circuit diagnostics, not the proof of the mathematical theorem'}
    (ROOT/'VERIFY_RESULTS.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))


if __name__=='__main__':main()
