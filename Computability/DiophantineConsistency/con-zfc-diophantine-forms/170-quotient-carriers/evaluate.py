#!/usr/bin/env python3
"""Evaluate a supplied integer tuple in an explicit equation from this archive.

Supports direct sum-of-squares residual JSON and compact arithmetic DAG JSON,
including equations/P36_integer.json. Use --modulus for a compact modular result.
"""
from pathlib import Path
import argparse, gzip, hashlib, json, sys

ROOT=Path(__file__).resolve().parent

def need(condition,message):
    if not condition:raise ValueError(message)

def coordinate_names(equation):
    if 'source' in equation:
        names=equation.get('witnesses')
        need(isinstance(names,list) and all(isinstance(x,str) for x in names),
             'DAG must declare an ordered witness list')
        need(len(set(names))==len(names),'Repeated witness name')
        return names
    need('residuals' in equation,'Expected a residual system or arithmetic DAG')
    declared=equation.get('variables')
    n=len(declared) if isinstance(declared,list) else declared
    need(type(n) is int and n>0,'Residual system must declare its variable count or ordered variable records')
    return ['x'+str(i) for i in range(n)]

def read_coordinates(data,names,domain):
    if isinstance(data,dict):
        need(set(data)==set(names),'Coordinate object must contain exactly: '+', '.join(names))
        values=[data[x] for x in names]
    else:
        need(isinstance(data,list),'Coordinates must be a JSON array or an object keyed by input names')
        values=data
    need(len(values)==len(names),'Expected exactly '+str(len(names))+' coordinates')
    need(all(type(x) is int for x in values),'Every coordinate must be a JSON integer (not a Boolean or float)')
    need(domain in {'unrestricted integers','strictly positive integers'},'Unrecognized equation domain')
    if domain=='strictly positive integers':
        bad=[names[i] for i,x in enumerate(values) if x<=0]
        need(not bad,'This equation requires strictly positive coordinates; invalid: '+', '.join(bad))
    return values

def fixed_values(equation,modulus):
    ports=equation.get('fixed_numerals',[])
    if not ports:return {}
    need(isinstance(ports,list) and len(set(ports))==len(ports),'Malformed fixed-port list')
    binding_path=ROOT/'compact/COEFFICIENTS.json'
    binding=json.loads(binding_path.read_text())
    declared=equation.get('coefficient_binding',{}).get('ports',{})
    values={}
    for name in ports:
        need(name in binding['ports'] and name in declared,'Unknown or unbound fixed port: '+name)
        meta=binding['ports'][name]
        need(declared[name].get('raw_sha256')==meta['raw_sha256'] and
             declared[name].get('bits')==meta['bits'],'Equation requests a different coefficient tuple: '+name)
        raw=gzip.decompress((binding_path.parent/binding['path']/meta['file']).read_bytes())
        need(hashlib.sha256(raw).hexdigest()==meta['raw_sha256'],'Coefficient byte digest failed: '+name)
        value=int.from_bytes(raw,'little')
        need(value.bit_length()==meta['bits'],'Coefficient bit length failed: '+name)
        values[name]=value if modulus is None else value%modulus
    return values

def evaluate(equation,coordinates,modulus=None):
    need(modulus is None or (type(modulus) is int and modulus>=2),'Modulus must be an integer at least 2')
    names=coordinate_names(equation)
    values=read_coordinates(coordinates,names,equation.get('domain'))
    reduce=(lambda x:x) if modulus is None else (lambda x:x%modulus)
    if 'source' in equation:
        env={name:reduce(value) for name,value in zip(names,values)}
        ports=fixed_values(equation,modulus)
        need(not (set(env)&set(ports)),'Witness/fixed-port name collision')
        env.update(ports)
        for row in equation['source']:
            need(isinstance(row,list) and len(row)==4,'Malformed DAG row')
            name,op,left,right=row
            need(isinstance(name,str) and name not in env,'Duplicate DAG register: '+str(name))
            need(op in {'+','-','*'},'Only addition, subtraction and multiplication are supported')
            def get(x):
                if type(x) is int:return reduce(x)
                need(isinstance(x,str) and x in env,'Unknown or forward DAG reference: '+str(x))
                return env[x]
            a,b=get(left),get(right)
            env[name]=reduce(a+b if op=='+' else a-b if op=='-' else a*b)
        output=equation.get('output')
        need(isinstance(output,str) and output in env,'Missing DAG output')
        value=env[output];residuals=None
    else:
        residuals=[]
        for row in equation['residuals']:
            need(isinstance(row,dict) and isinstance(row.get('terms'),list),'Malformed residual row')
            total=0
            for term in row['terms']:
                need(isinstance(term,list) and len(term)==2,'Malformed sparse term')
                coefficient,monomial=term
                need(type(coefficient) is int and isinstance(monomial,list),'Malformed sparse coefficient or monomial')
                product=reduce(coefficient)
                for index in monomial:
                    need(type(index) is int and 0<=index<len(values),'Sparse monomial index out of range')
                    product=reduce(product*values[index])
                total=reduce(total+product)
            residuals.append(total)
        value=reduce(sum(x*x for x in residuals))
    result={'variables':len(names),'domain':equation['domain']}
    if modulus is None:
        result.update(value=value,is_zero=value==0)
        if residuals is not None:result['nonzero_residuals']=sum(x!=0 for x in residuals)
    else:
        result.update(modulus=modulus,value_modulo=value,vanishes_modulo=value==0)
        if residuals is not None:result['nonzero_residuals_modulo']=sum(x!=0 for x in residuals)
    return result

def main():
    parser=argparse.ArgumentParser(description=__doc__,formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument('coordinates',type=Path,
                        help='JSON array in declared input order, or object keyed by input names (x0,... for direct equations)')
    parser.add_argument('--equation',type=Path,default=Path('equations/P217/equation.json'),
                        help='equation JSON; relative paths are resolved from the archive root (default: equations/P217/equation.json)')
    parser.add_argument('--modulus',type=int,help='evaluate modulo an integer at least 2')
    args=parser.parse_args()
    if hasattr(sys,'set_int_max_str_digits'):sys.set_int_max_str_digits(0)
    path=args.equation if args.equation.is_absolute() else ROOT/args.equation
    try:
        equation=json.loads(path.read_text());coordinates=json.loads(args.coordinates.read_text())
        result=evaluate(equation,coordinates,args.modulus)
    except (OSError,ValueError,KeyError,TypeError) as error:
        parser.error(str(error))
    result['equation']=str(path.relative_to(ROOT)) if path.is_relative_to(ROOT) else str(path)
    print(json.dumps(result,indent=2))

if __name__=='__main__':main()
