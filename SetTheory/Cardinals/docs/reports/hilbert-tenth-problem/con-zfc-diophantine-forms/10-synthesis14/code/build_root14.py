#!/usr/bin/env python3
"""Derive explicit root-eliminated blank-input circuits from inert JSON."""
import json
from collections import Counter
from pathlib import Path

ROOT=Path(__file__).resolve().parents[1]
RAW=json.loads((ROOT/'evidence/base67.json').read_text())
P=RAW.get('packet',RAW)
CIRCUITS=ROOT/'circuits'
CIRCUITS.mkdir(parents=True,exist_ok=True)

def live(rows, outputs):
    needed=set(outputs); out=[]
    for row in reversed(rows):
        if row[0] in needed:
            out.append(row)
            needed.update(v for v in row[2:] if isinstance(v,str))
    return out[::-1]

dep={'f'}; common=[]
for row in P['source']:
    if any(v in dep for v in row[2:]): dep.add(row[0])
    else: common.append(row)
if len(common)!=50: raise ValueError('Unexpected base67 dependency cone')

DATA=[
 ['u','*','i','c2'],['disc0','*','u','aux_coefficient_root'],['disc','+','disc0',1],
 ['RD','*','r_lhs','disc'],['zroot','+','R10a','RD'],['vroot','*','R10a','auxiliary_quotient'],
 ['v2','*','vroot','vroot'],['Dv2','*','disc','v2'],['z2','*','zroot','zroot'],
 ['p3','*','norm_pair','norm_index'],['p4','*','p3','norm_transport']]
LOCAL=[
 ['root_sum','+','Dv2','z2'],['root_gap','-','root_sum','aux_y2'],
 ['Qgap','*','R16','root_gap'],['Arat1','+','Qgap','aux_y2'],['Arat','-','Arat1',1],
 ['QDv2','*','R16','Dv2'],['Qz2','*','R16','z2'],['cross','*','QDv2','Qz2'],
 ['cross4','*',4,'cross'],['Arat2','*','Arat','Arat'],['root_norm','-','Arat2','cross4'],
 ['root_unit','+','root_norm',1],['product','*','p4','root_unit'],['polynomial','-','product',1]]
OUTER=[
 ['pQ','*','p4','R16'],['L','*','pQ','Dv2'],['M','*','pQ','z2'],
 ['pdiff','-','p4','pQ'],['Yterm','*','pdiff','aux_y2'],
 ['LM','+','L','M'],['LMY','+','LM','Yterm'],['outer','-','LMY',1],
 ['outer2','*','outer','outer'],['LMprod','*','L','M'],['LM4','*',4,'LMprod'],
 ['polynomial','-','outer2','LM4']]

def eval_rows(rows, values, mod=None):
    e=dict(values)
    for n,op,a,b in rows:
        a=a if isinstance(a,int) else e[a]
        b=b if isinstance(b,int) else e[b]
        e[n]=a+b if op=='+' else a-b if op=='-' else a*b
        if mod:e[n]%=mod
    return e

def degree(rows,wits):
    d={w:1 for w in wits}|{c:0 for c in P['fixed_numerals']}
    for n,op,a,b in rows:
        x=0 if isinstance(a,int) else d[a]
        y=0 if isinstance(b,int) else d[b]
        d[n]=x+y if op=='*' else max(x,y)
        if n=='norm_main':d[n]=18
    return d

def make(name,rows,outputs,eq=None):
    rows=live(rows,outputs); wits=[w for w in P['witnesses'] if w!='f']
    c=Counter(r[1] for r in rows); ds=degree(rows,wits)
    packet={'name':name,'witnesses':wits,'witness_domain':'strictly positive integers',
       'fixed_numerals':P['fixed_numerals'],'source':rows,'outputs':outputs,
       'ledger':{'operations':len(rows),'M':c['*'],'A':c['+']+c['-']},
       'degree_upper':{o:ds[o] for o in outputs},'equations':eq,
       'exact_degree':ds['polynomial'] if outputs==['polynomial'] else None,
       'degree_proof':'report.tex: uniform leading forms; generic source evaluation is only a diagnostic',
       'intermediates':'Signed polynomial abbreviations, not additional unknowns.'}
    (CIRCUITS/(name+'.json')).write_text(json.dumps(packet,indent=2)+'\n')
    print(name,packet['ledger'],packet['degree_upper'])
    return packet

if __name__=='__main__':
    make('root14_product75',common+DATA+LOCAL,['polynomial'])
    make('root14_outer73',common+DATA+OUTER,['polynomial'])
    eq=[['norm_first',1],['norm_main',1],['norm_index',1],['norm_transport',1],['root_norm',0]]
    make('root14_system69',common+DATA+LOCAL,[a for a,b in eq],eq)
