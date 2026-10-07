#!/usr/bin/env python3
"""Check every printed computational decimal against regenerated diagnostics.

Decimal rounding guards prevent transcription and last-place rounding errors.
They do not change the numerical diagnostics into certified interval arithmetic.
"""
from decimal import Decimal, ROUND_HALF_EVEN, localcontext
import json
from pathlib import Path
import re


def require(condition, label):
    if not condition:
        raise RuntimeError('Manuscript numerical check failed: '+label)


def fixed(value, places):
    with localcontext() as context:
        context.prec = 100
        result = Decimal(value).quantize(Decimal(1).scaleb(-places),rounding=ROUND_HALF_EVEN)
        return format(result,'f')


def scientific(value, significant):
    with localcontext() as context:
        context.prec = 100
        decimal = Decimal(value)
        exponent = decimal.adjusted()
        mantissa = decimal.scaleb(-exponent)
        rounded = mantissa.quantize(Decimal(1).scaleb(1-significant),rounding=ROUND_HALF_EVEN)
        if abs(rounded) >= 10:
            rounded /= 10
            exponent += 1
        return format(rounded,'f')+r'\cdot10^{'+str(exponent)+'}'


def table(text, header):
    require(text.count(header) == 1,'unique table header '+header)
    return text.split(header,1)[1].split(r'\end{tabular}',1)[0]


def check_row(block, start, expected):
    matching = [line for line in block.splitlines() if line.startswith(start+' & ')]
    require(len(matching) == 1,'unique table row '+start)
    cells = matching[0].split(' & ')[1:]
    actual = []
    for cell in cells:
        values = re.findall(r'\$([^$]+)\$',cell)
        require(len(values) == 1,'one numerical cell in row '+start)
        actual.append(values[0])
    require(actual == expected,'row '+start+': '+str(actual)+' != '+str(expected))
    return {'row':start,'values':actual}


def run(manuscript, diagnostics, output_dir):
    text = Path(manuscript).read_text(encoding='utf-8')
    rows = []
    block = table(text,'Quantity & Approximate value')
    constants = [('$Q(1)$',diagnostics['Q'])]
    constants += [(f'$c_{r}$',diagnostics['coefficients'][r]) for r in range(1,5)]
    constants += [(r'$\ell_2$',diagnostics['logarithmic_coefficients'][2]),
                  (r'$[\mu(1+e^{-1})-e^{-1}/2]/Q(1)$',diagnostics['TV_coefficient'])]
    for label,value in constants:
        rows.append(check_row(block,label,[fixed(value,20)]))
    block = table(text,r'$n$ & $E_0(n)$ & $E_1(n)$ & $E_2(n)$ & $E_3(n)$')
    for row in diagnostics['forward']:
        rows.append(check_row(block,str(row['n']),[fixed(x,6) for x in row['scaled_remainders'][:4]]))
    block = table(text,r'$n$ & $x_4(\log a_n)-n$ & $(x_4-n)n^6\log n$ & $n\TV(P_{n,1,0},\nu_1)$')
    for row,tv in zip(diagnostics['inverse'],diagnostics['TV']):
        require(row['n'] == tv['n'],'inverse and TV row alignment')
        rows.append(check_row(block,str(row['n']),[scientific(row['H4_root_minus_n'],6),
                                                  fixed(row['scaled_H4_error'],6),
                                                  fixed(tv['n_times_TV'],6)]))
    cutoff = text.split('gives approximately',1)
    require(len(cutoff) == 2,'cutoff numerical paragraph exists')
    cutoff = cutoff[1].split(r'\]',1)[0]
    found = re.findall(r'[0-9]+\.[0-9]+\\cdot10\^\{-[0-9]+\}',cutoff)
    expected = [scientific(row['total_majorant_diagnostic'],3) for row in diagnostics['cutoff']]
    require(found == expected,'cutoff rounded majorants')
    # The prose decimal followed by an ellipsis is a truncation, not a rounding.
    prefix = diagnostics['TV_coefficient'].split('.')[0]+'.'+diagnostics['TV_coefficient'].split('.')[1][:7]
    require('$'+prefix+r'\ldots$' in text,'TV prose decimal prefix')
    result = {'status':'PASS','qualification':'Decimal transcription and rounding checks against ordinary numerical diagnostics; no interval certification',
              'rounding':'Decimal ROUND_HALF_EVEN','table_rows':rows,'cutoff_values':found,
              'TV_prose_prefix':prefix,'numeric_cells_checked':sum(len(row['values']) for row in rows)+len(found)+1}
    output_dir = Path(output_dir)
    output_dir.mkdir(parents=True,exist_ok=True)
    (output_dir/'manuscript_checks.json').write_text(json.dumps(result,indent=2,sort_keys=True)+'\n',encoding='utf-8')
    return result
