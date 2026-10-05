from pathlib import Path
import json,hashlib

def modular(base,exponent,modulus):
    value=1
    while exponent:
        if exponent&1:value=value*base%modulus
        base=base*base%modulus
        exponent//=2
    return value

def factors(number):
    out={};trial=2
    while trial*trial<=number:
        while number%trial==0:
            out[trial]=out.get(trial,0)+1;number//=trial
        trial+=1
    if number>1:out[number]=out.get(number,0)+1
    return out

records=[]
for modulus,h,order in [(33554431,25,450),(269089806001,125,44848301000)]:
    fac=factors(order)
    if modular(2,h,modulus)!=1 or modular(3,order,modulus)!=1:raise ValueError('full powers')
    proper=[]
    for prime in fac:
        value=modular(3,order//prime,modulus)
        if value==1:raise ValueError('proper order')
        proper.append({'prime':prime,'exponent':order//prime,'residue':value})
    records.append({'modulus':modulus,'two_exponent':h,'three_order':order,'factorization':fac,'proper_tests':proper})
combined=403634709000
if combined%450 or combined%44848301000:raise ValueError('common multiple')
# Factor maps independently recover the least common multiple.
a,b=[factors(n) for n in (450,44848301000)];lcm_value=1
for prime in a.keys()|b.keys():lcm_value*=prime**max(a.get(prime,0),b.get(prime,0))
if lcm_value!=combined:raise ValueError('least common multiple')
if not 2**11<3**7 or not 11*450>=11+28*25:raise ValueError('small inequalities')
covered=[]
for n in range(3,17):
    d=5**n
    if not 11*combined>=11+28*d:raise ValueError('range')
    covered.append(n)
if not 2*combined<3*5**17:raise ValueError('n17 boundary')
result={'status':'PASS: original finite modular arithmetic before freeze','helper_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'certificates':records,'combined_order':combined,'covered_exponents':[2]+covered,'maximum_d':(11*combined-11)//28,'endpoint_margin':11*combined-11-28*5**16,'no_full_repunit_at_n17_asserted':True,'predecessor_code_run_or_imported':False,'source_arrays_evaluated':False,'large_compiler_values_materialized':False}
print(json.dumps(result,sort_keys=True,indent=2))
