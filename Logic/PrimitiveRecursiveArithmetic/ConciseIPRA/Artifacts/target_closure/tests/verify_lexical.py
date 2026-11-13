import ast, itertools, json, pathlib, random, subprocess, sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
PACKAGE = ROOT
OLD = ROOT / (sys.argv[2] if len(sys.argv)>2 else 'reference/typed_original.py')
NEW = ROOT / 'code' / (sys.argv[1] if len(sys.argv)>1 else 'lexical_explicit.py')
ALPHABET = '[],-0123456789 \t\r\n'

def ints_lists(a):
    return type(a) is int or (type(a) is list and all(map(ints_lists,a)))

def run(path,raw,optimized=False):
    args=[sys.executable]+(['-O'] if optimized else [])+[str(path)]
    try:
        p=subprocess.run(args,input=raw,capture_output=True,timeout=8)
        return p.returncode==0 and p.stdout==b'ACCEPT\n'
    except subprocess.TimeoutExpired:
        return False

fixture_results=[]
for p in sorted((PACKAGE/'tests/lexical').rglob('*.json')):
    if p.name=='upstream_cases.json':
        continue
    raw=p.read_bytes()
    for optimized in [False,True]:
        a,b=run(OLD,raw,optimized),run(NEW,raw,optimized)
        assert a==b, (p,optimized,a,b)
        fixture_results.append(dict(name=str(p.relative_to(PACKAGE/'tests/lexical')),optimized=optimized,accept=a))

base=json.loads((PACKAGE/'tests/lexical/zero_neutral/new_reflexivity_zero.json').read_text())
text=json.dumps(base,separators=(',',':'))
raw_cases={
    'compact': text.encode(),
    'whitespace': (' \t\r\n'+text+' \t\r\n').encode(),
    'pretty': json.dumps(base,indent=4).encode(),
    'negative_zero': text.replace('0','-0').encode(),
    'bom': b'\xef\xbb\xbf'+text.encode(),
    'bad_utf8': b'\xff'+text.encode(),
    'json_form_feed': ('\f'+text).encode(),
    'unicode_space': ('\u00a0'+text).encode(),
    'trailing_comma': (text[:-1]+',]').encode(),
    'unclosed_array': text[:-1].encode(),
    'two_values': (text+text).encode(),
    'unused_deep_valid_prefix': json.dumps([[[[[0]]]]]+base).encode(),
}
for name,value in [
    ('bool',True),('false',False),('null',None),('string','0'),
    ('dict',{}),('float',0.0),('nan',float('nan')),('infinity',float('inf')),
    ('negative_infinity',float('-inf')),('int',-23),('list',[0,1,-2]),
]:
    raw_cases['unused_'+name]=json.dumps([value]+base).encode()
for name,literal in [
    ('float_scientific','0e0'),('leading_zero','00'),('leading_plus','+0'),
    ('double_minus','--0'),('unicode_digit','٠'),('float_decimal','0.0'),
    ('float_exponent_plus','0e+0'),('escaped_string','"\\u0030"'),
]:
    raw_cases[name]=('['+literal+','+text[1:]).encode()

raw_results=[]
for name,raw in raw_cases.items():
    for optimized in [False,True]:
        a,b=run(OLD,raw,optimized),run(NEW,raw,optimized)
        assert a==b, (name,optimized,a,b)
        raw_results.append(dict(name=name,optimized=optimized,accept=a))

rng=random.Random(20261111)
def value(depth):
    atoms=[0,-1,10,True,False,None,'',{},1.5,float('nan')]
    if depth==0 or rng.randrange(2):
        return rng.choice(atoms)
    return [value(depth-1) for _ in range(rng.randrange(5))]

gate_checks=0
for _ in range(2000):
    a=value(5)
    raw=json.dumps(a,indent=rng.choice([None,0,1,2]),ensure_ascii=rng.choice([False,True]))
    assert (not raw.strip(ALPHABET))==ints_lists(json.loads(raw)),repr(raw)
    gate_checks+=1

# For arbitrary text, compare only successfully parsed JSON values; malformed
# strings are delegated to json.loads by both implementations.
chars='[],-01 \t\r\n.efalstrunNIF{}:"'
for length in range(5):
    for tup in itertools.product(chars[:10],repeat=length):
        raw=''.join(tup)
        try:
            value_=json.loads(raw)
        except (ValueError,RecursionError):
            continue
        assert (not raw.strip(ALPHABET))==ints_lists(value_),repr(raw)
        gate_checks+=1

receipt=dict(comparator=str(OLD.relative_to(ROOT)),candidate=str(NEW.relative_to(ROOT)),fixture_comparisons=len(fixture_results),raw_comparisons=len(raw_results),process_executions=2*(len(fixture_results)+len(raw_results)),gate_checks=gate_checks,mismatches=0,fixture_results=fixture_results,raw_results=raw_results,
    qualification='Equivalence is of the ideal finite certificate contract. Removing recursive j can change stack/resource failures for very deeply nested unused prefix data; resource exhaustion is never acceptance evidence.')
(ROOT/'evidence'/(NEW.stem+'_validation.json')).write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps({k:v for k,v in receipt.items() if not k.endswith('_results')},indent=2))
