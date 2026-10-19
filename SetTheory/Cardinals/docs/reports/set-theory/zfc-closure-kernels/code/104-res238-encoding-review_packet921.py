#!/usr/bin/env python3
"""Independent structural codec and exact-deletion audit; no source-code imports."""
import hashlib,json
from pathlib import Path
HERE=Path(__file__).resolve().parent
ROOT=HERE.parent/'formalisms'
old=json.loads((ROOT/'packet946.json').read_text())
new=json.loads((ROOT/'packet921.json').read_text())
assert new['equations']==old['equations'][:1]+old['equations'][2:]
for field in ('signature','start','target'):
    assert old[field]==new[field]
assert old['equations'][1]==[['d'],['N',['d'],['N',['d'],['d']]]]

def variables(t):
    if isinstance(t,str):return {t}
    return set().union(*(variables(a) for a in t[1:])) if len(t)>1 else set()
def nodes(t):return 1 if isinstance(t,str) else 1+sum(nodes(a) for a in t[1:])
def emit(data):
    symbols=list(data['signature']);arities=list(data['signature'].values())
    cap=max(len(variables(a)|variables(b)) for a,b in data['equations'])
    width=(len(symbols)+cap-1).bit_length()
    def tbits(t,names):
        if isinstance(t,str):return format(names.index(t),f'0{width}b')
        assert t[0] in symbols and len(t)-1==data['signature'][t[0]]
        return format(cap+symbols.index(t[0]),f'0{width}b')+''.join(tbits(a,names) for a in t[1:])
    header=format(len(symbols),'08b')+''.join(format(a,'03b') for a in arities)+format(cap,'08b')
    chunks=['1'+tbits(a,sorted(variables(a)|variables(b)))+tbits(b,sorted(variables(a)|variables(b))) for a,b in data['equations']]
    end=tbits(data['start'],[])+tbits(data['target'],[])
    return header+''.join(chunks)+'0'+end,header,chunks,end

def parse(bits):
    index=0
    def number(n):
        nonlocal index
        if index+n>len(bits):raise ValueError('truncated')
        text=bits[index:index+n];index+=n
        if any(c not in '01' for c in text):raise ValueError('nonbinary')
        return int(text,2)
    k=number(8);ars=[number(3) for _ in range(k)];v=number(8);w=(k+v-1).bit_length()
    if k+v<2:raise ValueError('unsupported degenerate alphabet')
    def term():
        opcode=number(w)
        if opcode<v:return ('var',opcode)
        sym=opcode-v
        if sym>=k:raise ValueError('unknown opcode')
        return (sym,tuple(term() for _ in range(ars[sym])))
    eqs=[]
    while number(1):eqs.append((term(),term()))
    start=term();target=term()
    if index!=len(bits):raise ValueError('trailing bits')
    def ground(t):return t[0]!='var' and all(ground(a) for a in t[1])
    if not ground(start) or not ground(target):raise ValueError('nonground endpoint')
    return ars,v,eqs,start,target

ob,oh,oc,oe=emit(old);nb,nh,nc,ne=emit(new)
assert len(ob)==946 and len(nb)==921 and len(oh)==len(nh)==55 and len(oe)==len(ne)==16
assert nb==(ROOT/'packet921.bits').read_text().strip()
assert hashlib.sha256(ob.encode()).hexdigest()==old['metrics']['bits_sha256']
assert hashlib.sha256(nb.encode()).hexdigest()==new['metrics']['bits_sha256']
assert oh==nh and oe==ne and oc[:1]+oc[2:]==nc
p0=parse(ob);p1=parse(nb)
assert p0[:2]==p1[:2] and p0[3:]==p1[3:] and p0[2][:1]+p0[2][2:]==p1[2]
for bits in (ob,nb):
    for i in range(len(bits)):
        try:parse(bits[:i])
        except ValueError:pass
        else:raise AssertionError(('accepted truncation',len(bits),i))
    for bad in (bits+'0',bits+'1',bits[:-1]+'x'):
        try:parse(bad)
        except ValueError:pass
        else:raise AssertionError('accepted malformed packet')
start=len(oh)+len(oc[0]);stop=start+len(oc[1]);assert ob[:start]+ob[stop:]==nb
result={'status':'INDEPENDENT_EXACT_CODEC_AND_DELETION_PASS','baseline_bits':len(ob),'reduced_bits':len(nb),'deleted_zero_based_bit_interval':[start,stop],'deleted_bits':oc[1],'deleted_term_nodes':sum(nodes(t) for t in old['equations'][1]),'saving_bits':len(oc[1]),'header_bits':len(nh),'equation_bits':len(nb)-len(nh)-len(ne),'endpoint_bits':len(ne),'equations':len(new['equations']),'both_side_tree_nodes':sum(nodes(t) for eq in new['equations'] for t in eq),'signature_symbols':len(new['signature']),'variable_capacity':p1[1],'signature_and_endpoints_unchanged':True,'strict_truncations_tested':len(ob)+len(nb),'malformed_packets_tested':6,'old_bits_sha256':hashlib.sha256(ob.encode()).hexdigest(),'new_bits_sha256':hashlib.sha256(nb.encode()).hexdigest(),'primary_Sh1_source':'https://www.cs.unm.edu/~mccune/papers/basax/v12.pdf','source_statement':'McCune et al. (2002), Short Single Axioms for Boolean Algebra, Theorem 2, section 3. Identity (x | ((y | x) | x)) | (y | (z | x)) = y.'}
(HERE/'packet921_independent_review.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
