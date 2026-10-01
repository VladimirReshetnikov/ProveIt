"""Literal universal word substrate; exact obstructions to two unpaid interfaces.

This is a finite presentation/word checker, not a Diophantine compiler.
External dependency: Tseytin's primary section 7, Lemma 9, for the word map.
The group completions and word/loader-size claims are proved in this packet.
"""
import argparse
from collections import Counter
import hashlib
from itertools import permutations, product
import json
from pathlib import Path

ALPHABET='abcde'
C1=(('ac','ca'),('ad','da'),('bc','cb'),('bd','db'),
    ('eca','ce'),('edb','de'),('cca','ccae'))
C2=C1[:6]+(('cdca','cdcae'),('caaa','aaa'),('daaa','aaa'))
PRIMARY='https://arxiv.org/pdf/2401.11757'


def inverse(word):
    return tuple(-x for x in reversed(word))


def reduce_word(word):
    result=[]
    for x in word:
        assert type(x) is int and x
        if result and result[-1]==-x:result.pop()
        else:result.append(x)
    return tuple(result)


def cyclic_core(word):
    word=reduce_word(word);conjugator=[]
    while len(word)>=2 and word[0]==-word[-1]:
        conjugator.append(word[0]);word=word[1:-1]
    return tuple(conjugator),word


def relators(relations):
    code=lambda w:tuple(ALPHABET.index(a)+1 for a in w)
    return [reduce_word(code(u)+inverse(code(v))) for u,v in relations]


def completion_certificate(relations,order):
    """Every pivot is a conjugate of one generator/inverse after prior erasures.

    Replacing such a relator by the generator, then substituting 1 in every
    other relator, is an exact Tietze elimination.  No search cutoff proves it.
    """
    current=relators(relations);steps=[]
    for letter in order:
        generator=ALPHABET.index(letter)+1
        pivots=[(i,*cyclic_core(w)) for i,w in enumerate(current)
                if cyclic_core(w)[1] in ((generator,),(-generator,))]
        assert pivots
        index,conjugator,pivot=pivots[0]
        assert reduce_word(conjugator+pivot+inverse(conjugator))==current[index]
        steps.append(dict(eliminate=letter,pivot_relator=index,
            before=current[index],conjugator=conjugator,cyclic_pivot=pivot))
        current=[reduce_word(x for x in w if abs(x)!=generator) for w in current]
    assert not any(current)
    return dict(steps=steps,free_generators=''.join(a for a in ALPHABET if a not in order),
                remaining_relators=current)


def neighbors(word,relations):
    result=set()
    for u,v in relations:
      for before,after in ((u,v),(v,u)):
        for i in range(len(word)-len(before)+1):
            if word[i:i+len(before)]==before:
                result.add(word[:i]+after+word[i+len(before):])
    return result


def perm_mul(a,b):
    return tuple(a[b[i]] for i in range(3))


def eval_perm(word,images):
    value=(0,1,2)
    for letter in word:value=perm_mul(value,images[letter])
    return value


def finite_group_audit():
    counts=Counter();elements=tuple(permutations(range(3)));identity=(0,1,2)
    for values in product(elements,repeat=5):
        images=dict(zip(ALPHABET,values))
        for name,relations in (('C1',C1),('C2',C2)):
            satisfies=all(eval_perm(u,images)==eval_perm(v,images) for u,v in relations)
            predicted=all(images[a]==identity for a in ('abe' if name=='C1' else ALPHABET))
            assert satisfies==predicted
            counts[name+'_S3_assignments']+=1
            counts[name+'_S3_solutions']+=satisfies
    return dict(counts)


def code_for_group(rank):
    assert type(rank) is int and rank>=2
    order=[1,2,-1,-2]+[x for i in range(3,rank+1) for x in (i,-i)]
    # alpha is the erasable presentation letter; beta is the fresh separator.
    return dict(zip(order,range(2,2+len(order))))|{'alpha':1,'beta':0}


def phi(word,code):
    return ''.join('a'+'b'*code[a] for a in word)+'a'


def decode_phi(word,code):
    assert word and word[0]=='a' and word[-1]=='a' and set(word)<=set('ab')
    inverse_code={v:k for k,v in code.items()};assert len(inverse_code)==len(code)
    return tuple(inverse_code[len(block)] for block in word[:-1].split('a')[1:])


def group_to_fixed_target(rank,group_relators,word):
    """Effective primary §3(11), §7 Lemma9 word map into literal C2.

    The mathematical iff relies on the cited primary theorem.  The checker
    checks the construction and local word identities, not undecidability.
    Group inputs use signed generators 1..rank; 1 and 2 are distinguished.
    """
    assert type(rank) is int and rank>=2
    valid=lambda w:all(type(x) is int and 1<=abs(x)<=rank for x in w)
    assert valid(word) and all(valid(r) for r in group_relators)
    # A group as a special monoid: each relator and both inverse cancellations.
    special=[tuple(r) for r in group_relators]
    special += [(i,-i) for i in range(1,rank+1)]+[(-i,i) for i in range(1,rank+1)]
    code=code_for_group(rank)
    # K0 is empty. alpha K0 alpha K1 alpha ... Km alpha.
    program=('alpha','alpha')
    for r in special:program+=r+('alpha',)
    S=phi(program,code).translate(str.maketrans('ab','cd'))
    output=S+phi(('beta',)+tuple(word)+('beta',),code)
    return dict(program_word=S,query_word=output,target='aaa',code=code,
                special_relators=special)


def commutator_input(x):
    assert type(x) is int and x>0
    a_x=(-2,)*x+(1,)+(2,)*x
    return reduce_word(a_x+(1,)+inverse(a_x)+(-1,))


def base8(word):
    result=0
    for letter in word:result=8*result+(ALPHABET.index(letter)+1)
    return result


def word_audit():
    counts=Counter();examples=[]
    for relations in (C1,C2):
        for word in ('a','aa','b','bb','e'):
            assert not neighbors(word,relations)
            counts['isolated_word_checks']+=1
    # Actual accepted C2 words, with a displayed sequence of legal reductions.
    for size in range(9):
      for prefix in product('cd',repeat=size):
        word=''.join(prefix)+'aaa'
        for _ in prefix:
            following=word[:-4]+word[-3:]
            assert following in neighbors(word,C2)
            word=following;counts['literal_C2_derivation_steps']+=1
        assert word=='aaa';counts['literal_C2_accepted_words']+=1
    for rank in (2,3,5):
      for rs in ((),((1,1),),((1,2,-1,-2),)):
        for x in range(1,33):
            r=commutator_input(x);assert len(r)==4*x+4
            result=group_to_fixed_target(rank,rs,r);S=result['program_word']
            tail=result['query_word'][len(S):]
            assert decode_phi(tail,result['code'])==('beta',)+r+('beta',)
            assert len(tail)==20*x+19 and set(S)<=set('cd')
            number=base8(result['query_word'])
            # These comparisons verify each finite fixture, not the asymptotic theorem.
            length=len(S)+20*x+19
            assert 8**(length-1)<=number<8**length
            assert number.bit_length() in (3*length-2,3*length-1,3*length)
            counts['group_input_code_and_exact_size_checks']+=1
            if rank==2 and not rs and x<=2:
                examples.append(dict(x=x,program_word=S,query_word=result['query_word'],
                    target='aaa',query_length=length,encoded_integer_bits=number.bit_length()))
    return dict(counts),examples


def signed_normal_form_audit():
    counts=Counter()
    for size in range(5):
      for word in product(tuple(range(1,6))+tuple(range(-5,0)),repeat=size):
        c1=reduce_word(x for x in word if abs(x) in (3,4))
        normalized=reduce_word(word)
        assert c1==reduce_word(x for x in normalized if abs(x) in (3,4))
        assert not tuple(x for x in word if abs(x) not in (1,2,3,4,5))
        counts['signed_word_quotient_normalizations']+=1
    return dict(counts)


def verify():
    assert len(C1)==7 and sum(len(u)+len(v) for u,v in C1)==33
    assert len(C2)==9 and sum(len(u)+len(v) for u,v in C2)==49
    certificates={name:completion_certificate(relations,order)
        for name,relations,order in (('C1',C1,'eab'),('C2',C2,'eabcd'))}
    assert certificates['C1']['free_generators']=='cd'
    assert certificates['C2']['free_generators']==''
    words,examples=word_audit()
    return dict(status='PASS',scope='Exact group-completion and raw word-loader obstructions; no Diophantine or universal operation bound.',
        arithmetic_operation_bound=None,
        primary=dict(url=PRIMARY,locations=['translated original §1(1)-(2)',
            'translated original §3(11)','translated original §6 Lemma4/Theorem1',
            'translated original §7 Lemma9/Theorem2/Corollary1'],
            dependency='Uniform word reduction is imported; universal group completions are independently proved here.'),
        presentations={name:dict(generators=ALPHABET,relations=relations,
            defining_letter_occurrences=sum(len(a)+len(b) for a,b in relations))
            for name,relations in (('C1',C1),('C2',C2))},
        completion_certificates=certificates,checks=finite_group_audit()|words|signed_normal_form_audit(),
        exact_code_examples=examples,loader_length='|S|+20*x+19 for the chosen distinguished-generator code',
        source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--write',action='store_true');args=parser.parse_args()
    result=verify();path=Path(__file__).with_suffix('.json')
    canonical=json.loads(json.dumps(result))
    if args.write:path.write_text(json.dumps(canonical,indent=2)+'\n')
    else:assert canonical==json.loads(path.read_text()),'receipt mismatch'
    print(json.dumps(dict(status='PASS',checks=result['checks'],receipt=str(path))))
