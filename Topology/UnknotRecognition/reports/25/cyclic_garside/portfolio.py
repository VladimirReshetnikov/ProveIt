"""Cheap certified whole-word normalization before optional cyclic kernels.

The chosen result need not equal a radius-r kernel optimum: a whole-word normal
form can use a longer target. It is at least as short as the selected kernel
unless the universal lower bound already certifies a shorter result. Every
candidate is checked against the original input, avoiding composite provenance.
"""
from dataclasses import asdict
from .normalform import normal_form, expand_state, validate, Counters, IDENTITY
from .kernel import input_digest, length_lower_bound, compress
from .radius import compress_radius
from .verify import verify
from .verify_radius import verify_radius


def normal_form_candidate(b, word, *, budget=None):
    word = validate(b, word)
    n, lower = len(word), length_lower_bound(b, word)
    counts = Counters()
    target = word
    records = []
    if lower < n:
        state, _ = normal_form(b, word, counters=counts, budget=budget)
        half_length = b*(b-1)//2
        length = abs(state[0])*half_length
        for p in state[1]:
            length += sum(p[i] > p[j] for i in range(b) for j in range(i+1,b))
        if length < n:
            target = expand_state(b, state)
            assert len(target) == length
            residual = word + tuple(-a for a in reversed(target))
            identity, proof = normal_form(b, residual, trace=True, counters=counts, budget=budget)
            assert identity == IDENTITY
            records = [dict(start=0,end=n,target=list(target),proof=proof)]
    cert = dict(schema='cyclic-garside-kernel-v2',strands=b,input_digest=input_digest(b,word),
                mode='linear',rotation=0,output=list(target),replacements=records,
                target_radius=max(1,len(target)))
    checked = verify_radius(b,word,cert)
    assert checked == target
    stats = asdict(counts)
    stats.pop("prefix_height", None)  # no doubled-prefix table was prepared
    stats.update(stage='whole-normal-form',input_length=n,output_length=len(target),
                 lower_bound=lower,lower_bound_attained=len(target)==lower)
    return dict(word=list(target),certificate=cert,stats=stats)


def preprocess(b, word, *, radius=1, max_targets=100000, budget=None):
    """Choose a verified candidate; never return a knot verdict.

    Operation limits propagate, so the caller can fall back to its original
    input. Optimizers always read the original source, not each other's output.
    """
    if type(radius) is not int or radius < 1:
        raise ValueError('radius must be a positive integer')
    word = validate(b,word)
    cheap = normal_form_candidate(b,word,budget=budget)
    if cheap['stats']['lower_bound_attained']:
        cheap['stats']['portfolio_shortcut']=True
        return cheap
    if radius == 1:
        result=compress(b,word,budget=budget)
        verify(b,word,result['certificate'])
    else:
        result=compress_radius(b,word,radius=radius,max_targets=max_targets,budget=budget)
        verify_radius(b,word,result['certificate'])
    result['stats']['stage']='cyclic-kernel'
    answer=cheap if len(cheap['word'])<=len(result['word']) else result
    answer['stats']['portfolio_shortcut']=False
    answer['stats']['portfolio_candidates']={'normal_form_length':len(cheap['word']),
                                            'kernel_length':len(result['word']),
                                            'kernel_radius':radius}
    return answer
