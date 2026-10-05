#!/usr/bin/env python3
"""Explicit row/subset bijection, empty-row repair and three separate fibers.

Includes exact nontrivial Markov distributions, doubled seeds and fresh-record
padding. Bounded computation checks implementations; no numerical fit is proof.
"""
from __future__ import annotations
import argparse
from collections import Counter
from decimal import Decimal, localcontext, ROUND_FLOOR, ROUND_CEILING
from fractions import Fraction
import hashlib
from math import comb
from common import REPORT_NUMBER, emit, integer, integer_receipt, new_file_path, require
from exact_counts import checked_word, fast_avoidance, is_ascent, literal_avoidance
from upper_bound import table_term

MAX_ROWS = 400
MAX_CELLS = 100_000
MAX_TOTAL = 10_000
MAX_WORD = 20_000
MAX_ENUM_CELLS = 36
MAX_ENUM_TOTAL = 8
MAX_ENUM_ARRAYS = 20_000
MAX_DP_ROWS = 16
MAX_DP_TOTAL = 128


def bounded_row(row, positive=False):
    require(isinstance(positive,bool), 'positive selector must be Boolean')
    require(isinstance(row,(tuple,list)) and 1 <= len(row) <= MAX_ROWS, 'row width outside cutoff')
    result = tuple(integer(x,0,MAX_TOTAL,'cell') for x in row)
    require(sum(result) <= MAX_TOTAL, 'row total exceeds cutoff')
    if positive:
        require(sum(result) >= 1, 'positive row required')
    return result


def rows_checked(rows, positive=False):
    require(isinstance(positive,bool), 'positive selector must be Boolean')
    require(isinstance(rows,(tuple,list)) and 1 <= len(rows) <= MAX_ROWS, 'row count outside cutoff')
    r = len(rows)
    require(r*(r+1)//2 <= MAX_CELLS, 'triangular cell budget exceeded')
    result = tuple(bounded_row(row,positive) for row in rows)
    require(all(len(row) == r-j for j,row in enumerate(result)), 'row widths must be r,...,1')
    require(sum(map(sum,result)) <= MAX_TOTAL, 'array total exceeds cutoff')
    return result


def stars_to_ranks(row):
    """Stars are selected zero-based ranks; the omitted positions are bars.

    For a=(a_0,...,a_{w-1}), row i contributes consecutive star positions
    sum(a_h for h<i)+i through that value+a_i-1. Universe size ell+w-1.
    """
    row = bounded_row(row)
    ranks,position = [],0
    for amount in row:
        ranks.extend(range(position,position+amount))
        position += amount+1
    return tuple(ranks)


def ranks_to_stars(ranks,width):
    """Inverse map: count selected positions before/between/after missing bars."""
    integer(width,1,MAX_ROWS,'row width')
    require(isinstance(ranks,(tuple,list)) and len(ranks) <= MAX_TOTAL, 'rank list outside cutoff')
    universe = len(ranks)+width-1
    for rank in ranks:
        integer(rank,0,universe-1,'star rank')
    require(all(x<y for x,y in zip(ranks,ranks[1:])), 'star ranks must strictly increase')
    selected = set(ranks)
    row,count = [],0
    for position in range(universe):
        if position in selected:
            count += 1
        else:
            row.append(count)
            count = 0
    row.append(count)
    require(len(row) == width, 'wrong bar count')
    return tuple(row)


def weak_compositions(total,cells):
    integer(total,0,MAX_ENUM_TOTAL,'enumeration total')
    integer(cells,1,MAX_ENUM_CELLS,'enumeration cell count')
    require(comb(cells+total-1,total) <= MAX_ENUM_ARRAYS, 'array enumeration budget exceeded')
    def generate(q,k):
        if k == 1:
            yield (q,)
        else:
            for first in range(q+1):
                for tail in generate(q-first,k-1):
                    yield (first,)+tail
    return generate(total,cells)


def group_cells(cells,r):
    integer(r,1,MAX_ROWS,'row count')
    require(isinstance(cells,(tuple,list)) and len(cells) == r*(r+1)//2 <= MAX_CELLS,
            'incorrect or excessive triangular cell count')
    rows,position = [],0
    for width in range(r,0,-1):
        rows.append(tuple(cells[position:position+width]))
        position += width
    return rows_checked(rows)


def repair(rows):
    rows = rows_checked(rows)
    result = tuple(((1,)+row[1:]) if sum(row) == 0 else row for row in rows)
    return rows_checked(result,positive=True)


def positive_word(rows):
    rows = rows_checked(rows,positive=True)
    r = len(rows)
    suffix,used,lengths = [],set(),[]
    previous_ceiling = -1
    for j,row in enumerate(rows,1):
        ell = sum(row)
        lengths.append(ell)
        A0 = r+len(suffix)-j
        ceiling = A0+ell-1
        require(ceiling >= previous_ceiling, 'positive rows must give nondecreasing ceilings')
        require(all(x <= ceiling for x in used), 'old suffix label outside current interval')
        candidates = tuple(x for x in range(ceiling+1) if x not in used)
        require(len(candidates) == r+ell-j, 'positive-row candidate count fails')
        ranks = stars_to_ranks(row)
        require(ranks_to_stars(ranks,len(row)) == row, 'stars-and-bars inverse fails')
        block = tuple(candidates[x] for x in ranks)
        require(all(x <= A0+t-1 for t,x in enumerate(block,1)), 'order-statistic legality bound fails')
        suffix.extend(block)
        used.update(block)
        previous_ceiling = ceiling
    require(len(used) == len(suffix), 'suffix labels must all differ')
    word = tuple(range(r))+tuple(suffix)
    require(is_ascent(word), 'constructed word violates ascent legality')
    flags = fast_avoidance(word)
    require(flags[0] and flags[1], 'constructed word contains 000 or 100')
    return word,tuple(lengths)


def recover_rows(word,lengths):
    word = checked_word(word,MAX_WORD)
    require(isinstance(lengths,(tuple,list)) and 1 <= len(lengths) <= MAX_ROWS, 'bounded lengths required')
    lengths = tuple(integer(x,1,MAX_TOTAL,'block length') for x in lengths)
    r = len(lengths)
    require(len(word) == r+sum(lengths) and sum(lengths) <= MAX_TOTAL, 'word/length total mismatch')
    require(word[:r] == tuple(range(r)), 'incorrect seed')
    require(is_ascent(word), 'illegal input ascent sequence')
    rows,used = [],set()
    position = r
    for j,ell in enumerate(lengths,1):
        ceiling = position+ell-j-1
        candidates = tuple(x for x in range(ceiling+1) if x not in used)
        require(len(candidates) == r+ell-j, 'decoder candidate count fails')
        index = {x:i for i,x in enumerate(candidates)}
        block = word[position:position+ell]
        require(all(x<y for x,y in zip(block,block[1:])), 'decoded block not strictly increasing')
        require(all(x in index for x in block), 'decoded value absent from candidate pool')
        ranks = tuple(index[x] for x in block)
        rows.append(ranks_to_stars(ranks,r-j+1))
        used.update(block)
        position += ell
    result = rows_checked(rows,positive=True)
    require(positive_word(result) == (word,lengths), 'decorated-word inverse fails')
    return result


def doubled_seed(word,r):
    word = checked_word(word,MAX_WORD)
    integer(r,1,MAX_ROWS,'seed size')
    require(len(word)>r and word[:r] == tuple(range(r)), 'positive suffix and correct seed required')
    require(is_ascent(word), 'input word must be an ascent sequence')
    suffix = word[r:]
    require(len(suffix) == len(set(suffix)), 'suffix must be distinct')
    require(suffix[0] <= r-1, 'first suffix entry violates construction condition')
    result = tuple(range(r))*2+tuple(x+r for x in suffix)
    require(len(result) <= MAX_WORD, 'doubled word exceeds cutoff')
    require(is_ascent(result) and all(fast_avoidance(result)), 'doubled-seed common construction fails')
    return result


def undo_doubled_seed(word,r):
    word = checked_word(word,MAX_WORD)
    integer(r,1,MAX_ROWS,'seed size')
    require(len(word)>2*r and word[:2*r] == tuple(range(r))*2, 'incorrect doubled seed')
    require(all(x>=r for x in word[2*r:]), 'doubled suffix label below r')
    result = tuple(range(r))+tuple(x-r for x in word[2*r:])
    require(doubled_seed(result,r) == word, 'doubled-seed inverse fails')
    return result


def pad_records(word,N):
    word = checked_word(word,MAX_WORD)
    integer(N,0,MAX_WORD,'padding target')
    require(N >= len(word), 'padding cannot shorten a word')
    require(is_ascent(word), 'padding input must be legal')
    maximum = max(word,default=-1)
    result = word+tuple(range(maximum+1,maximum+1+N-len(word)))
    require(is_ascent(result), 'record padding legality fails')
    flags,after = fast_avoidance(word),fast_avoidance(result)
    require(all(not before or later for before,later in zip(flags,after)), 'padding creates a forbidden pattern')
    return result


def repair_budget(r,q):
    integer(r,1,10_000,'dimension')
    integer(q,1,10_000,'original total')
    M = r*(r+1)//2
    return (2*(M+q)+q-1)//q


def empty_distribution(r,q):
    """Exact distribution over q-unit triangular arrays, without enumerating them."""
    integer(r,1,MAX_DP_ROWS,'DP dimension')
    integer(q,1,MAX_DP_TOTAL,'DP total')
    # A positive row of width k and sum s has binom(k+s-1,s) choices.
    dp = {(0,0):1}
    for k in range(r,0,-1):
        weights = [comb(k+s-1,s) for s in range(q+1)]
        next_dp = {}
        for (spent,empty),count in dp.items():
            key = (spent,empty+1)
            next_dp[key] = next_dp.get(key,0)+count
            for s in range(1,q-spent+1):
                key = (spent+s,empty)
                next_dp[key] = next_dp.get(key,0)+count*weights[s]
        dp = next_dp
    return tuple(dp.get((q,e),0) for e in range(r+1))


def verify_markov():
    receipts = []
    for r,q in ((1,3),(8,30),(12,90),(16,128)):
        M = r*(r+1)//2
        T = comb(M+q-1,q)
        Q = repair_budget(r,q)
        distribution = empty_distribution(r,q)
        require(sum(distribution) == T, 'empty-row histogram total mismatch')
        total_empty = sum(e*count for e,count in enumerate(distribution))
        marginal = sum(comb(M-k+q-1,q) if M-k else 0 for k in range(1,r+1))
        require(total_empty == marginal, 'DP and exact marginal expectations disagree')
        expectation = Fraction(total_empty,T)
        require(expectation <= Fraction(M+q-1,q), 'empty expectation bound fails')
        eligible = sum(distribution[:min(Q,r)+1])
        require(2*eligible >= T, 'Markov retained-half conclusion fails')
        if r>1:
            require(Q<r and 0<T-eligible<T, 'Markov example must have genuine rejection and Q<r')
        receipts.append({'r':r,'q':q,'M':M,'Q':Q,'nontrivial_cutoff':Q<r,
                         'total':integer_receipt(T),'eligible':integer_receipt(eligible),
                         'rejected':integer_receipt(T-eligible),
                         'empty_expectation':str(expectation),
                         'eligible_fraction':str(Fraction(eligible,T)),
                         'empty_row_histogram':[integer_receipt(x) for x in distribution]})
    return receipts


def verify_exhaustive(max_n=9):
    integer(max_n,2,9,'exhaustive cutoff')
    receipts,total = [],0
    digest = hashlib.sha256()
    for n in range(2,max_n+1):
        for r in range(1,n):
            q,M = n-r,r*(r+1)//2
            T = table_term(n,r)
            Q = repair_budget(r,q)
            originals,eligible,total_empty = 0,0,0
            repaired = Counter()
            for cells in weak_compositions(q,M):
                originals += 1
                rows = group_cells(cells,r)
                e = sum(sum(row)==0 for row in rows)
                total_empty += e
                if e <= Q:
                    eligible += 1
                    fixed = repair(rows)
                    require(sum(map(sum,fixed)) == q+e, 'repair total mismatch')
                    repaired[fixed] += 1
            require(originals == T, 'weak-composition count mismatch')
            require(Fraction(total_empty,T) <= Fraction(M+q-1,q), 'expectation bound fails')
            require(2*eligible >= T, 'retained-half bound fails')
            require(max(repaired.values()) <= 2**r, 'repair fiber exceeds 2^r')
            words,common_words = Counter(),Counter()
            decorated = set()
            for rows in sorted(repaired):
                word,lengths = positive_word(rows)
                require(recover_rows(word,lengths) == rows, 'positive-row inverse mismatch')
                signature = (word,lengths)
                require(signature not in decorated, 'decorated map collision')
                decorated.add(signature)
                common = doubled_seed(word,r)
                require(undo_doubled_seed(common,r) == word, 'doubled map inverse mismatch')
                require(all(literal_avoidance(common)), 'literal common avoidance fails')
                literal = literal_avoidance(word)
                require(literal[0] and literal[1], 'literal 000/100 avoidance fails')
                require(n <= len(word) <= n+Q, 'repaired length outside budget')
                words[word] += 1
                common_words[common] += 1
                digest.update((repr((n,r,rows,word,common))+'\n').encode('ascii'))
            max_composition = 0
            for word,fiber in words.items():
                p = len(word)-r
                require(fiber <= comb(p-1,r-1), 'composition fiber exceeds positive-composition count')
                max_composition = max(max_composition,fiber)
            padded,padded_common = Counter(),Counter()
            for word in words:
                padded[pad_records(word,n+Q)] += 1
            for word in common_words:
                padded_common[pad_records(word,n+r+Q)] += 1
            # This count is over DISTINCT pre-padding words, separate from row fibers.
            require(max(padded.values()) <= Q+1, 'record-padding fiber exceeds Q+1')
            require(max(padded_common.values()) <= Q+1, 'common padding fiber exceeds Q+1')
            denominator = 2**(r+1)*(Q+1)*comb(n+Q,r)
            require(len(padded)*denominator >= T, 'finite 000/100 lower comparison fails')
            require(len(padded_common)*denominator >= T, 'finite common lower comparison fails')
            total += originals
            receipts.append({'n':n,'r':r,'q':q,'T':T,'Q':Q,'eligible_arrays':eligible,
                             'empty_expectation':str(Fraction(total_empty,T)),
                             'repaired_arrays':len(repaired),'distinct_words_000_100':len(words),
                             'distinct_common_words':len(common_words),
                             'max_repair_fiber':max(repaired.values()),
                             'max_composition_fiber':max_composition,
                             'max_padding_fiber':max(padded.values()),
                             'max_common_padding_fiber':max(padded_common.values()),
                             'padded_words_000_100':len(padded),'padded_common_words':len(padded_common),
                             'lower_denominator':denominator})
    return {'original_arrays_checked':total,'mapping_sha256':digest.hexdigest(),'rows':receipts}


def all_length_parameters(N,common=False):
    integer(N,100,10_000,'all-length target')
    require(isinstance(common,bool), 'common selector must be Boolean')
    with localcontext() as context:
        context.prec = 60
        logN = Decimal(N).ln()
        if common:
            r = int((Decimal(N)/logN).to_integral_value(rounding=ROUND_FLOOR))
            slack = int((Decimal(4*N)/(logN*logN)).to_integral_value(rounding=ROUND_CEILING))
            n = N-r-slack
        else:
            slack = int((Decimal(8*N)/(logN*logN)).to_integral_value(rounding=ROUND_CEILING))
            n = N-slack
            r = int((Decimal(2*n)/Decimal(n).ln()).to_integral_value(rounding=ROUND_FLOOR))
    q = n-r
    require(1 <= r<n, 'target too small for selected dimension')
    Q = repair_budget(r,q)
    final = n+Q+(r if common else 0)
    require(final<=N, 'selected finite target has insufficient slack')
    T = table_term(n,r)
    denominator = 2**(r+1)*(Q+1)*comb(n+Q,r)
    result = {'target':N,'class':'common' if common else '000_100',
              'n':n,'r':r,'q':q,'M':r*(r+1)//2,'Q':Q,
              'repair_and_seed_target':final,'extra_padding':N-final,
              'triangular_count':integer_receipt(T),'lower_denominator':integer_receipt(denominator)}
    if N<=1000:
        # Give Q empty rows where possible; remaining rows positive.
        t = min(Q,r-1)
        nonempty = r-t
        require(q>=nonempty, 'sample cannot fill intended positive rows')
        rows = tuple(((q-nonempty+1 if j==0 else (1 if j<nonempty else 0)),)+(0,)*(r-j-1)
                     for j in range(r))
        fixed = repair(rows)
        word,lengths = positive_word(fixed)
        require(recover_rows(word,lengths) == fixed, 'all-length sample inverse fails')
        if common:
            word = doubled_seed(word,r)
        padded = pad_records(word,N)
        flags = fast_avoidance(padded)
        require(all(flags) if common else flags[0] and flags[1], 'all-length sample avoidance fails')
        result.update({'sample_original_empty_rows':t,'sample_pre_padding_length':len(word),
                       'sample_final_length':len(padded),
                       'sample_word_sha256':hashlib.sha256(repr(padded).encode('ascii')).hexdigest()})
    return result


def verify(max_n=9):
    exhaustive = verify_exhaustive(max_n)
    # Exhaustively check BOTH directions of the row/subset bijection.
    from itertools import combinations
    bijections = 0
    for width in range(1,7):
        for total in range(0,7):
            for row in weak_compositions(total,width):
                ranks = stars_to_ranks(row)
                require(ranks_to_stars(ranks,width) == row, 'row/subset round trip fails')
                bijections += 1
            for ranks in combinations(range(total+width-1),total):
                require(stars_to_ranks(ranks_to_stars(ranks,width)) == ranks, 'subset/row round trip fails')
                bijections += 1
    witness_rows = ((0,1),(2,))
    witness,lengths = positive_word(witness_rows)
    require(witness == (0,1,1,0,2) and not literal_avoidance(witness)[2], '110 obstruction witness fails')
    doubled = doubled_seed(witness,2)
    return {'status':'PASS','report_number':REPORT_NUMBER,
            'stars_and_bars_round_trips':bijections,'exhaustive':exhaustive,
            'nontrivial_markov_checks':verify_markov(),
            'all_length_examples':[all_length_parameters(N,c) for c in (False,True) for N in (100,250,1000,10_000)],
            'witness':{'rows':witness_rows,'word':witness,'lengths':lengths,'doubled_common_word':doubled},
            'scope':'Exact bounded tests and finite parameter examples. No numerical extrapolation or fitting establishes an asymptotic claim.'}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--max-n',type=int,default=9)
    parser.add_argument('--output')
    args = parser.parse_args()
    if args.output is not None:
        new_file_path(args.output)
    emit(verify(args.max_n),args.output)


if __name__ == '__main__':
    try:
        main()
    except (ValueError,RuntimeError,OSError,ArithmeticError) as exc:
        raise SystemExit(str(exc))
