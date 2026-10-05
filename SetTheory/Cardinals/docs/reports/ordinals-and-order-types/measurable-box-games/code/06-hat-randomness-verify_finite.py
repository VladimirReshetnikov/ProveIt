#!/usr/bin/env python3
"""Exact finite checks for the hat-randomness article (Python 3.10+).

Standard library only; no Monte Carlo estimates. All hats and all effective
seed outcomes of each displayed finite strategy are enumerated, with integer
weights for biased activation masks. These finite checks do not prove the
infinite scheduling, almost-sure, martingale, or limiting assertions.

Run: python3 verify_finite.py [--output /path/to/results.json]
"""

import argparse
import json
from collections import Counter
from fractions import Fraction as F
from math import comb
from pathlib import Path


CHECKS = 0


def require(condition, message):
    global CHECKS
    CHECKS += 1
    if not condition:
        raise AssertionError(message)


def bits(mask, n):
    return tuple((mask >> j) & 1 for j in range(n))


def weighted_masks(n, probability):
    a, d = probability.numerator, probability.denominator
    outcomes = [(mask, a**mask.bit_count() * (d-a)**(n-mask.bit_count()))
                for mask in range(1 << n)]
    require(sum(w for _, w in outcomes) == d**n, "seed weights")
    return outcomes, d**n


class Moments:
    def __init__(self, n):
        self.n = n
        self.mass = self.states = self.first = self.second = 0
        self.queries = [0] * n
        self.zeros = [0] * n
        self.law = Counter()

    def add(self, hats, guesses, queries, weight):
        require(len(guesses) == len(queries) == self.n, "dimensions")
        signs = tuple(1 if x == g else -1 for x, g in zip(hats, guesses))
        score = sum(signs)
        self.mass += weight
        self.states += 1
        self.first += weight * score
        self.second += weight * score * score
        self.law[score] += weight
        for i, q in enumerate(queries):
            self.queries[i] += weight * q
            self.zeros[i] += weight * (q == 0)
        return signs

    def result(self, name, private, expected_mass):
        require(self.mass == expected_mass, name + ": probability mass")
        require(self.first == 0, name + ": centered score")
        q, z = F(sum(self.queries), self.mass), F(sum(self.zeros), self.mass)
        variance = F(self.second, self.mass)
        minus = F(sum(v for k, v in self.law.items() if k < 0), self.mass)
        plus = F(sum(v for k, v in self.law.items() if k > 0), self.mass)
        require(self.n-q <= variance <= self.n+q, name + ": variance sandwich")
        bound = z*z / (12*self.n*(self.n+q))
        cost_bound = max(F(0), self.n-q)**2 / (12*self.n*(self.n+q))
        require(min(minus, plus) >= bound, name + ": zero-query sign bounds")
        require(min(minus, plus) >= cost_bound, name + ": cost sign bounds")
        out = {
            "name": name, "owners": self.n,
            "enumerated_hat_seed_states": self.states,
            "integer_probability_denominator": self.mass,
            "total_expected_queries": str(q),
            "expected_zero_query_players": str(z),
            "score_variance": str(variance),
            "negative_score_probability": str(minus),
            "positive_score_probability": str(plus),
            "general_zero_query_sign_lower_bound": str(bound),
            "cost_sign_lower_bound": str(cost_bound),
            "per_owner_expected_queries": [str(F(v, self.mass)) for v in self.queries],
            "score_law": {str(k): str(F(v, self.mass)) for k, v in sorted(self.law.items())},
        }
        if private:
            bound = z*z / (4*(3*z+1)*(self.n+q))
            require(min(minus, plus) >= bound, name + ": independent-private bounds")
            out["independent_private_sign_lower_bound"] = str(bound)
        return out


def observe(hats, owner):
    """Run the actual early-stopping S algorithm and return its transcript."""
    partner = owner + 1
    queried = [partner]
    if hats[partner]:
        return 1, queried
    for j in range(len(hats)):
        if j == owner or j == partner:
            continue
        queried.append(j)
        if hats[j]:
            return 0, queried
    return 1, queried


def block_data(m):
    n = 2*m
    rows, sums = [], [0]*m
    laws = [Counter() for _ in range(m)]
    conditional = [[0, 0] for _ in range(m)]
    for hatmask in range(1 << n):
        hats = bits(hatmask, n)
        base = tuple(hats[i+1] if i % 2 == 0 else 1-hats[i-1] for i in range(n))
        active, queries = [], []
        for j in range(m):
            owner = 2*j
            guess, transcript = observe(hats, owner)
            require(owner not in transcript, "owner not inspected")
            require(len(set(transcript)) == len(transcript), "fresh queries")
            expected = (hats[owner+1] if any(hats[k] for k in range(n) if k != owner)
                        else 1)
            require(guess == expected, "operational and Boolean block rules")
            flipped = list(hats)
            flipped[owner] ^= 1
            require(observe(tuple(flipped), owner) == (guess, transcript),
                    "owner-flip invariance")
            active.append(guess)
            queries.append(len(transcript))
            sums[j] += len(transcript)
            laws[j][len(transcript)] += 1
            conditional[j][hats[owner+1]] += len(transcript)
        rows.append((hats, base, tuple(active), tuple(queries)))
    active_mean = 2-F(1, 2**(2*m-2))
    black_mean = 3-F(2)**(3-2*m)
    for j in range(m):
        require(F(sums[j], 1 << n) == active_mean, "active S expected cost")
        require(F(conditional[j][0], 1 << (n-1)) == black_mean,
                "cost given black partner")
        require(F(conditional[j][1], 1 << (n-1)) == 1, "cost given white partner")
        for t in range(2*m+1):
            actual = F(sum(v for k, v in laws[j].items() if k > t), 1 << n)
            expected = F(1, 2**t) if t < 2*m-1 else F(0)
            require(actual == expected, "truncated geometric query tail")
    costs = {
        "active_S_mean": str(active_mean), "inactive_S_mean": "1", "T_mean": "1",
        "active_S_mean_given_black_partner": str(black_mean),
        "active_S_mean_given_white_partner": "1",
        "active_S_query_law": {str(k): str(F(v, 1 << n))
                               for k, v in sorted(laws[0].items())},
    }
    return rows, costs


def evaluate(row, activation):
    hats, base, active, costs = row
    guesses, queries = list(base), [1]*len(hats)
    for j in range(len(active)):
        if activation & (1 << j):
            guesses[2*j], queries[2*j] = active[j], costs[j]
    return guesses, queries


def verify_blocks():
    blocks, gates, cached = [], [], {}
    for m in range(1, 6):
        n = 2*m
        rows, conditional = block_data(m)
        cached[m] = rows
        for alpha in (F(1, 2), F(1, 4)):
            outcomes, denominator = weighted_masks(m, alpha)
            stats, gated, black_law = Moments(n), Moments(n), Counter()
            positive_mass = 0
            for row in rows:
                hats = row[0]
                for mask, weight in outcomes:
                    guesses, queries = evaluate(row, mask)
                    signs = stats.add(hats, guesses, queries, weight)
                    score = sum(signs)
                    pairs = tuple(signs[2*j]+signs[2*j+1] for j in range(m))
                    if not any(hats):
                        require(score == -2*mask.bit_count(), "all-black block law")
                        require(pairs == tuple(-2 if mask & (1 << j) else 0
                                               for j in range(m)), "all-black pair law")
                        black_law[score//2] += weight
                    elif sum(hats) == 1 and hats.index(1) % 2 == 0:
                        j = hats.index(1)//2
                        require(score == (2 if mask & (1 << j) else 0),
                                "singleton activated gain")
                        require(all(s >= 0 for s in pairs), "singleton pair law")
                    else:
                        require(score == 0 and all(s == 0 for s in pairs),
                                "neutral configuration law")
                    if any(hats):
                        require(all(s in (0, 2) for s in pairs), "nonbad pair monotonicity")
                        prefixes = [0]
                        for sign in signs:
                            prefixes.append(prefixes[-1]+sign)
                        require(max(abs(v-score) for v in prefixes) <= 2,
                                "nonbad prefixes within one surplus of endpoint")
                        if score == 0:
                            require(max(abs(v) for v in prefixes) <= 1,
                                    "neutral prefixes within one half")
                    positive_mass += weight*(score > 0)
                    # This is one public gate for the whole strategy; off with
                    # epsilon=alpha. It is not an independent gate at each player.
                    gated.add(hats, guesses, queries,
                              (alpha.denominator-alpha.numerator)*weight)
                gated.add(hats, [0]*n, [0]*n, alpha.numerator*denominator)
            name = "activated_block_m%d_alpha_%s" % (m, str(alpha).replace("/", "_"))
            result = stats.result(name, True, (1 << n)*denominator)
            result.update(pairs=m, alpha=str(alpha), conditional_query_means=conditional)
            positive = alpha*m/(4**m)
            require(F(positive_mass, stats.mass) == positive, "positive block probability")
            expected_s = 1+alpha*(1-F(1, 2**(2*m-2)))
            for i, total in enumerate(stats.queries):
                require(F(total, stats.mass) == (expected_s if i % 2 == 0 else 1),
                        "activated per-owner expected queries")
            for k in range(m+1):
                expected = comb(m, k)*alpha**k*(1-alpha)**(m-k)
                require(F(black_law[-k], denominator) == expected,
                        "negative binomial law conditional on all black")
            result["surplus_law_given_all_black"] = {
                str(k): str(F(v, denominator)) for k, v in sorted(black_law.items())}
            result["positive_block_probability_formula"] = str(positive)
            blocks.append(result)
            gate = gated.result("public_gate_"+name, False,
                                (1 << n)*denominator*alpha.denominator)
            s_cost, t_cost = (1-alpha)*expected_s, 1-alpha
            require(s_cost <= 1 and t_cost <= 1, "public gate unit expected budget")
            for i, total in enumerate(gated.queries):
                require(F(total, gated.mass) == (s_cost if i % 2 == 0 else t_cost),
                        "public gate exact per-owner expected costs")
            gate.update(epsilon=str(alpha), gate_on_probability=str(1-alpha),
                        expected_S_cost_formula=str(s_cost),
                        expected_T_cost_formula=str(t_cost))
            gates.append(gate)
    return blocks, gates, cached


def verify_representatives():
    results = []
    for n in range(1, 7):
        stats = Moments(n)
        for mask in range(1 << n):
            stats.add(bits(mask, n), [0]*n, [0]*n, 1)
        results.append(stats.result("constant_guesses_n%d" % n, True, 1 << n))
    for n in (2, 4, 6):
        stats = Moments(n)
        for mask in range(1 << n):
            hats = bits(mask, n)
            guesses = [hats[i+1] if i % 2 == 0 else 1-hats[i-1] for i in range(n)]
            stats.add(hats, guesses, [1]*n, 1)
        results.append(stats.result("neutral_pairs_n%d" % n, True, 1 << n))
        for alpha in (F(1, 2), F(1, 4)):
            outcomes, denominator = weighted_masks(n, alpha)
            stats = Moments(n)
            for mask in range(1 << n):
                hats = bits(mask, n)
                for seed, weight in outcomes:
                    guesses, queries = [], []
                    for i in range(n):
                        inspect = bool(seed & (1 << i))
                        guess = hats[i+1] if i % 2 == 0 else 1-hats[i-1]
                        guesses.append(guess if inspect else 0)
                        queries.append(int(inspect))
                    stats.add(hats, guesses, queries, weight)
            name = "privately_thinned_pairs_n%d_alpha_%s" % (
                n, str(alpha).replace("/", "_"))
            results.append(stats.result(name, True, (1 << n)*denominator))
    return results


def fwht(values):
    """Unnormalized integer Walsh transform."""
    out, width = list(values), 1
    while width < len(out):
        for start in range(0, len(out), 2*width):
            for j in range(start, start+width):
                a, b = out[j], out[j+width]
                out[j], out[j+width] = a+b, a-b
        width *= 2
    return out


def verify_fourier_profile(name, guesses, queries):
    """Check every scored prefix, including queries outside that prefix."""
    n, size = len(guesses), 1 << len(guesses)
    denominator = size*size
    transforms, influences = [], []
    for owner, table in enumerate(guesses):
        require(len(table) == size, name+": complete truth table")
        require(all(table[x] == table[x ^ (1 << owner)] for x in range(size)),
                name+": owner blindness")
        coefficients = fwht(table)
        require(all(coefficients[a] == 0 for a in range(size) if a & (1 << owner)),
                name+": forbidden Fourier support")
        require(sum(v*v for v in coefficients) == denominator, name+": Boolean Parseval")
        influence = sum(a.bit_count()*v*v for a, v in enumerate(coefficients))
        direct = sum(table[x] != table[x ^ (1 << j)]
                     for j in range(n) for x in range(size))*size
        require(influence == direct, name+": derivative and Fourier influence")
        require(influence <= sum(queries[owner])*size, name+": influence versus queries")
        transforms.append(coefficients)
        influences.append(influence)
    aggregate, energy, scores = [0]*size, [0]*(n+1), [0]*size
    influence = query_sum = 0
    records = []
    for count in range(1, n+1):
        owner = count-1
        for b in range(size):
            if b & (1 << owner):
                value = transforms[owner][b ^ (1 << owner)]
                aggregate[b] += value
                energy[b.bit_count()] += value*value
        for x in range(size):
            scores[x] += (-1 if x & (1 << owner) else 1)*guesses[owner][x]
        require(fwht(scores) == aggregate, name+": aggregate coefficient identity")
        require(aggregate[0] == 0, name+": centered aggregate")
        influence += influences[owner]
        query_sum += sum(queries[owner])*size
        require(sum(energy) == count*denominator, name+": total owner energy")
        require(sum((k-1)*e for k, e in enumerate(energy)) == influence,
                name+": influence accounting")
        v1 = sum(v*v for b, v in enumerate(aggregate) if b.bit_count() == 1)
        low = sum(v*v for b, v in enumerate(aggregate) if b.bit_count() in (1, 2))
        high = sum(v*v for b, v in enumerate(aggregate) if b.bit_count() >= 3)
        variance = low+high
        weighted_high = sum((k-2)*e for k, e in enumerate(energy) if k >= 3)
        require(v1 == energy[1], name+": unique degree-one owner")
        require(weighted_high == influence-count*denominator+v1,
                name+": critical owner-energy balance")
        require(high <= sum(k*e for k, e in enumerate(energy) if k >= 3),
                name+": support multiplicity bound")
        require(high <= 3*weighted_high, name+": high-degree energy bound")
        require(variance == sum(v*v for v in scores)*size, name+": score Parseval")
        require(variance <= count*denominator+query_sum, name+": query variance bound")
        # An exact admissible slack; K=0 whenever total influence <= count.
        k_value = max(0, influence-count*denominator)
        require(influence <= count*denominator+k_value, name+": influence budget")
        require(variance <= 4*low+3*k_value, name+": critical low-degree capture")
        records.append({
            "scored_owners": count, "total_hat_coordinates": n,
            "total_influence": str(F(influence, denominator)),
            "total_expected_queries": str(F(query_sum, denominator)),
            "score_variance": str(F(variance, denominator)),
            "degree_at_most_two_variance": str(F(low, denominator)),
            "degree_at_least_three_variance": str(F(high, denominator)),
            "admissible_K": str(F(k_value, denominator)),
        })
    return {"name": name, "prefixes": records}


class ReproducibleBits:
    """Specified xorshift64 stream for fixed synthetic truth tables."""
    def __init__(self):
        self.state = 0x20261004C0FFEE

    def next(self):
        x = self.state
        x ^= (x << 13) & ((1 << 64)-1)
        x ^= x >> 7
        x ^= (x << 17) & ((1 << 64)-1)
        self.state = x & ((1 << 64)-1)
        return self.state


def verify_fourier(cached):
    records = []
    for m in range(1, 5):
        n = 2*m
        for activation in range(1 << m):
            guesses, queries = [[] for _ in range(n)], [[] for _ in range(n)]
            for row in cached[m]:
                g, q = evaluate(row, activation)
                for i in range(n):
                    guesses[i].append(1 if g[i] == 0 else -1)
                    queries[i].append(q[i])
            records.append(verify_fourier_profile(
                "deterministic_block_m%d_mask%d" % (m, activation), guesses, queries))
    stream = ReproducibleBits()
    for n in range(1, 6):
        for example in range(32):
            guesses, queries = [], []
            for owner in range(n):
                visible = [j for j in range(n) if j != owner and stream.next() & 1]
                truth = [1 if stream.next() & 1 else -1
                         for _ in range(1 << len(visible))]
                table = []
                for x in range(1 << n):
                    index = sum(((x >> j) & 1) << k for k, j in enumerate(visible))
                    table.append(truth[index])
                guesses.append(table)
                queries.append([len(visible)]*(1 << n))
            records.append(verify_fourier_profile(
                "fixed_synthetic_n%d_example%02d" % (n, example), guesses, queries))
        # Whole-block parity attains the high-degree factor 3 when n=3.
        guesses = [[-1 if (x & (((1 << n)-1) ^ (1 << owner))).bit_count() % 2 else 1
                    for x in range(1 << n)] for owner in range(n)]
        queries = [[n-1]*(1 << n) for _ in range(n)]
        records.append(verify_fourier_profile("parity_team_n%d" % n, guesses, queries))
    return records


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path,
                        default=Path(__file__).resolve().with_name("results.json"))
    args = parser.parse_args()
    blocks, gates, cached = verify_blocks()
    representatives = verify_representatives()
    fourier = verify_fourier(cached)
    prefixes = sum(len(r["prefixes"]) for r in fourier)
    zero_slack = sum(p["admissible_K"] == "0" for r in fourier for p in r["prefixes"])
    summary = {
        "status": "all checks passed", "logical_checks": CHECKS,
        "activated_block_strategies": len(blocks),
        "activated_block_hat_seed_states": sum(r["enumerated_hat_seed_states"] for r in blocks),
        "public_gate_strategies": len(gates),
        "public_gate_hat_seed_states": sum(r["enumerated_hat_seed_states"] for r in gates),
        "other_representative_strategies": len(representatives),
        "other_representative_hat_seed_states":
            sum(r["enumerated_hat_seed_states"] for r in representatives),
        "fourier_profiles": len(fourier), "fourier_scored_prefixes": prefixes,
        "fourier_prefixes_with_K_zero": zero_slack,
    }
    result = {
        "format_version": 1,
        "scope": "Exact finite identities and examples; not a computational proof of infinite theorems.",
        "arithmetic": "Integer enumeration and fractions.Fraction; exact rational JSON values are strings.",
        "synthetic_truth_tables": {
            "selection": "32 fixed synthetic profiles for each ambient size 1 through 5",
            "generator": "xorshift64, shifts 13/7/17, seed 0x20261004C0FFEE",
            "interpretation": "All hat assignments checked within each selected profile; no Monte Carlo inference.",
        },
        "public_gate_interpretation":
            "One shared gate for the whole strategy; finite costs checked, not almost-sure success.",
        "summary": summary, "activated_blocks": blocks, "public_gated_blocks": gates,
        "other_representative_strategies": representatives, "fourier_bookkeeping": fourier,
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2, sort_keys=True)+"\n", encoding="utf-8")
    print("All exact finite checks passed.")
    print("Activated blocks: %d strategies, %d hat/seed states (m=1..5; alpha=1/2,1/4)." %
          (len(blocks), summary["activated_block_hat_seed_states"]))
    print("Public gates: %d strategies, %d hat/seed states; all expected per-owner costs <= 1." %
          (len(gates), summary["public_gate_hat_seed_states"]))
    print("Other sign-bound examples: %d strategies, %d hat/seed states." %
          (len(representatives), summary["other_representative_hat_seed_states"]))
    print("Fourier accounting: %d profiles, %d scored prefixes, including %d with K=0." %
          (len(fourier), prefixes, zero_slack))
    print("Logical checks: %d. All probabilities and moments used exact arithmetic." % CHECKS)
    print("Finite checks do not replace the article's proofs of infinite assertions.")
    print("Results written to "+str(args.output))


if __name__ == "__main__":
    main()
