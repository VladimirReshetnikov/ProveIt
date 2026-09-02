# -*- coding: utf-8 -*-
r"""(Re)generate the Lean formalization register of
Combinatorial_Coefficient_Calculus.tex.

Run:  python add_register.py <path-to-tex>

* First run: adds the \lean macro to the preamble and appends the register
  section before \backmatter.
* Later runs: replaces the existing register section (everything from
  '\section{Lean formalization register}' to '\backmatter') with a fresh one.

One row per theorem-like environment (theorem/proposition/lemma/corollary/
identity/algorithm), in document order, with a status column:

  Lean      -- an exact (or more general) Lean counterpart exists
  partial   -- a named part of the statement is proved; the rest is named
  none      -- no Lean counterpart yet (the default)

Statuses come from the STATUS dictionary, keyed by label.  Unlabelled
results are keyed by environment name and running number.
"""
import io, re, sys

path = sys.argv[1]
s = io.open(path, encoding='utf-8').read()

# ---------------------------------------------------------------- macro
if '\\newcommand{\\lean}' not in s:
    anchor = '\\newtheorem{historical}[theorem]{Historical note}\n'
    assert s.count(anchor) == 1
    macro = anchor + (
        '\n% Crosswalk to the Lean development (Analysis/FabiusFunction/Lean/FabiusFunction):\n'
        '% typeset a declaration name verbatim, in text or in math mode.\n'
        '\\newcommand{\\lean}[1]{\\ifmmode\\text{\\texttt{\\detokenize{#1}}}'
        '\\else\\nolinkurl{#1}\\fi}\n')
    s = s.replace(anchor, macro)

# ---------------------------------------------------------------- statuses
# label -> (status, "declarations (module)")
STATUS = {
 'thm:first-cycle': ('partial',
   r"recurrence and boundary values are Mathlib's \lean{Nat.stirlingFirst_succ_succ}, "
   r"\lean{Nat.stirlingFirst_succ_zero}, \lean{Nat.stirlingFirst_eq_zero_of_lt}; the "
   r"defining expansions are \lean{Fabius.ascPochhammer_eq_sum_monomial_stirlingFirst} and "
   r"\lean{Fabius.descPochhammer_eq_sum_monomial_signedStirlingFirst} "
   r"(\lean{StirlingBasisChange}); the permutation count itself is not formalized"),
 'thm:second-recurrence': ('Lean',
   r"\lean{Nat.stirlingSecond_succ_succ}, \lean{Nat.stirlingSecond_succ_zero}, "
   r"\lean{Nat.stirlingSecond_eq_zero_of_lt} (Mathlib); the set-partition count is "
   r"Mathlib's definition by this recurrence"),
 'thm:second-explicit': ('Lean',
   r"\lean{Fabius.factorial_mul_stirlingSecond_eq_sum} (over $\mathbb Z$) and "
   r"\lean{Fabius.stirlingSecond_eq_sum_div_factorial} (over $\mathbb Q$) "
   r"(\lean{StirlingBasisChange}); proved by binomial inversion of "
   r"\lean{Fabius.pow_eq_sum_stirlingSecond_mul_factorial_mul_choose}"),
 'thm:stirling-basis': ('Lean',
   r"\lean{Fabius.ascPochhammer_eq_sum_monomial_stirlingFirst}, "
   r"\lean{Fabius.descPochhammer_eq_sum_monomial_signedStirlingFirst}, "
   r"\lean{Fabius.X_pow_eq_sum_stirlingSecond_mul_descPochhammer}, "
   r"\lean{Fabius.X_pow_eq_sum_stirlingSecond_mul_ascPochhammer}, "
   r"\lean{Fabius.pow_eq_sum_stirlingSecond_mul_factorial_mul_choose} "
   r"(\lean{StirlingBasisChange}); polynomial identities over every commutative ring"),
 'cor:stirling-inverse': ('Lean',
   r"\lean{Fabius.sum_range_stirlingSecond_mul_signedStirlingFirst}, "
   r"\lean{Fabius.sum_range_signedStirlingFirst_mul_stirlingSecond} and their "
   r"\lean{Icc} forms (\lean{StirlingBasisChange})"),
 'thm:lah-conv': ('Lean',
   r"\lean{Fabius.ascPochhammer_eq_sum_lahNumber_mul_descPochhammer}, "
   r"\lean{Fabius.descPochhammer_eq_sum_lahNumber_mul_ascPochhammer}, "
   r"\lean{Fabius.sum_range_lahNumber_mul_lahNumber}, "
   r"\lean{Fabius.lahNumber_eq_sum_stirlingFirst_mul_stirlingSecond} (\lean{LahNumbers}); "
   r"the closed form of the definition is \lean{Fabius.lahNumber_succ_succ_mul_factorial}"),
 'thm:stirling-egfs': ('partial',
   r"\lean{Fabius.exp_sub_one_pow}, \lean{Fabius.egf_stirlingSecond}, "
   r"\lean{Fabius.negLogOneSub_pow}, \lean{Fabius.egf_stirlingFirst}, "
   r"\lean{Fabius.log_pow} (\lean{StirlingGeneratingFunctions}), as formal power series "
   r"over any commutative $\mathbb Q$-algebra; the bivariate generating function "
   r"\cref{eq:second-double-egf} is not formalized"),
 'thm:stirling-transform': ('partial',
   r"the inversion formula is \lean{Fabius.stirling_inversion}, "
   r"\lean{Fabius.stirling_inversion_symm}, \lean{Fabius.stirling_inversion_iff} "
   r"(\lean{StirlingBasisChange}), for sequences in any additive commutative group; "
   r"the generating-function form is not formalized"),
 'thm:bell-binomial-recurrence': ('Lean', r"\lean{Nat.bell_succ} (Mathlib, the definition)"),
 'thm:bell-stirling-sum': ('Lean',
   r"\lean{Fabius.bell_eq_sum_stirlingSecond}, \lean{Fabius.bell_eq_sum_sum_div_factorial} "
   r"(\lean{BellStirling})"),
 'thm:dobinski': ('Lean',
   r"\lean{Fabius.dobinski} (\lean{BellStirling}), from the general Poisson moment identity "
   r"\lean{Fabius.tsum_pow_mul_pow_div_factorial}"),
 'thm:poisson-stirling-moments': ('partial',
   r"the moment series $\sum_m m^n\lambda^m/m! = e^{\lambda}\sum_k S(n,k)\lambda^k$ is "
   r"\lean{Fabius.tsum_pow_mul_pow_div_factorial} (\lean{BellStirling}) for every real "
   r"$\lambda$; the probabilistic phrasing is not formalized"),
 'thm:merged-binomial-inversion': ('Lean',
   r"\lean{Fabius.binomial_inversion_iff} (additive commutative groups) and "
   r"\lean{Fabius.binomial_inversion_ring_iff} (commutative rings) "
   r"(\lean{BinomialInversion}); the kernel orthogonality is "
   r"\lean{Fabius.sum_Icc_neg_one_pow_choose_mul_choose}; the EGF form is not formalized"),
 'thm:eulerian-recurrence': ('partial',
   r"\lean{Fabius.eulerianNumber} is defined by this recurrence "
   r"(\lean{Fabius.eulerianNumber_succ_left}, \lean{Fabius.eulerianNumber_succ_succ}, "
   r"module \lean{EulerianNumbers}); the descent count and the polynomial form "
   r"\cref{eq:eulerian-poly-recurrence} are not formalized"),
 'thm:worpitzky': ('Lean',
   r"\lean{Fabius.worpitzky_nat} (natural numbers, all $n$) and "
   r"\lean{Fabius.worpitzky_polynomial} (in $\mathbb Q[x]$, with "
   r"\lean{Fabius.binomialPoly} for $\binom{x+k}{n}$) (\lean{EulerianNumbers})"),
 'cor:eulerian-power-sum': ('Lean',
   r"\lean{Fabius.sum_range_pow_succ_eq_sum_eulerianNumber} (\lean{EulerianNumbers}), "
   r"in the form $\sum_{r=0}^{m} r^{n+1}=\sum_k A(n+1,k)\binom{m+k+1}{n+2}$"),
}

ENV = re.compile(
    r'\\begin\{(theorem|proposition|lemma|corollary|identity|algorithm)\}'
    r'(?:\[([^\]]*)\])?\s*(?:\\label\{([^}]*)\})?')
CHAPTER = re.compile(r'\\chapter\*?\{([^}]*)\}')
SECTION_START = '\\section{Lean formalization register}'
BACK = '\\backmatter\n'


def tex_escape(t):
    return t.replace('&', '\\&').replace('%', '\\%').replace('_', '\\_').replace('#', '\\#')


# remove an existing register before scanning
if SECTION_START in s:
    i = s.index(SECTION_START)
    j = s.index(BACK)
    assert i < j
    s = s[:i] + s[j:]

rows = []
counters = {}
chapter = ''
events = [(m.start(), 'ch', m) for m in CHAPTER.finditer(s)] + \
         [(m.start(), 'env', m) for m in ENV.finditer(s)]
events.sort(key=lambda e: e[0])
for _, kind, m in events:
    if kind == 'ch':
        chapter = m.group(1)
        continue
    env, title, label = m.group(1), m.group(2), m.group(3)
    counters[env] = counters.get(env, 0) + 1
    key = label if label else '%s-%d' % (env, counters[env])
    status, decl = STATUS.get(key, ('none', ''))
    name = ('\\Cref{%s}' % label) if label else ('%s (unlabelled, no.~%d)' % (env, counters[env]))
    ttl = tex_escape(title) if title else ''
    rows.append((name, ttl, status, decl))

unknown = set(STATUS) - {r[0][6:-1] for r in rows if r[0].startswith('\\Cref{')}
assert not unknown, 'STATUS keys without a matching label: %s' % sorted(unknown)

n_lean = sum(1 for r in rows if r[2] == 'Lean')
n_part = sum(1 for r in rows if r[2] == 'partial')
n_none = sum(1 for r in rows if r[2] == 'none')

table = []
table.append(SECTION_START)
table.append('\\label{sec:lean-register}')
table.append(
 'Every theorem-like environment of this monograph is listed here with the status of its '
 'formalization in the Lean development \\path{Analysis/FabiusFunction/Lean/FabiusFunction} '
 '(Mathlib \\texttt{v4.32.0}).  \\emph{Lean} means that a public, compiled declaration proves '
 'the exact statement or a more general one (the generalization is then noted next to the '
 'result); \\emph{partial} means that a named part of the statement is proved and the rest is '
 'named; \\emph{none} means that no Lean counterpart exists yet.  A citation, a numerical '
 'check, or a plausible derivation does not count.  The register is generated from the '
 'source and must be regenerated when results are added.  Current totals: '
 '%d Lean, %d partial, %d none, of %d results.' % (n_lean, n_part, n_none, len(rows)))
table.append('')
table.append('\\begin{footnotesize}')
table.append('\\begin{longtable}{@{}p{0.16\\textwidth}p{0.22\\textwidth}p{0.08\\textwidth}p{0.48\\textwidth}@{}}')
table.append('\\toprule')
table.append('Result & Title & Status & Lean declarations (module) \\\\')
table.append('\\midrule')
table.append('\\endfirsthead')
table.append('\\toprule')
table.append('Result & Title & Status & Lean declarations (module) \\\\')
table.append('\\midrule')
table.append('\\endhead')
table.append('\\bottomrule')
table.append('\\endfoot')
for name, ttl, status, decl in rows:
    table.append('%s & %s & %s & %s \\\\' % (name, ttl, status, decl))
table.append('\\end{longtable}')
table.append('\\end{footnotesize}')
table.append('')

assert s.count(BACK) == 1
s = s.replace(BACK, '\n'.join(table) + '\n' + BACK)

io.open(path, 'w', encoding='utf-8', newline='\n').write(s)
print('rows', len(rows), 'Lean', n_lean, 'partial', n_part, 'none', n_none)
