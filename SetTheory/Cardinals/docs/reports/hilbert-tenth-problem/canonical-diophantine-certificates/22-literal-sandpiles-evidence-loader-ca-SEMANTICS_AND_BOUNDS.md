# Explicit fixed U15 lazy cellular automaton

This is a complete semantic layer, separate from the correctness of any sandpile gate or geometric wiring implementation. All Python here is newly authored. It does not import or execute an upstream simulator.

## 1. Data and conventions

The transition table is the supplied pure JSON file `../data/u15_table.json`. `lazy_u15.py` embeds exactly that table, replacing the direction letters by displacements `-1,+1`. The verifier checks equality entry by entry. Its 15 control states are `A,...,O`; the tape alphabet is `{0,1}`, with blank `0`; the only undefined transition is `(J,1)`. The initial head position is zero, and the default initial control state is `A`.

A U15 configuration at time `t` consists of the tape **before** its next transition, its control state, and its head position. If the configuration at time `T` reads `1` in control state `J`, the machine has halted after exactly `T` executed transitions. In particular, halting is detected upon arrival in that configuration; it is not counted as an additional transition.

The active CA state IDs are:

- `t(0)=0`, `t(1)=1`
- `h(q,g)=2+2*index(q)+g`, where `index(A)=0,...,index(O)=14`
- left front `FL=32`, right front `FR=33`

There are 34 active states. The lazy state is `lambda=-1`, and the pattern wildcard is `*=-2`; neither belongs to the active set `S={0,...,33}`. The final head is `h(J,1)=21`; put `tau=S\{21}`, so `|tau|=33`.

Using a final **head-and-letter pair**, rather than a final control state, is a harmless specialization of Cairns's construction to a partial TM. No final pair occurs as a positively tested pattern entry. A nonfinal transition may output either `h(J,0)` or `h(J,1)`, according to the symbol already on its destination square. Thus the undefined U15 transition is implemented literally, without changing its machine or adding a transition.

## 2. Literal finite rule set

Each radius-two rule is `(pi[-2],pi[-1],pi[0],pi[1],pi[2]) -> output`. An entry `*` imposes no requirement; any other entry requires equality with that active state. At output cell `(x,t+1)`, an input `(k,s)` refers to active state `s` at `(x+k,t)`. No rule tests for absence or for laziness. If exactly one rule matches, its output is the next state; if none matches, the next state is lazy; if two or more match, the automaton malfunctions. We prove no malfunction on the authorized initialization family below.

In the following list, `a,b` range independently over `tau`, `u,v,w` over `{0,1}`, and `(q,g)` over the 29 defined U15 transition pairs. Write `delta(q,g)=(write,d,qnext)`.

1. Head at center: `(a,t(u),h(q,g),t(v),b) -> t(write)`
2. No nearby head: `(a,t(u),t(v),t(w),b) -> t(v)`
3. Left front adjacent: `(*,FL,t(u),t(v),b) -> t(u)`
4. Left front becomes blank: `(*,*,FL,t(v),b) -> t(0)`
5. Right front adjacent: `(a,t(u),t(v),FR,*) -> t(v)`
6. Right front becomes blank: `(a,t(u),FR,*,*) -> t(0)`
7. Left front moves: `(*,*,*,FL,b) -> FL`
8. Right front moves: `(a,FR,*,*,*) -> FR`
9. Head on right: `(a,t(u),t(v),h(q,g),b) -> h(qnext,v)` if `d=-1`, otherwise `t(v)`
10. Head on left: `(a,h(q,g),t(u),t(v),b) -> h(qnext,u)` if `d=+1`, otherwise `t(u)`

The integer generator `iter_rules()` in `lazy_u15.py` fixes the enumeration order. Its `Rule.inputs` is an ordered tuple of `(offset,stateID)` pairs, sorted by increasing offset. Its `Rule.output` is the integer output state. Rule IDs are zero-based positions in this deterministic stream. `rules.jsonl.gz` materializes that same stream; each decompressed line is compact JSON `[ruleID,[five pattern IDs],outputID]`.

Exact counts:

| Family | Count |
|---|---:|
| Head at center | `29*2^2*33^2 = 126324` |
| No nearby head | `2^3*33^2 = 8712` |
| Left front adjacent | `2^2*33 = 132` |
| Left front becomes blank | `2*33 = 66` |
| Right front adjacent | `33*2^2 = 132` |
| Right front becomes blank | `33*2 = 66` |
| Left front moves | `33` |
| Right front moves | `33` |
| Head on right | `126324` |
| Head on left | `126324` |
| **Total** | **388146** |

The arity histogram is `{2:66,3:132,4:264,5:387684}`. Consequently there are exactly 1,940,004 positive one-hot input occurrences and 388,146 one-hot output occurrences per CA macrocell. The manifest lists each state's producer count `m_s`, each state's input-occurrence count `f_s`, and the counts at every offset. In particular, `f_21=0` while `m_21=2178`: the final-state root has no outgoing fanout. All other `f_s` are positive. A source root at `(x,t)` used at offset `k` feeds the corresponding rule in target `(x-k,t+1)`.

These counts are intentionally not optimized. They provide a finite literal circuit input with at most five tested states per rule, avoiding a reliance on an informal schematic.

## 3. Finite initialization on arbitrary finite binary tapes

Let `a<=0<=b` and let the initial tape be blank outside `[a,b]`. Put `n=b-a+1>=1`, and define

```
L = min(-3,a-1),     R = max(3,b+1),     M = max(3,n).
```

The initial CA state is:

- `FL` at `L`, and `FR` at `R`
- the initial headed symbol `h(A,tape(0))` at zero
- `t(tape(x))` at every other integer strictly between `L` and `R`
- lazy at every other coordinate

This is finite. It uses exactly `R-L+1` active state roots, with the head initially at distance at least three from either front. Because the interval `[a,b]` contains zero, `-L<=M` and `R<=M`.

For a word `w` of declared length `n` placed at `0,...,n-1`, the simpler specialization is `L=-3`, `R=max(3,n)`; the empty word also works with `R=3`. `initialize_word()` uses precisely this specialization. `initialize()` supports arbitrary two-sided finite tapes; omitted tape coordinates are blank. Zero-valued entries outside a declared interval do not matter.

The CA construction does not assert that arbitrary words are valid encodings for the universal-machine reduction. It implements the supplied U15 table on every finite binary tape. Any reduction from another computational model must separately supply its correct U15 input encoding.

## 4. Pre-halt simulation and no malfunction

Until a final headed pair first appears, at every time `t`:

1. The active support is the whole integer interval `[L-t,R+t]`
2. `FL` and `FR` are at its two endpoints
3. Every interior square is the correct U15 tape symbol, except for the unique correct headed symbol at its head position `p_t`
4. The head lies at least three cells from either front
5. No other active states occur

Induction proves these claims. The head moves one cell per TM transition, as do the fronts, so the distance margins never shrink below three. The fronts are at least six cells apart, so no radius-two neighborhood can contain both of them. Away from the fronts, exactly one of the center/head-left/head-right/no-head families applies. The two outer positions in its pattern take their actual values in `tau`, giving exactly one literal expanded rule. At a front or at a cell one position behind it, exactly its listed boundary family applies. Immediately outside each front, exactly its movement family applies. More distant cells match no rule. The family cases have incompatible required symbols in the relevant inner positions, so these matching rules are unique.

The transition outputs write the old head square, preserve every other tape square, and place the new head on the correct adjacent symbol. This includes arrival at `h(J,1)`. Thus the first appearance of the final CA head is precisely the U15 halting configuration at the same `(T,p)`.

## 5. Exact shutdown, not just an asymptotic speed argument

Suppose the machine halts at time `T` and position `p`. Let the front coordinates at that time be `l=L-T` and `r=R+T`, and let

```
D_L = p-l = p-L+T,     D_R = r-p = R+T-p.
```

Both distances are at least three. At time `T+1`, exactly the five cells `p-2,...,p+2` become lazy. Each of their potentially applicable patterns positively tests the final head, or requires a nonfinal headed pair where the final head occurs, and therefore fails. All other updates are the usual tape/front updates. In particular, there are no headed states after this step.

For every integer `s>=1`, the active support at time `T+s` consists of the following two disjoint wings, omitting an interval when its left endpoint exceeds its right endpoint:

```
left wing:  [L-T-s, p-2s-1]      if s<D_L, otherwise empty
right wing: [p+2s+1, R+T+s]      if s<D_R, otherwise empty
```

A nonempty left wing has `FL` at its left endpoint and only tape symbols to its right. A nonempty right wing has `FR` at its right endpoint and only tape symbols to its left. All other coordinates are lazy. Their lengths are exactly `max(D_L-s,0)` and `max(D_R-s,0)`.

To prove this invariant, a left wing of length `m>=2` moves its front one position left, produces blank tape behind the moving front when enough supporting tape exists, and loses its two rightmost active positions. Its new interval is one cell longer on the left and two shorter on the right, of length `m-1`. This remains true for `m=2`, where only the new front survives. For `m=1`, no movement rule matches because the required square behind the front is lazy, so the wing disappears. The right-wing proof is symmetric. Every surviving output has exactly one matching literal rule, and every excluded output has none. Thus shutdown cannot malfunction. This also establishes the claimed speed-two inward-facing lazy boundary and speed-one outward-moving front, including their final collision.

It follows that the **first all-lazy time**, not merely an upper bound, is

```
H = T + max(D_L,D_R) = 2T + max(p-L,R-p).
```

The last active row is `H-1`. The exact minimum and maximum coordinates ever active are

```
x_min = 2L-2T-p+1,     x_max = 2R+2T-p-1.
```

They are the positions of the last surviving left and right fronts, respectively. The exact number of active CA spacetime cells, including the initialization row and the final head, is

```
A = (T+1)(R-L+1+T) + D_L(D_L-1)/2 + D_R(D_R-1)/2.
```

The first term sums `R-L+1+2t` over `0<=t<=T`; the other terms sum the two shrinking-wing lengths over all positive `s`.

If the machine never halts, the pre-halt invariant holds forever and each row has two active fronts. Hence the CA has infinitely many active spacetime cells. If it halts, the formulas above give finitely many active spacetime cells and a permanently all-lazy state. The all-lazy state is fixed because every rule has at least two positive inputs. Thus global extinction, finite active spacetime, and U15 halting are equivalent for this initialization family.

## 6. Explicit quadratic prism bounds

Since `|p|<=T`, for general two-sided input interval of length `n>=1` and `M=max(3,n)`:

```
H <= M+3T
all active roots have 0<=t<=M+3T-1
and -2M-3T+1 <= x <= 2M+3T-1.
```

The number of integer `(x,t)` cells in this root prism is at most

```
(M+3T)(4M+6T-1) <= 21(n+T+1)^2.
```

Indeed `M<=n+2`, `M+3T<=3(n+T+1)`, and `4M+6T-1<=7(n+T+1)`.

For a one-sided word and `M=max(3,n)`, the sharper convenient coordinate bound is

```
-5-3T <= x <= 2M+3T-1,
0 <= t <= M+3T-1.
```

For a literal gate circuit, partial AND evaluations can happen in a target cell even if no CA output state is produced there. Such activity must be charged to an active predecessor root. Every tested input belongs to time `t-1` and is at spatial offset at most two. Therefore, assuming internal gate networks have no independent seeds and cannot activate state roots without a complete rule, a sufficient **target-cell collar** is one extra time row and two extra spatial positions on each side:

```
0<=t<=M+3T,
-2M-3T-1 <= x <= 2M+3T+1.
```

This collared prism contains at most

```
(M+3T+1)(4M+6T+3) <= 24(n+T+1)^2
```

integer cells for `n>=1`. The physical wire routing may require a further fixed collar and a fixed thickness in the third direction; those are geometric constants independent of `n,T`. This document does not claim that the semantic argument alone proves safe sandpile routing.

## 7. Verification and source cautions

`test_lazy_u15.py` uses the complete literal rule set, indexed only by wildcard masks. Its engine detects multiple matching rules. It compares pre-halt evolutions to an independently updated TM tape, then checks every shutdown support, exact extinction, exact coordinate extrema, and exact active-cell count. `verification.json` records a passing run over 58 initializations and 4,335 literal CA updates, including all 30 initial headed pairs and nine halting cases. One default-state-A halting example has the 41-bit tape

```
01100001100111101000010100111001100001011
```

placed at coordinates `-20,...,20`; it halts at `T=75,p=-13`. The tests are checks, not substitutes for the induction proof above.

Primary reference: Hannah Cairns, *Some Halting Problems for Sandpiles*, arXiv:1508.00161v2, sections 5-6, especially the partial rules in section 6.2 and Corollary 1 in section 5.2.3. The primary paper is available at https://arxiv.org/pdf/1508.00161. Three literal-text issues are resolved explicitly here rather than propagated:

- The pattern matching definition must compare `pi_k` with `S_t(x+k)`, not repeatedly with `S_t(x)`
- “All but finitely many squares are lazy at some time” in section 5.1 cannot define the desired extinction notion for a finite initialization; Corollary 1 correctly uses **all** states lazy at a finite time. Our definition is explicit and our theorem proves that stronger property
- The initialization paragraph's coordinate slips and figure labeling do not fix unique front positions. Our `L,R` initialization is unambiguous and its margins are proved

These clarifications do not alter the ten rule families or the intended radius-two/speed-one/speed-two construction.

## 8. Exact two-sided input-pair loader interface

For the Report32 convention supplied by the parent construction, let `ell,r` be binary strings, both written **nearest to the head first**. Initialize U15 in state `A` scanning a blank zero at coordinate zero, with

```
tape(-i-1)=ell[i],     tape(i+1)=r[i],     tape(0)=0.
```

All other tape symbols are zero. `initialize_pair(ell,r)` implements this map, retaining declared terminal zeroes in its extent, and has exactly

```
L=min(-3,-len(ell)-1),     R=max(3,len(r)+1).
```

A completely literal finite binary input grammar is

```
1^len(ell) 0 ell r.
```

Count the initial ones until the first zero, call this count `m`, read the next `m` bits as `ell`, and take all remaining bits as `r`. Reject an input with no delimiter zero, too few remaining bits, or any nonbinary character. `serialize_pair`, `parse_pair`, and `initialize_serialized_pair` implement this grammar. Empty `ell` and `r` serialize as the single bit `0`.

Let `n=len(ell)+len(r)>=0`. All the exact formulas of section 5 apply unchanged. In particular,

```
H=2T+max(p-L,R-p) <= n+3+3T,
last active row = H-1,
x_min=2L-2T-p+1 >= -2len(ell)-5-3T,
x_max=2R+2T-p-1 <=  2len(r)+5+3T.
```

Thus a convenient root prism has `n+3+3T` time rows and `2n+6T+11` spatial positions, at most `33(n+T+1)^2` cells. The one-time/two-space target-cell collar has at most

```
(n+4+3T)(2n+6T+15) <= 60(n+T+1)^2
```

cells. This pair-length convention differs by one from the interval-length `n` used in sections 3 and 6 because the central scanned blank is included in the latter.

This interface is an explicit finite pair-to-CA loader. The theorem that arbitrary programs can be encoded as valid pairs for this particular U15 is a separate Neary-Woods universality dependency. No claim is made here to implement that earlier program-to-pair compiler.
