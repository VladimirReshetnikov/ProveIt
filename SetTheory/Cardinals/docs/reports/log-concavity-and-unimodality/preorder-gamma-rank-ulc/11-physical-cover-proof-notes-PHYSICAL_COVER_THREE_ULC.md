# Rank ULC for arbitrary directed relations with a three-vertex physical cover

Status: proposed ordinary extension using the independently approved coefficientwise boundary theorem; independent review pending. October 1, 2026. Previously released packages are unchanged.

## Theorem

Let D be a finite loopless directed relation whose underlying undirected graph has a vertex cover C of size at most three. Give each physical vertex independent nonnegative tail and head activities. Count each feasible ordered disjoint endpoint support once, with the product of its role activities, and write Gamma_D(t)=sum gamma_k t^k.

Then Gamma_D is ultra-log-concave with respect to its actual surviving degree. No transitivity is required. The internal directed relation on C is arbitrary, including opposite arcs, directed cycles, and every fork pattern.

In particular, this proves the general two-tail/three-head role-cover ULC assertion whenever the two selected physical tail vertices are contained in the selected set of three physical head vertices. Indeed, their physical union is then a three-vertex cover.

## Setup and support decomposition

The actual matching degree is at most three because every edge meets C. Degrees at most two follow from the universal first Newton inequality proved below. Thus it remains to consider C={0,1,2} and actual degree three.

Write I=V\C. It is independent. Delete all internal core arcs to obtain the bipartite physical relation D_0 on C and I. Use the approved exterior coefficients, with original role activities included:

- a_i: size-one supports of D_0 using core {i}
- b_ij: size-two supports of D_0 using core {i,j}
- c: size-three supports of D_0 using all three cores

Put A=sum_i a_i and B=sum_(i<j)b_ij. For an unordered core pair {i,j}, let

    h_ij = 1_(i→j in D) u_i v_j + 1_(j→i in D) u_j v_i,
    E = h_01+h_02+h_12.

Let H be the sum of weights of size-two supports in D using all three physical core vertices. Such a support uses one internal core arc and one exterior arc. Every other size-two support has exactly two used core vertices and belongs to D_0. A size-three support cannot use an internal edge: that would consume two core vertices, leaving only one core vertex for its other two disjoint edges. Therefore

    gamma_1=A+E,     gamma_2=B+H,     gamma_3=c.

In particular actual degree three implies c>0. These decompositions are at the level of endpoint supports, with core-usage cardinality separating the summands.

## Exterior inequalities

The approved three-core coefficientwise theorem gives, for distinct i,j,k,

    b_ij b_ik >= a_i c.

Summing yields

    A c <= b_01 b_02 + b_01 b_12 + b_02 b_12.                 (1)

There is also the elementary coefficientwise inequality

    a_k b_ij >= c.                                         (2)

For any size-three support, choose one witnessing matching. Its edge at core k is a singleton support counted by a_k; deleting that edge leaves a size-two support counted by b_ij. The product has the original support weight. Multiple possible decompositions and products with intersecting exterior endpoints only add nonnegative terms, so (2) follows.

## Internal-edge witness bounds

For each core pair {i,j}, with remaining vertex k, put

    w_ij = h_ij a_k.

Each product term consists of an internal arc on {i,j} and an exterior arc at k. These two arcs are physically disjoint. For a fixed unordered pair {i,j}, every resulting endpoint support is counted exactly once: opposite orientations of its internal edge give different ordered endpoint supports, and its exterior edge is then forced by those endpoints and their roles. Thus

    0 <= w_ij <= H.                                        (3)

The sum w_01+w_02+w_12 counts the internal-edge witnesses of H-supports. Such a support has three core vertices and one exterior vertex. If two core vertices are tails and one is a head, its internal edge must run from one of the two tails to that head, so there are at most two possibilities. The case of one core tail and two core heads is the order-dual case. Hence every H-support has at most two internal-edge witnesses, all of its same role weight, and

    w_01+w_02+w_12 <= 2H.                                  (4)

Both (3) and (4) hold coefficientwise. No core arc pattern is excluded. In particular, fork-induced duplicate matching witnesses are handled by the factor two in (4), not by pretending H is a sum without overlap.

Multiplying (2) by h_ij and summing also gives

    E c <= sum_(i<j) w_ij b_ij.                            (5)

## A three-variable bound and the Newton gap

Relabel the three numerical b-values as x>=y>=z>=0 and write w_x,w_y,w_z for their associated w-values. By (3),(4),

    x w_x + y w_y + z w_z <= H(x+y).                       (6)

For a direct verification, the slack is

    H(x+y) - (x w_x+y w_y+z w_z)
      = (x-y)(H-w_x)
        + y(2H-w_x-w_y-w_z) + (y-z)w_z >= 0.

Combining (1),(5),(6) yields

    gamma_1 gamma_3 = (A+E)c
        <= xy+xz+yz+H(x+y),
    gamma_2 = x+y+z+H.

It follows that

    gamma_2² - 3 gamma_1 gamma_3
      >= (x+y+z+H)² - 3[xy+xz+yz+H(x+y)]
       = (z+H-(x+y)/2)² + 3(x-y)²/4 >= 0.                 (7)

This proves the second cubic Newton inequality. If desired, the proof can be written as the exact nonnegative decomposition

    gamma_2² - 3 gamma_1 gamma_3
      = (z+H-(x+y)/2)² + 3(x-y)²/4
        + 3 sum_i (b_ij b_ik-a_i c)
        + 3 sum_(i<j) h_ij(a_k b_ij-c)
        + 3[(x-y)(H-w_x)
             + y(2H-w_x-w_y-w_z) + (y-z)w_z].

The ordering x>=y>=z is made after a nonnegative activity specialization; this is a scalar proof, not a claim that the full Newton gap is coefficientwise nonnegative.

## First inequality and actual-degree boundary

For any directed relation of actual positive-weight matching degree d>=2, form its compatibility graph on positive-weight directed arcs. Two arc vertices are adjacent when their physical endpoints are disjoint. Give arc i→j vertex weight u_i v_j. Its clique number is exactly d.

Let M be the total vertex weight and W_0 the original weighted edge sum. Repeatedly choose two nonadjacent positive-weight vertices and move all weight from one to the one with the larger weighted neighbor sum. This preserves total mass, does not decrease the weighted edge sum, and reduces the number of positive-weight vertices. Eventually the positive support is a clique of size q<=d, with masses m_1,...,m_q and weighted edge sum W_final. Then

    W_0 <= W_final = [M² - sum m_i²]/2 <= (d-1) M²/(2d).

One has M=gamma_1. Every size-two endpoint support has at least one disjoint-arc matching witness, with its prescribed support weight, so gamma_2<=W_0. Consequently

    gamma_1² >= [2d/(d-1)] gamma_2.

For d=3 this is gamma_1²>=3 gamma_2, the first cubic Newton inequality. For d=2 it is the stronger surviving-degree condition gamma_1²>=4 gamma_2. Degrees zero and one have no Newton inequalities. Positive-weight submatchings ensure no internal zeros. Thus the theorem holds with the actual degree, including all activity-induced degree drops.

## Dependency and scope

The only computational dependency within this research chain is the independently audited three-core boundary theorem in `../three-core-orientation-rayleigh/COEFFICIENTWISE_BOUNDARY_LEMMA.md`, certified by the 48-type/17,376-graph finite localization. Every internal-core step above is an ordinary support-counting or algebraic argument.

This theorem does not claim real-rootedness, signed-monomer stability, or negative correlation once internal core arcs are present. It does not resolve general two-tail/three-head covers whose physical union has four or five vertices.
