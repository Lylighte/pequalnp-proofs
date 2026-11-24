# A 39-gate lower bound for concurrently used gates

Make the dual reduction and fix one consistent accepting proof DAG D(L) per line L as in cycle-anchor.md. For a gate g let its uses be the lines L whose proof DAG includes g. All references to uses below concern these selected certificates, not all line rows on which a gate happens to evaluate true.

**Theorem.** If the use set of every gate lies in some pencil, the original circuit has at least 39 gates. This allows up to four uses, arbitrary depth, arbitrary alternation and repeated variables in an accepting proof.

Write a_L and o_L for the AND and OR counts in D(L). It has exactly four raw sources, a_L+o_L+4 vertices, and 2a_L+o_L edges, because each OR keeps one chosen edge. Its cycle rank r_L is therefore a_L−3.

Add the thirteen graphs in any order. Given the next graph D(L), let H be its intersection as a vertex-and-edge graph with the union of the previous graphs. Let k be the number of raw vertices, c the number of connected components, and r the cycle rank of H; all are zero for the empty intersection. Shared AND gates always have both edges in this intersection. Shared OR gates have one entering edge unless all preceding uses selected the operand opposite to L's choice, in which case this OR has indegree zero in H. Call the number in this last case s. Subtracting the vertex count from the edge count gives exactly

    number of already counted AND gates in D(L) = r + s + k − c.

The graph H is a union of D(L) intersected with individual earlier D(M). Group these intersections by p=L intersect M. Every such group contains the raw vertex p. Distinct groups are vertex-disjoint: a shared vertex across the groups would occur simultaneously for L and two earlier lines which meet L at different points. These lines are nonconcurrent, contrary to the hypothesis. Raw vertices cannot cause this either, as their use sets are always pencils. Thus c≥k. The number of already counted AND gates is at most r_L+s, because H is a subgraph of D(L).

Every OR contributes to s in at most one addition, the first use of its second operand. Thus the number of physical AND gates in the union is at least the sum of a_L minus the sum of r_L minus the number of OR gates. Since a_L−r_L=3 for every line, adding back the OR count proves 39.

In particular, every circuit of fewer than 39 gates would, under *every* consistent choice of accepting proofs, have some gate used by three lines without a common point. The earliest such gate must be an OR gate, as both operands of an AND occur in all its selected proofs, and raw vertices are always used concurrently. It suffices in the theorem to check the use sets of OR gates.

Without the concurrence assumption the same calculation gives the exact obstruction. In any line order the surplus above three AND gates contributed by the cycle rank of D(L) can be offset by at most c's deficit from k, after paying the first new use of an OR operand. Thus every sub-39 circuit has, in every order, an addition whose common part H connects two distinct raw points of L. This last conclusion follows also when H has components without a raw point: c<k still forces such a connection. The full bound remains open in that case.
