# An unconditional lower bound of 21 for L-meta-920

Use the dual zero-set description from reduction.md. On |Z| ≤ 4 the required output h_L is 1 exactly when Z=L. Different line outputs can never both be 1.

## Isolating the thirteen output gates

An output cannot be a raw input or a constant: h_L changes between L and L without q for each of the four q in L. Output wires for different lines are distinct, since their truth functions on this domain differ. Retain all thirteen output wires as designated gate outputs, but replace each use of any designated output as a gate operand with a free dual constant 0. This preserves every designated output throughout the admissible domain. In fact the modified gates never exceed their old values by monotonicity. If the old output for L is 1, all other outputs are 0. Before reaching its gate, every earlier overwritten output reference was already 0, so the gate for L is unchanged on this input. This argument allows the original outputs to have been read by later outputs. Invalid arguments and ignored arguments can be replaced by constants, and actual operand edges always run forward in time. The use of free constants is only for deriving a lower bound.

## A pencil requires twelve gates

Fix a point p. Its four incident lines partition the twelve other points into groups of three. For each selected line L and every q in L, changing the input from Z=L without q to Z=L changes h_L. Both inputs satisfy the promise. It follows that q has a directed path to that output in the modified graph. The four complete ancestor cones of the four selected outputs intersect at p. Their union is a connected undirected graph containing all thirteen input vertices. Every remaining gate or constant in this union has a path to one of the four outputs by construction. If the union contains m gates and c distinct constant vertices, it has at least m+13+c-1 edges by connectivity. There are at most 2m edges, since all operand edges end at gates of fan-in at most two. Thus the union has at least twelve gates. The nine other designated outputs are distinct sinks outside this union. The entire original circuit has at least 12+9=21 gates.

This bound allows arbitrary sharing and AND/OR gates and does not settle the posted bound of 39. The same argument can count any nonempty subset S of line outputs whose point-line incidence graph is connected. It yields |union of S|-1 gates in their ancestor union and a separate gate for each of the remaining outputs. The four-line pencil maximizes this particular count for the order-3 plane.
