# Restrictions on a 25-gate circuit with a hidden forest

This note is conditional on the thirteen selected outputs being binary AND sinks and the remaining twelve gates together with all thirteen sources forming an undirected tree. These conditions occur in the saturated branch of the 25-gate investigation. Normalize constants and copies first. Every hidden gate is then a read-once formula in its source variables, because its two predecessor source sets are disjoint: a shared source would create an undirected cycle at their join.

## The last hidden gate

Let the last hidden gate H join signals f and g in disjoint components A and B. A terminal using H and one further signal h uses h in just one component; suppose it is A. If H is OR, each such terminal may replace H by one of its two children. Indeed one child is true on the terminal's positive line; choosing it preserves that row and weakly decreases the output at every input. As H is last hidden and the outputs are sinks, choices are independent at different terminals. Thus H may be deleted outright. This argument for the last OR actually holds for any OR whose only uses are at output sinks.

Suppose H is AND. A cross-line output of the form H AND h from A is the product (f AND h) times g, over disjoint variable sets. On its specified line the B-section must be the unique globally minimum true input of g: fixing the A-section of that line, replace the B-section by a minimum input for g. The resulting input has at most four points and thus equals the target line. It follows that all such lines have exactly the same B-section. If its size is at least two there can be at most one line. If its size is one, say {b}, h such lines through b have disjoint A-sections of size three.

In the latter case f is true on h pairwise disjoint A-sections and requires at least h−1 original OR gates in its cone. Indeed replacing every AND by one chosen child weakly increases f and yields a pure OR circuit; to hit h disjoint nonempty inputs it needs h points and at least h−1 ORs. The analogous OR cost for the class whose extra signal lies in B is in the other component. These OR costs can be added to lower bounds on private AND gates required by known unique-minimum sections.

## The shared part of a terminal

An accepting D(L) here has at most one undirected cycle. If the two chosen parent proofs share vertices, their intersection is connected as a subtree in the hidden forest. It has a sink s, the split vertex in the unique cycle after adding the terminal, with a common upstream acceptance tree and two vertex-disjoint selected paths from s towards the two terminal parents. The source labels S below s and the side labels outside that common subtree are disjoint. Simultaneously replace all occurrences of s by a globally minimum input: the union with the outside gives at most four points, hence must recover L. Thus S is the unique globally minimum input of s. The same argument applies to every side subtree off either path; these contain no shared leaves.

One must distinguish the chosen proof intersection from the full syntactic intersection. If both chosen parent proofs actually include the chosen split s, the unique path property ensures that any additional common syntactic ancestors are upstream of s. Thus s is also the common root of their shared *full* subformula. Writing its value z, the two parent formulas have disjoint other variables. If their cofactors are f_i^0 and f_i^1, their AND is identically

    (f_1^0 AND f_2^0) OR (z AND f_1^1 AND f_2^1).

This follows by evaluating at the two values of z and using monotonicity. It is a representation of the existing terminal, with no assertion that the displayed formula can be implemented at zero additional cost.

## Using minimum witnesses consistently

Assign one global raw-point order to break ties. In the entire hidden forest choose the smaller minimum-cardinality witness at each OR, with equal cardinality resolved lexicographically in favor of the set containing the earliest point where the witnesses differ. At an AND take the union: input supports are disjoint in the hidden forest, so these choices yield the globally preferred minimum witness at every hidden gate. The resulting circuit bypasses ORs and retains only original AND gates.

All lines with an ordinary clean proof remain four-point outputs under these replacements. Each terminal parent in its chosen clean proof has a unique minimum witness equal to its subtree labels, by the context replacement argument. This remains valid for a semantically clean proof at certified singleton leaves, since for a terminal parent that is itself such a leaf its unique global minimum is its one point whenever the leaf was formed by the cycle compression above.

For a unicyclic chosen proof whose split s has S={p}, put p first in the global order. The chosen witness of s is {p}. Propagate along each path from s towards the terminal. A designated arm witness consists of p and a set U of exclusive points. At an AND, the side subtree has a globally unique minimum set: it occurs only in this arm with all its points disjoint from its outside. At an OR, the alternate child's raw support is disjoint from the whole selected child's raw support, including p and U. The outside still contains p via the other arm and contains the other 3−|U| points. A true input of the alternate child of size at most |U| would, together with the outside, give an input of size at most four missing all of U. If U is empty the prohibited alternate input is a constant true wire, already normalized out. Thus the other minimum is at least |U|+1, and in a tie the chosen branch wins because its witness contains p. This proves that both terminal parent witnesses are preserved by the global order. The argument works simultaneously for every line sharing the same split point p.

If |S|≥2, the hidden formula for s computes its unique minimum S. Its global pure-AND reduction therefore provides at least |S|−1 original hidden ANDs with distinct support sets of size at least two contained in S. Such supports cannot be charged to another line. The minimum supports of their *full* original gates are intrinsic as well: any local alternate minimum inserted into the clean proof of s on S would give a same-or-smaller different input to s.

One numerical consequence uses k OR gates, r semantically clean lines, b_1 remaining lines with one-point split supports and the larger supports S for other remaining lines. At most 2^k different global OR selections occur. Every one of the b_1 lines succeeds under some such selection, so some single selection preserves at least their average (rounded up) as well as all r clean lines. For each successful line the terminal and two other AND gates are charged using pure-AND supports. All thirteen terminals are counted regardless of success. The hidden charges for each larger S remain present with any global tie order, and are disjoint from the successful-line charges by their pure support labels. Hence

    m ≥ 13 + k + 2r + sum_large (|S|−1) + 2 ceil(b_1 / 2^k).

This does not settle the 25-gate branch. For k=2 it implies r≤2 at m=25.
