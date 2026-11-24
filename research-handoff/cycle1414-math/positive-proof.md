# A tight one-variable restriction for the 7-cycle edge function

This is a mathematical proof of the positive assertion underlying L-meta-1414. It applies to every circuit size. The 10-gate premise in the posted assertion only determines the index type of its set of gates. The posted assertion negates the positive result.

Let F(x) be the OR of the seven products x_i x_{i+1} with cyclic indices. Under x_p=b, call an original gate removable when its wire is constant on that face, or agrees on the entire face with a single earlier wire. We prove that there is a face on which at least three gates are removable for b=0 or at least four are removable for b=1.

## A cofactor fact

For any distinct p,q and either bit b, there are inputs x,y with x_q=y_q=b, differing only at p, for which F(x)=0 and F(y)=1. For b=0 choose a neighbor k of p other than q and take x to have just k active. For b=1 and q adjacent to p, take x to have just q active. Otherwise choose a neighbor k of p not adjacent to q and take x to have precisely q,k active. Such k exists because two vertices of the seven-cycle have at most one common neighbor. In every case y is obtained by adding p. In particular F is nonconstant on each one-coordinate face and depends on all seven input bits.

The executable cofactor-witnesses.cjs checks all 84 ordered triples (p,q,b), writes both input masks in cofactor-witnesses.json and records its counts in cofactor-witnesses.log. It also checks an explicit 10-gate upper bound on all 128 inputs.

## Reduction to an effective circuit

Associate each original wire its full truth table on the 128 inputs. Work through the gates in the original order. Maintain a representative for each table encountered, including the seven raw wires and two distinguished constant labels. A reference to a wire not yet present has the constant-false label, exactly as in Circuit.wires. For an original gate compute its table using these representatives. If the table already has a representative, use that representative. Otherwise retain this gate at its original index, record its arguments as representatives and use its original wire as the new representative. The NOT operation uses its first argument only. The empty AND and NOT are true, and the empty OR is false. Unary AND/OR and repeated arguments to AND/OR give a copy. An AND/OR with any constant input is a constant or a copy, and NOT of a constant is a constant. Consequently every retained gate is a unary NOT of a nonconstant wire or a binary AND/OR of two distinct nonconstant wires. Its table differs from each earlier gate and each raw wire and from both constants.

Take the representative of the actual output, including a constant-false label if the output index is invalid. By the cofactor fact it is a retained non-input gate. Delete everything that has no directed path to that representative. Every retained gate other than this output now has a successor. All seven raw variables still have paths to the output, since F depends on them. Successor and reader in the rest of the proof refer only to this effective graph. Each edge sourced at a gate points from a smaller original gate index to a larger one. Evaluating this graph gives the original truth function at each retained wire.

If a retained gate has constant value on a face it meets the first disjunct of the posted removal test. If it equals an earlier retained wire or raw input on the face, that very original wire index witnesses the second disjunct. Distinct retained gates are distinct original gates. Thus any lower bound obtained by counting removable retained gates carries over without requiring the new graph to have size 10. No claim that every unretained gate is itself removable is needed.

## Counting direct readers and successors

Suppose for contradiction that every zero face has at most two removable gates and every one face has at most three. Every gate that reads a fixed input becomes constant or equals an earlier wire. The same holds of every immediate successor of a gate whose value becomes constant. Indeed a binary AND/OR with one constant is constant or copies its other argument, and NOT of a constant is constant. Both observations count the gate itself. They imply that each raw input has at most two distinct direct readers, by using its zero face.

We will use this path observation. If all routes from a raw input p to the output pass through wires whose values are independent of p under a fixed setting of another raw input q, then F is independent of p under that setting. To see it, compare two evaluations with all coordinates except p equal. A differing value at the output can be traced backwards, choosing a differing argument at every gate. This yields a path from p to the output on which the values differ at every wire.

If a gate N reads p as NOT(p), it cannot be the output. On p=0 the gate N is constant and all its successors are removable. If p has an additional reader R, then N and R are already two removable gates on this face. Every successor of N must be R. Thus R reads both p and N. A retained unary gate cannot read both. The binary possibilities p AND NOT(p) and p OR NOT(p) are constant and were discarded. There can therefore be no additional reader of p. Also N has exactly one successor since two successors together with N would give three removals on p=0.

## The first binary gate

There is a binary gate because a circuit containing only unary gates cannot depend on seven inputs. Take the earliest retained binary gate G in the original order. Its arguments are literals. Before G, a retained negation can only be a negation of a raw input, since a second negation of the same literal returns a pre-existing raw table. Its two literals concern distinct variables p and q. Equal literals were identified, and opposite literals in an AND/OR give a constant.

If G reads NOT(p), every path from p passes through that negation and then through G by the preceding reader and successor bounds. Fix q so that its literal is the absorbing value for G. The value of G then becomes constant independently of p. This contradicts the cofactor fact by the path observation. The same argument excludes a negated q. Hence G reads raw p and raw q.

Fix q to the absorbing value for G. The cofactor fact forces a path from p to the output avoiding G, so p has a second direct reader P distinct from G. Likewise q has a second reader Q. These are their only readers. Neither P nor Q can precede G. An earlier reader would have to be NOT(p) or NOT(q), and such a negation is its variable's sole reader. G is not the output since it depends on at most two variables.

If G is AND, on p=0 both G and P are removable, and G is constant. Every successor of G therefore must be P. Similarly on q=0 every successor must be Q. G has a successor, so that successor equals both P and Q. It would read G,p,q, three distinct wires, contradicting the fan-in bound.

It remains to consider G=OR(p,q). P cannot be AND or NOT. On p=0 such a P would be constant and G would copy q. P could not be the output, since F is nonconstant on this face. A successor of P is later than G and P and is also removable, giving three removals. Thus P is OR, and similarly Q is OR.

There is no edge G to P. Such an edge would give P=OR(p,G)=G on every input, contrary to the construction of the retained graph. There is no edge P to G because of the order. Identical conclusions apply to Q. On p=1 the gates G,P are both constant. Neither is the output, since F varies on p=1. All their successors lie outside the pair and are removable. Since the bound is three there must be a single gate D that is the sole successor of G and the sole successor of P. In particular D reads G,P. Repeating this on q=1 yields a gate that is the sole successor of G and Q. G already has unique successor D, so D reads G,Q too. A gate reads at most two wires and P,Q are both distinct from G, hence P=Q. This OR reads both p and q and has the same full truth table as G. It could not have been retained. This exhausts the possible first gates and proves the contradiction.

For a circuit of size 10 choose the Finset of all the original gate indices removable on the face supplied by the proof. The zero-face threshold is three and the one-face threshold is four, exactly as in the question. This argument supplies the positive twin semantically. It is not a Lean kernel certificate for the full contrast pair.
