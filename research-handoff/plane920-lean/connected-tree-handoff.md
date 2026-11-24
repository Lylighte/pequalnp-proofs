# L-meta-920 connected hidden-tree reduction

Local partial proof under the official 13-input, binary AND/OR gate-list semantics and heavy-input promise. All theorem names below use the Plane920 namespace. The component theorems assume correctness, connected normalized hidden supports, and at most 25 gates. General lower bound 25 remains the unconditional project-level conclusion of this bundle.

## Last hidden merge

Bypass.remove_last_and constructs a physically shorter circuit. After deletion, each named output independently replaces references to the deleted original AND with an earlier child that agrees on that output's unique negative row. This gives a single replacement gate list and preserves all outputs together. Thus the last hidden gate of a 25-gate connected candidate must be an original OR, a dual AND.

LastMerge.three_orbits rules out end cuts equivalent, under point/line incidence permutations or side exchange, to masks 31, 63, and 95. The exclusion is kernel checked. root-pencil-orbits.cjs separately counts 702, 234, and 936 unordered cuts in these three orbits of the 5,616-element collineation group.

## Every internal merge

Restriction.tree_slices projects every plane line to each child component and their parent. Freezing outside U to the given line preserves every restricted target with at most |L ∩ U| points. The resulting signals come from actual internal prefixes and may be constants. Two signals per target suffice with a dual conjunction.

Restriction.merge_charges records how a crossed line is paid. A dual OR needs native unique minima on both sides. A dual AND can waive one native child minimum only if its other fixed driver has exactly the opposite side's minimum. The drivers are shared by every crossed line at the same gate.

Restriction.physical_cost and Restriction.sum_cost count |S|−1 distinct earlier dual ANDs for a mandatory target S with up to three points. The support of each counted gate lies in its paid component. Different plane lines have at most one common point, ruling out double counting. Sibling gate pools are disjoint. Restriction.parent_pool charges an extra gate at a dual AND parent.

Restriction.physical_rules also transports native single-signal requirements. A mandatory target crossing both sides must have the mixed gate as its own unique minimum, must use a dual AND, and fixes both native child minima. Two distinct crossing mandatory targets cannot co-occur.

## Finite table interface

Restriction.table_sound takes a predicate Test U E k over only plane-point sets U, plane-line identifiers E, and natural budgets k. Its two premises are the singleton base and a finite binary transition quantified over disjoint nonempty child sets, their label profiles, the two child budgets, and the tag of the merge. The conclusion applies Test to the full projective plane, empty incoming requirement set, and the actual global hidden dual-AND count for a connected candidate. Restriction.Transition is the finite compatibility predicate. It includes all inherited and crossed obligations with common designated driver labels. Child budgets pay all their distinct inherited targets and are bounded above by their component size minus one. Restriction.tree_induction proves that no chronology or component birth cases have been omitted, including interleaved named outputs and merges in unrelated components.

The 7-point free-OR auxiliary lower bound, the complete finite DP values, and an unconditional 26-gate project lower bound have not been derived here. This file does not settle the posted 39-gate statement.

## Reproduction

Run the repository-bundled node executable in this directory.

    D:\pequalnp-agent\tools\node\node.exe tree-table-bundle.cjs
    D:\pequalnp-agent\tools\node\node.exe check.cjs build:Plane920TreeTable replay:Plane920TreeTable build:TreeTableAudit

The 332668-byte flat file starts with the single official import PEqualNP.Defs. SHA-256 is 01d516fd37bb993fb1d6cbbb7bd8c8253ec2ad3dbc670f266eb94a0cc97ee559. Lean 4.36.0, one process and a 3500 MiB compilation allocation cap. The checker writes the full compilation, independent leanchecker replay, and axiom-audit logs alongside the source.

The flat TreeTable build completed without warnings in 56.539 seconds. Its independent leanchecker replay took 22.293 seconds. All ten audit declarations used only propext, Classical.choice, and Quot.sound. The follow-on FreezeActual.lean identifies the top pool with precisely the original OR gates among non-output gate wires and exports Restriction.finite_lower as a direct inequality on that count.

    D:\pequalnp-agent\tools\node\node.exe check.cjs build:FreezeActual replay:FreezeActual build:FreezeActualAudit