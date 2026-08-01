# dinitz-verify — a kernel-checked refutation of the Goemans (Dinitz–Garg–Goemans) cost conjecture

`Challenge.lean` and `Submission.lean` machine-check, in **Lean 4 + mathlib**, the
July-2026 counterexample to **Goemans' cost conjecture** for single-source unsplittable
flow (Conjecture 1.3 of arXiv:2308.02651, the cost version of the Dinitz–Garg–Goemans
theorem).

The headline theorem:

```lean
-- Goemans' cost conjecture — capacities `u` present with `x ≤ u`, the digraph simple,
-- loopless and acyclic — is false over `ℚ`.
theorem goemans_cost_conjecture_false : ¬ DGGCostConjectureFull ℚ
```

`DGGCostConjectureFull` is the literature-faithful transcription of Conjecture 1.3: it
carries the arc-capacity vector `u` with the source's standing hypothesis `x ≤ u`, and it
requires the digraph to be **simple** (`Function.Injective fun a => (tail a, head a)`),
**loopless** (`∀ a, tail a ≠ head a`) and **acyclic**
(`∃ r : W → ℕ, ∀ a, r (tail a) < r (head a)`). Each of those four is an *added* hypothesis,
so the Prop being refuted is weaker than any reading of Conjecture 1.3 — and that
implication is itself kernel-checked, not asserted:

```lean
theorem DGGCostConjectureFull_of_DGGCostConjecture (R : Type) [CommRing R] [LinearOrder R]
    [IsStrictOrderedRing R] (h : DGGCostConjecture R) : DGGCostConjectureFull R
```

The bare form's refutation, `dgg_cost_conjecture_false : ¬ DGGCostConjecture ℚ`, is kept as
a corollary and as the searchable name.

This is the second entry of the "kernel referee" program, after
[`jacobian-verify`](https://github.com/jyh/jacobian-verify).

## Repository layout

The layout follows the comparator convention (as in
[`leanprover/lean-eval`](https://github.com/leanprover/lean-eval)): the statement is kept in
a separate, trusted file, so that what is being claimed can be reviewed without reading a
line of proof — and the fact that the proof discharges exactly that claim is then checked
mechanically rather than taken on trust.

| file | what it is |
|---|---|
| [`Challenge.lean`](Challenge.lean) | **the statement.** Imports only Mathlib; declares `IsWalk`, `uload` and `DGGCostConjectureFull`, and states `goemans_cost_conjecture_false` with a `sorry` body. Nothing is proved here — this is the file to review against the quotes from the primary source (given below, and in the header of `Submission.lean`). 111 lines, most of them comment. |
| [`Submission.lean`](Submission.lean) | **the proof.** `import Challenge`, then everything else, in namespace `Submission`, ending in `Submission.goemans_cost_conjecture_false`. No `sorry`. |
| [`check.py`](check.py) | `lake build`, the axiom audit, and the bridge below — plus an independent Python brute force of the instance (see "Independent cross-check"). |

Because `Submission.lean` imports `Challenge.lean`, the two refer to the *same*
`DGGCostConjectureFull` constant: the statement cannot drift between them. That the proof
discharges the stated Prop is itself type-checked, by the bridge

```lean
example : (¬ DGGCostConjectureFull ℚ) := Submission.goemans_cost_conjecture_false
```

which `check.py` elaborates. `check.py` also verifies that every theorem of
`Submission.lean` depends on no axiom outside `[propext, Classical.choice, Quot.sound]` —
in particular that none of them reaches through the `sorry` in `Challenge.lean`.

## Where the conjecture is stated — and where it is not

Read this before citing anything here.

The conjecture refuted is **not** in the 1999 Combinatorica paper of Dinitz, Garg and
Goemans. That paper is the *theorem* — an unsplittable flow with additive capacity violation
`d_max`, quoted as Theorem 1.2 in the header of `Submission.lean`. The cost strengthening is
folklore:
the primary source used here — Traub, Vargas Koch, Zenklusen, *Single-Source Unsplittable
Flows in Planar Graphs*, arXiv:2308.02651 — introduces it with the words

> "Shortly thereafter, Goemans conjectured that the following stronger, cost-enhanced
> version of the same result holds."

**with no citation**, and then states it as their Conjecture 1.3. What is refuted here is
therefore *TVZ's rendering* of that folklore conjecture, quoted verbatim in the header of
`Submission.lean`. No claim is made about any other wording of it, and the DGG99 text itself
was not consulted.

## Planarity: the instance is planar, and what that does and does not mean

The underlying undirected graph of the instance is a **subdivision of K₄**, hence planar.
Suppress the three degree-2 terminals: `t1` (edges `s–t1`, `v–t1`) becomes an `s–v` edge,
`t2` (edges `s–t2`, `w–t2`) becomes `s–w`, and `t3` (edges `u–t3`, `w–t3`) becomes `u–w`.
What is left is `{s, u, v, w}` carrying all six edges `s–u, u–v, v–w, s–v, s–w, u–w` — that
is K₄; a subdivision of a planar graph is planar. Together with acyclicity (`rank_arc`) this
makes the instance a *planar SSUF (PSSUF) instance* in the sense of TVZ Definition 1.6.

**Planarity is standard for this 7-vertex graph, and it is NOT formalized here.** It is a
hand argument, stated in this README only; nothing in `Challenge.lean` or `Submission.lean`
depends on it. That is the boundary of the kernel-checked claim.

**No conflict with the planar theorems of TVZ.** Theorem 1.7 (no costs, two-sided violation
`d_max`) and Theorem 1.8 (with costs, two-sided violation `2·d_max`) both remain satisfied
at this instance. For Theorem 1.8 the check is kernel-checked as
`two_dmax_conclusion_holds_here`: with `d_max = 15`, so `2·d_max = 30`, the all-`Z` routing
`routeZZZ = (Z1, Z2, Z3)` has cost `0 ≤ 58 = c^T x` and arc loads

| arc | `s→t1` | `s→t2` | `s→u` | `u→t3` | `u→v` | `v→t1` | `v→w` | `w→t2` | `w→t3` |
|---|---|---|---|---|---|---|---|---|---|
| `flow_P(a)` | 0 | 0 | 40 | 0 | 40 | 15 | 25 | 10 | 15 |
| `x(a)` | 10 | 6 | 24 | 10 | 14 | 5 | 9 | 4 | 5 |
| deviation from `x` | 10 | 6 | 16 | 10 | 26 | 10 | 16 | 6 | 10 |

— every deviation is at most 26 ≤ 30, on both sides. So the counterexample bites at the
`d_max` grade only, which is exactly the grade Conjecture 1.3 asserts.

**Informal corollary — not formalized, and pending ratification.** Since the instance is
planar *and* acyclic, it also shows that the `2·d_max` of TVZ Theorem 1.8 **cannot be
improved to `d_max`** for planar instances — equivalently, that Morell–Skutella
Conjecture 1.4 fails even when restricted to planar instances (it already fails in general,
Conjecture 1.4 being stronger than Conjecture 1.3). One-line justification: a routing
witnessing the improved bound would satisfy `flow_P(a) ≤ x(a) + d_max` for all `a` together
with cost `≤ 58`, and `min_cost_capacity_good` proves that every routing satisfying the
first has cost `≥ 60 > 58`; the two-sided requirement only makes such a routing harder to
find. The only unformalized ingredient is the planarity of the 7-vertex graph above.

## Provenance and credit

**The counterexample is not ours.** It was found on 2026-07-22 in a ChatGPT (GPT-5.6 Pro)
session run by **Dmitry Rybin**, who announced it publicly and published the full chat:

- Announcement: <https://x.com/DmitryRybin1/status/2079904005652893709>
  > "Dinitz-Garg-Goemans conjecture is false. This graph theory problem was open for ~30
  > years. The graph below has fractional flow cost 58. Any unsplittable flow (with
  > capacity violation <=15) has cost at least 60."
- Session transcript: <https://chatgpt.com/share/6a60b2eb-0b64-83ee-9c76-7931ca1de063>

Underlying literature:

- Y. Dinitz, N. Garg, M. X. Goemans, *On the single-source unsplittable flow problem*,
  Combinatorica **19** (1999) 17–41. (The additive-`d_max` **theorem**; the cost conjecture
  is *not* stated there — see above.)
- V. Traub, L. Vargas Koch, R. Zenklusen, *Single-Source Unsplittable Flows in Planar
  Graphs*, arXiv:2308.02651. **Used here as the primary source for the exact statement**
  (Definition 1.1, Theorem 1.2, Conjecture 1.3, and Theorems 1.7/1.8); the relevant prose is
  quoted verbatim in the header of `Submission.lean`.

**We claim no part of the discovery.** This repository contributes only the independent,
kernel-checked verification.

### The attribution chain

Traub–Vargas Koch–Zenklusen introduce the conjecture without citation. The chain does end
somewhere: Salazar–Skutella (*Single-source k-splittable min-cost flows*) cite it as
"Goemans [4]", where [4] is *"M. X. Goemans, January 2000, Personal communication."* No
document — a date and a form of transmission. Every difference among the published
restatements is downstream of that. (This provenance was traced by
[DiscreteAlias](https://github.com/DiscreteAlias); see below.)

## Related formalization, and the other wordings

**[DiscreteAlias/unsplittable-flow](https://github.com/DiscreteAlias/unsplittable-flow)**
is an independent Lean 4 formalization of the same counterexample, written without
knowledge of this one (announced five days after this repository, in the same
[Zulip thread](https://leanprover.zulipchat.com/#narrow/channel/583339-AI-authored-projects/topic/Counterexample.20to.20Dinitz-Garg-Goemans.20conjecture)).
The two developments differ in useful ways, and each covers ground the other does not:

- **The statement catalogue (theirs).** This repository is explicit that it refutes the
  TVZ rendering (Conjecture 1.3) and claims nothing about other wordings.
  DiscreteAlias surveyed the literature and found **five sources with six statements, not
  equivalent as written** (the catalogue lives in their `Statement.lean` §9, with source
  and page for each) — cost domains differ (unrestricted ℝ, ℚ≥₀, ℝ≥₀, unspecified)
  and modalities differ (two assert polynomial-time computability, four assert existence;
  refuting a poly-time claim is weaker than refuting an existence claim). Their repository
  refutes all six, including both convex-combination forms, which this one does not cover.
- **Statement generality (here).** `min_cost_capacity_good` quantifies over arbitrary
  walk-triples (no vertex-simplicity assumption is needed — though on this acyclic
  instance the two readings coincide, by the rank function `[0,1,2,3,4,4,4]`); the theorem
  is generic over ordered rings; and `check.py` bridges `Challenge` against `Submission`,
  which catches statement drift.
- **A caveat both repositories share:** both formalizations were written with Claude, so
  their agreement is *correlated, not independent*. The kernel de-correlates the proof
  layer — both proofs are machine-checked from the same three axioms — but the
  statement-choice layer is where independent judgment matters, and the six-wordings
  catalogue is exactly that de-correlation.

## The instance

DAG on 7 vertices `{s, u, v, w, t1, t2, t3}`, source `s`, terminals `t1, t2, t3` with
demands `15, 10, 15`, so `d_max = 15`. Nine arcs, written `arc (flow x_a, cost c_a)`:

| arc | `x_a` | `c_a` | | arc | `x_a` | `c_a` |
|---|---|---|---|---|---|---|
| `s→t1` | 10 | 2 | | `v→t1` | 5 | 0 |
| `s→t2` | 6 | 3 | | `v→w`  | 9 | 0 |
| `s→u`  | 24 | 0 | | `w→t2` | 4 | 0 |
| `u→t3` | 10 | 2 | | `w→t3` | 5 | 0 |
| `u→v`  | 14 | 0 | | | | |

`x` is a feasible single-source flow (checked: 40 out of `s`; 24 = 10+14 at `u`;
14 = 5+9 at `v`; 9 = 4+5 at `w`; terminal inflows 15/10/15) of cost
`c^T x = 10·2 + 6·3 + 10·2 = 58`.

There are exactly six `s`→`t_i` paths — and this is **proved from the arc list**, not
assumed:

```
E1 = [s→t1]                      Z1 = [s→u, u→v, v→t1]
E2 = [s→t2]                      Z2 = [s→u, u→v, v→w, w→t2]
E3 = [s→u, u→t3]                 Z3 = [s→u, u→v, v→w, w→t3]
```

Each `E_i` costs `d_i · 2` or `d_i · 3` (total 30 each); each `Z_i` is free. Three pairwise
overloads kill every routing that uses two or more `Z` paths:

- `Z2, Z3` → `v→w` carries 25 > 9 + 15 = 24
- `Z1, Z3` → `u→v` carries 30 > 14 + 15 = 29
- `Z1, Z2` → all 40 units are forced onto `s→u`, > 24 + 15 = 39

So at least two terminals must take an `E` path: every capacity-good routing costs ≥ 60
> 58. The bound is tight (60 is attained, e.g. by `E1, E2, Z3`).

## What is verified

### Layer B — the conjecture and its refutation (the headline)

| theorem | content |
|---|---|
| `goemans_cost_conjecture_false` | **the headline**: `¬ DGGCostConjectureFull ℚ` — the literature-faithful form (capacities `u` with `x ≤ u`; simple, loopless, acyclic digraph) is false over `ℚ` |
| `not_DGGCostConjectureFull` | the same over **every** linearly ordered commutative ring `R` |
| `not_DGGCostConjectureFull_int`, `not_DGGCostConjectureFull_rat`, `goemans_cost_conjecture_false_real` | the `ℤ`, `ℚ` and `ℝ` instances |
| `DGGCostConjectureFull_of_DGGCostConjecture` | the Full form really is the **weaker** Prop: the bare conjecture implies it, so refuting Full is the stronger result |
| `DGGCostConjectureFull_int_of`, `DGGCostConjecture_int_of` | transfer: a solution over `R` pulls back to `ℤ` along the order embedding `ℤ ↪ R` |
| `dgg_cost_conjecture_false`, `dgg_cost_conjecture_false_real`, `not_DGGCostConjecture`, `not_DGGCostConjecture_int` | the bare form `DGGCostConjecture`, refuted directly (kept as the searchable names) |
| `dgg_cost_conjecture_false_of_headline` | the bare-form refutation re-derived from the headline alone, with no second appeal to the instance |

```lean
theorem goemans_cost_conjecture_false : ¬ DGGCostConjectureFull ℚ   -- the literature's setting
theorem not_DGGCostConjectureFull (R : Type) [CommRing R] [LinearOrder R]
    [IsStrictOrderedRing R] : ¬ DGGCostConjectureFull R
theorem dgg_cost_conjecture_false : ¬ DGGCostConjecture ℚ
```

Every way in which the formal `DGGCostConjectureFull` deviates from Conjecture 1.3 makes it
**weaker or equivalent**, so refuting it refutes Conjecture 1.3 a fortiori. The full
clause-by-clause comparison is in the header of `Submission.lean`; in summary:

- we assert only **existence** of a good unsplittable flow, not polynomial-time
  computability (the conjecture claims the stronger, computational form);
- routings may be **walks**, not just simple paths — this only enlarges the candidate set
  (and is vacuous here: `the_six_walks_are_simple`);
- all the source's side conditions are **added as hypotheses** (digraph simple, loopless and
  acyclic; `x ≤ u`; terminals distinct and distinct from `s`; demands positive; `d_max`
  pinned to the maximum demand; `c ≥ 0`; `x ≥ 0`; full conservation at the source and at
  every other vertex) — and each is verified for the instance.

The bare `DGGCostConjecture` additionally quantifies over *more* instances than a
conservative reading of Conjecture 1.3 does — parallel arcs and self-loops are admitted,
cyclic digraphs are admitted, and capacities `u` are absent — i.e. in those three respects
it is **stronger**, not weaker, than the conjecture. That is precisely why the headline is
stated for the Full form, which closes all three; the instance discharges them
(`arcs_simple`, `no_self_loops`, `rank_arc`, and `u := x` with `le_refl`).

### Layer A — the concrete instance (unconditional)

| theorem | content |
|---|---|
| `path_complete` | for each `i`, the arc-lists forming a **walk** `s → t_i` are *exactly* `{pathE i, pathZ i}` — derived from the arc list via an enumeration (`walksFrom`) plus a topological rank bounding every walk by 4 arcs |
| `min_cost_capacity_good` | `∀ p : Fin 3 → List Arc, IsRouting p → CapGood p → 60 ≤ tcost p` — quantified over **arbitrary walk-triples**, not over an 8-element enum |
| `enum_check` | the 8-case kernel check behind it, `by decide` |
| `fractional_cost` | `∑ a, c a * x a = 58` |
| `flow_feasible`, `conservation_source` | `x` is a genuine feasible single-source flow |
| `exists_capacity_good` | non-vacuity: a capacity-good routing exists |
| `cost_sixty_attained`, `optimum_is_sixty` | 60 is the exact optimum, so Layer A is tight |
| `dgg_theorem_holds_here` | **positive control**: the instance satisfies clause (i) of DGG Theorem 1.2 on its own |
| `cost_clause_alone_satisfiable` | **the other positive control**: clause (ii), the cost clause, is *also* satisfiable on its own — the all-`Z` routing costs `0 ≤ 58`. Each clause of Conjecture 1.3 is individually satisfiable at this instance; only their conjunction fails |
| `two_dmax_conclusion_holds_here` | the conclusion of TVZ Theorem 1.8 (two-sided `2·d_max` + cost) holds here, so the refutation lands on the `d_max` grade only |
| `arcs_simple`, `no_self_loops`, `rank_arc` | the digraph is simple, loopless and acyclic — the refutation is not an artifact of multigraphs, loops or cycles |
| `the_six_walks_are_simple` | all six `s`→`t_i` walks are simple paths |

## What is *not* claimed

- **No claim to the discovery.** Credit for the counterexample belongs to Dmitry Rybin and
  the GPT-5.6 Pro session he ran.
- No claim about the *original* Combinatorica 1999 text: the conjecture is transcribed from
  arXiv:2308.02651 (Traub–Vargas Koch–Zenklusen), which states it as Conjecture 1.3 and
  attributes it to Goemans without citation. The DGG 1999 paper itself was not fetched.
- **Planarity of the instance is not formalized** — it is the hand argument in the planarity
  section above. Every Lean statement in the file is independent of it.
- The Morell–Skutella strengthenings (Conjectures 1.4/1.5 of the same paper) are **not**
  separately transcribed in Lean. Conjecture 1.4 (two-sided `d_max` plus cost, acyclic `G`)
  does fall with Conjecture 1.3 — the instance is acyclic, and any flow witnessing 1.4 here
  would in particular satisfy `flow_P(a) ≤ x(a) + d_max` with cost `≤ 58`, which
  `min_cost_capacity_good` excludes — but that inference is prose, not a Lean statement.
  Nothing at all is claimed about the cost-free Conjecture 1.5, nor about any weakened
  `O(d_max)` version, beyond the informal corollary flagged above.
- Nothing about generalizations of the instance (e.g. the parametrized families circulating
  on X); only this one instance is checked.

## Axiom report

Every theorem in `Submission.lean` reports at most `[propext, Classical.choice, Quot.sound]`
— the three standard mathlib axioms. There is **no `sorry`** in the proof, **no
`native_decide`**, and **no new axiom**. (The single `sorry` in the repository is the
placeholder body of the theorem stated in `Challenge.lean`; `check.py` verifies that no
theorem of `Submission.lean` reaches it — `sorryAx` appears in no axiom report.) Several
theorems come in below even the three:
`DGGCostConjectureFull_of_DGGCostConjecture` and `Dmax_is_max` use `[propext, Quot.sound]`,
`the_six_are_walks` uses only `propext`, and `the_six_walks_are_simple` uses none at all.

`Submission.lean` ends with a `#print axioms` block covering **the 35 headline results**,
emitted by the compile itself. To be precise about the scope: the two files declare 89 named
constants besides `Challenge.lean`'s placeholder (53 theorems, 33 definitions, 2 inductive
types, 1 `Decidable` instance); the block covers 35 of the 53 theorems — every result named
anywhere in this README — and the 18 it omits are helper lemmas that the covered ones depend
on, so their axiom footprint is subsumed (`#print axioms` reports transitive dependencies).

## How to reproduce

The two files are self-contained on top of mathlib — `Challenge.lean` imports only Mathlib,
`Submission.lean` imports only `Challenge`; "self-contained" means they declare everything
they use on top of mathlib, not that they run without mathlib. Two ways to check them:

**1. With the included lakefile** (fetches mathlib; needs
[elan](https://github.com/leanprover/elan)), in this directory:

```sh
lake exe cache get   # fetch the mathlib build cache
lake build           # kernel-checks everything
python3 check.py     # build + axiom audit + the statement-identity bridge
```

**2. Against any project already pinning the same mathlib revision** — the fast path, and
the one used during development (here, the `salt` project):

```sh
cd /path/to/salt
D=/path/to/dinitz-verify; mkdir -p /tmp/dinitz
~/.elan/bin/lake env lean --root="$D" -o /tmp/dinitz/Challenge.olean "$D/Challenge.lean"
~/.elan/bin/lake env bash -c "LEAN_PATH=/tmp/dinitz:\$LEAN_PATH lean --root=$D $D/Submission.lean"
```

Either way the expected output is the 35 `#print axioms` lines, plus one `declaration uses
'sorry'` warning on the placeholder in `Challenge.lean` and nothing else — zero errors, no
other warning. Route 2 takes a few seconds wall-clock (4–16 s here, depending on how
warm the OS file cache is, with mathlib already built); the verification itself is
kernel-cheap because all arithmetic is over `ℤ` and every `decide` ranges over a handful of
cases.

Pinned: `leanprover/lean4:v4.32.0-rc1`; mathlib
`360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56`.

## Independent cross-check

`check.py` opens with a small, dependency-free Python brute force of the same claims
(conservation, `d_max`, fractional cost, exhaustive walk enumeration to length 8, all 8
routings) — run it on its own with `python3 check.py --brute`. It agrees with the Lean
development:

```
conservation OK; dmax = 15
fractional cost = 58
t1 [('st1',), ('su', 'uv', 'vt1')]
t2 [('st2',), ('su', 'uv', 'vw', 'wt2')]
t3 [('su', 'ut3'), ('su', 'uv', 'vw', 'wt3')]
capacity-good routings: 4   min unsplittable cost: 60
```

It is a sanity oracle only; the Lean files are the referee. The rest of `check.py` runs the
Lean gates listed under "Repository layout": `lake build`, the axiom audit of all 35
reported theorems, and the statement-identity bridge.

## Credits and license

The mathematics is due to Dmitry Rybin and the GPT-5.6 Pro session he ran (2026-07-22); the
conjecture's statement is quoted from Traub–Vargas Koch–Zenklusen, arXiv:2308.02651. This
verification: Jason Hickey (with Claude). The author thanks Katherine Schlitz for
bringing the announcement to his attention. Built on
[mathlib](https://github.com/leanprover-community/mathlib4), the Lean mathematical library,
by the mathlib community. License: Apache-2.0 (see `LICENSE`).
