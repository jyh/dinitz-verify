/-
# A kernel-checked refutation of the Goemans (Dinitz–Garg–Goemans) cost conjecture
  for single-source unsplittable flow.
## Where the statement lives

This file carries the *proof*.  The Prop it refutes — `DGGCostConjectureFull` — together
with the two definitions it is phrased with (`IsWalk` and `uload`), lives in
`Challenge.lean`, which imports nothing but Mathlib and proves nothing; that is the file to
read against the quotes below.  The two files share a single `DGGCostConjectureFull`
constant, so what is proved here is literally what is stated there, and `check.py`
type-checks that bridge.  See the README's "Repository layout".

## Provenance

The counterexample verified here is **not ours**.  It was found on 2026-07-22 in a
ChatGPT (GPT-5.6 Pro) session run by Dmitry Rybin, and announced by him on X:

    "Dinitz-Garg-Goemans conjecture is false.  This graph theory problem was open for
     ~30 years.  The graph below has fractional flow cost 58.  Any unsplittable flow
     (with capacity violation <= 15) has cost at least 60."
    -- https://x.com/DmitryRybin1/status/2079904005652893709
       chat: https://chatgpt.com/share/6a60b2eb-0b64-83ee-9c76-7931ca1de063

This file contributes only the machine-checked verification.

## The conjecture, from the primary source

Traub, Vargas Koch, Zenklusen, *Single-Source Unsplittable Flows in Planar Graphs*,
arXiv:2308.02651v1, p.1-2, state the setting and the conjecture as follows (verbatim):

> **Definition 1.1** (Single-source unsplittable flow (SSUF) instance).  *A single-source
> unsplittable flow (SSUF) instance is a tuple (G = (V, A), s, T, d, x), where G is a
> directed graph with source s in V, terminals T subset of V with corresponding demands
> d in Q^T_{>=0}, and a splittable flow x in Q^A_{>=0}.  The source s and terminals T are
> assumed to be distinct.*

> **Theorem 1.2** ([DGG99]).  *Given an SSUF instance (G, s, T, u, d, x), one can compute in
> polynomial time an unsplittable flow P = {P^t}_{t in T} with flow_P(a) <= x(a) + d_max
> for all a in A.*

> **Conjecture 1.3** (Goemans).  *Given an SSUF instance (G, s, T, u, d, x) and a cost
> vector c in Q^A_{>=0}, one can compute in polynomial time an unsplittable flow
> P = {P^t}_{t in T} with*
> *(i)  flow_P(a) <= x(a) + d_max for all a in A, and*
> *(ii) cost at most c^T x, i.e., sum_{a in A} c(a) flow_P(a) <= sum_{a in A} c(a) x(a).*

Supporting definitions from the same source (p.1-2):

> an *unsplittable flow*, i.e., such a family P = {P^t}_{t in T} of paths
> [one s-t path P^t for each terminal t]

> flow_P(a) := sum_{t in T : a in P^t} d_t

> x(delta^+(v)) - x(delta^-(v)) = sum_{t in T} d_t if v = s;  -d_v if v in T;
>                                 0 if v in V \ ({s} u T)

> d_max := max{d_t : t in T} is the largest demand

> Note that one can assume G to be acyclic in Conjecture 1.3.

## How the Props below relate to Conjecture 1.3

Section 5 states *two* transcriptions of Conjecture 1.3:

* `DGGCostConjectureFull` -- the literature-faithful form.  Capacities `u` are present
  together with the source's standing hypothesis `x <= u`, and the digraph is required to
  be **simple** (`Function.Injective fun a => (tail a, head a)`), **loopless**
  (`∀ a, tail a ≠ head a`) and **acyclic**
  (`∃ r : W → ℕ, ∀ a, r (tail a) < r (head a)`).
* `DGGCostConjecture` -- the bare form: the same statement with those four hypotheses
  dropped.

`DGGCostConjectureFull` is obtained from `DGGCostConjecture` by *adding* hypotheses and
nothing else, so it is the weaker Prop and its refutation is the stronger result.  That
implication is itself kernel-checked, not asserted:
`DGGCostConjectureFull_of_DGGCostConjecture : DGGCostConjecture R → DGGCostConjectureFull R`.
The headline theorem is therefore `goemans_cost_conjecture_false : ¬ DGGCostConjectureFull ℚ`
(with `dgg_cost_conjecture_false : ¬ DGGCostConjecture ℚ` retained as a corollary and as
the searchable name).

Every deviation of `DGGCostConjectureFull` from Conjecture 1.3 is in the direction that
makes our stated Prop **weaker or equivalent**, so that refuting it refutes Conjecture 1.3
a fortiori:

* **Existence, not polynomial-time computability.**  Conjecture 1.3 asserts that a good
  unsplittable flow can be *computed in polynomial time*; we assert only that one
  *exists*.  Non-existence therefore refutes the stronger computational claim too.
* **Walks, not simple paths.**  `IsWalk` allows a routing to repeat vertices/arcs.  This
  only enlarges the set of candidate routings, making the existential easier to satisfy.
  (`the_six_walks_are_simple` records that on this instance every s-t_i walk is in fact a
  simple path, so the distinction is vacuous here.)
* **Extra hypotheses are *added*, never removed**: the digraph simple, loopless and
  acyclic; `x <= u`; terminals distinct (`Function.Injective term`), terminals distinct
  from the source, demands strictly positive, `dmax` pinned to be exactly the maximum
  demand, costs nonnegative, `x` nonnegative, full flow conservation at the source and at
  every other vertex.  Adding hypotheses weakens the conjecture.  All of them are verified
  for the counterexample instance below.
* **Coefficient ring.**  Conjecture 1.3 is over `Q`.  Both Props are stated over an
  arbitrary linearly ordered commutative ring `R`; `not_DGGCostConjectureFull` refutes the
  faithful form for *every* such `R`, in particular for `Z`, `Q` and `R`.  (The
  counterexample is integral; `DGGCostConjectureFull_int_of` transfers a general-`R`
  solution back to `Z`.)
* `DecidableEq` hypotheses are used only to write the indicator sums; they are free for
  the finite types involved.

### Why the bare form alone would not suffice: its three ∀-widenings

`DGGCostConjecture` quantifies over *more* instances than a conservative reading of
Conjecture 1.3 does, so in these three respects the bare form is **stronger**, not weaker,
than the conjecture -- which is exactly why the headline is stated for the Full form:

* **parallel arcs and self-loops are admitted.**  `E` is an arbitrary finite type with
  endpoint maps `tail`, `head`, so two arcs may share both endpoints and an arc may be a
  loop; a reader who takes `G = (V, A)` to mean a simple loopless digraph would not grant
  those instances.
* **no acyclicity restriction.**  The primary source notes that `G` may be assumed acyclic
  in Conjecture 1.3; the bare form ranges over cyclic digraphs too.
* **capacities `u` dropped.**  An SSUF instance of Conjecture 1.3 carries a capacity vector
  `u` with `x <= u`; the bare form has no `u` at all.  (In substance this is vacuous --
  `u := x` always works, and is the worst case the source explicitly identifies -- but the
  Full form restores `u` so that no reading is left uncovered.)

`DGGCostConjectureFull` re-adds all four hypotheses, and the counterexample instance
satisfies every one of them: `arcs_simple`, `no_self_loops`, `rank_arc` (a topological
rank), and `u := x` with `le_refl`.

## What is verified

* `goemans_cost_conjecture_false` -- **the headline.**  Layer B: Goemans' cost conjecture,
  in its literature-faithful form `DGGCostConjectureFull` (capacities restored; simple,
  loopless, acyclic digraph), is false over `ℚ` -- and, via `not_DGGCostConjectureFull`,
  over every linearly ordered commutative ring.
* `DGGCostConjectureFull_of_DGGCostConjecture` -- the Full form really is the weaker Prop,
  so `¬ DGGCostConjectureFull` implies `¬ DGGCostConjecture`.  (`dgg_cost_conjecture_false`
  is kept, and is also proved directly from the instance; the derivation from the headline
  alone is `dgg_cost_conjecture_false_of_headline`.)
* `arcs_simple`, `no_self_loops`, `rank_arc` -- the instance is a *simple, loopless,
  acyclic* digraph, so the refutation is not an artifact of admitting multigraphs, loops,
  or cycles (the primary source notes `G` may be assumed acyclic in Conjecture 1.3).
* `path_complete` -- the six s-t_i paths are *exactly* the s-t_i walks of the arc list.
* `min_cost_capacity_good` -- Layer A, unconditional: *every* routing of the three demands
  along *arbitrary* walks from `s` that keeps every arc load within `x(a) + 15` has cost at
  least 60.  Path-completeness (only six s-t_i walks exist) is proved, not assumed.
* `fractional_cost` -- the fractional flow costs 58.
* `flow_feasible`, `conservation_source` -- `x` really is a feasible single-source flow.
* `exists_capacity_good`, `cost_sixty_attained` -- non-vacuity: capacity-good routings
  exist, and 60 is attained, so Layer A is tight.
* `dgg_theorem_holds_here`, `cost_clause_alone_satisfiable` -- each clause of Conjecture 1.3
  is *individually* satisfiable at this instance (clause (i) by the all-`E` routing, clause
  (ii) by the all-`Z` routing at cost 0); only their conjunction fails.
* `two_dmax_conclusion_holds_here` -- the conclusion of Theorem 1.8 of the primary source
  (planar instances, two-sided violation `2*d_max`, with the cost bound) *is* satisfied
  here, so the refutation lands on the `d_max` grade only and does not conflict with that
  theorem.  (The instance is planar -- a subdivision of `K₄`; that fact is stated in the
  README and is *not* formalized.)

No `sorry`, no `native_decide`, no new axioms; see the `#print axioms` block at the end.
-/
import Challenge

set_option maxHeartbeats 2000000

namespace Submission

open DGG

/-! ## 0.  Walks in a digraph (generic) -/

section Walks

variable {W E : Type}

@[simp] theorem IsWalk_nil (tail head : E → W) (x y : W) :
    IsWalk tail head x [] y ↔ x = y := Iff.rfl

@[simp] theorem IsWalk_cons (tail head : E → W) (x : W) (e : E) (l : List E) (y : W) :
    IsWalk tail head x (e :: l) y ↔ (tail e = x ∧ IsWalk tail head (head e) l y) := Iff.rfl

/-- Boolean decision procedure for `IsWalk` (kernel-friendly). -/
def walkB [DecidableEq W] (tail head : E → W) : W → List E → W → Bool
  | x, [], y => decide (x = y)
  | x, e :: l, y => decide (tail e = x) && walkB tail head (head e) l y

theorem walkB_iff [DecidableEq W] (tail head : E → W) (x : W) (l : List E) (y : W) :
    walkB tail head x l y = true ↔ IsWalk tail head x l y := by
  induction l generalizing x with
  | nil => simp [walkB]
  | cons e l ih => simp [walkB, ih]

instance instDecidableIsWalk [DecidableEq W] (tail head : E → W) (x : W) (l : List E) (y : W) :
    Decidable (IsWalk tail head x l y) :=
  decidable_of_iff _ (walkB_iff tail head x l y)

end Walks

/-! ## 1.  The counterexample instance -/

/-- The seven vertices. -/
inductive Vtx | s | u | v | w | t1 | t2 | t3
  deriving DecidableEq, Fintype, Repr

/-- The nine arcs. -/
inductive Arc | st1 | st2 | su | ut3 | uv | vt1 | vw | wt2 | wt3
  deriving DecidableEq, Fintype, Repr

def tl : Arc → Vtx
  | .st1 => .s  | .st2 => .s  | .su  => .s
  | .ut3 => .u  | .uv  => .u
  | .vt1 => .v  | .vw  => .v
  | .wt2 => .w  | .wt3 => .w

def hd : Arc → Vtx
  | .st1 => .t1 | .st2 => .t2 | .su  => .u
  | .ut3 => .t3 | .uv  => .v
  | .vt1 => .t1 | .vw  => .w
  | .wt2 => .t2 | .wt3 => .t3

/-- The fractional (splittable) flow `x`. -/
def xf : Arc → ℤ
  | .st1 => 10 | .st2 => 6 | .su  => 24
  | .ut3 => 10 | .uv  => 14
  | .vt1 => 5  | .vw  => 9
  | .wt2 => 4  | .wt3 => 5

/-- The cost vector `c`. -/
def cf : Arc → ℤ
  | .st1 => 2 | .st2 => 3 | .su  => 0
  | .ut3 => 2 | .uv  => 0
  | .vt1 => 0 | .vw  => 0
  | .wt2 => 0 | .wt3 => 0

/-- Terminal of commodity `i`. -/
def trm (i : Fin 3) : Vtx := if i = 0 then .t1 else if i = 1 then .t2 else .t3

/-- Demand of commodity `i`. -/
def dem (i : Fin 3) : ℤ := if i = 0 then 15 else if i = 1 then 10 else 15

/-- `d_max`, the largest demand. -/
def Dmax : ℤ := 15

theorem Dmax_is_max : (∀ i, dem i ≤ Dmax) ∧ (∃ i, dem i = Dmax) := by decide

theorem dem_pos : ∀ i, 0 < dem i := by decide

theorem cf_nonneg : ∀ a, 0 ≤ cf a := by decide

theorem xf_nonneg : ∀ a, 0 ≤ xf a := by decide

theorem trm_injective : Function.Injective trm := by decide

theorem trm_ne_source : ∀ i, trm i ≠ Vtx.s := by decide

/-- The instance is a *simple* digraph: no two arcs share both endpoints. -/
theorem arcs_simple : Function.Injective (fun a : Arc => (tl a, hd a)) := by decide

/-- The instance has no self-loops. -/
theorem no_self_loops : ∀ a : Arc, tl a ≠ hd a := by decide

/-- Flow conservation at every vertex other than the source: inflow − outflow = demand
absorbed there (which is `0` at non-terminals). -/
theorem flow_feasible : ∀ z : Vtx, z ≠ Vtx.s →
    (∑ a : Arc, if hd a = z then xf a else 0) - (∑ a : Arc, if tl a = z then xf a else 0)
      = ∑ i : Fin 3, if trm i = z then dem i else 0 := by decide

/-- Flow conservation at the source: net outflow = total demand. -/
theorem conservation_source :
    (∑ a : Arc, if tl a = Vtx.s then xf a else 0)
      - (∑ a : Arc, if hd a = Vtx.s then xf a else 0) = ∑ i : Fin 3, dem i := by decide

/-! ## 2.  Loads and costs -/

/-- A routing: one walk from `s` to `t_i` per commodity `i`. -/
def IsRouting (p : Fin 3 → List Arc) : Prop :=
  ∀ i : Fin 3, IsWalk tl hd Vtx.s (p i) (trm i)

/-- Capacity-good: every arc load stays within `x(a) + d_max`. -/
def CapGood (p : Fin 3 → List Arc) : Prop :=
  ∀ a : Arc, uload dem p a ≤ xf a + Dmax

/-- Cost of a routing. -/
def tcost (p : Fin 3 → List Arc) : ℤ := ∑ a : Arc, cf a * uload dem p a

/-- The cost of the fractional flow. -/
theorem fractional_cost : (∑ a : Arc, cf a * xf a) = 58 := by decide

/-! ## 3.  Path completeness: the digraph has exactly six s-t_i walks -/

def allArcs : List Arc := [.st1, .st2, .su, .ut3, .uv, .vt1, .vw, .wt2, .wt3]

theorem mem_allArcs : ∀ e : Arc, e ∈ allArcs := by decide

/-- Arcs leaving `x`. -/
def outOf (x : Vtx) : List Arc := allArcs.filter (fun e => decide (tl e = x))

theorem mem_outOf {e : Arc} {x : Vtx} (h : tl e = x) : e ∈ outOf x :=
  List.mem_filter.mpr ⟨mem_allArcs e, by simp [h]⟩

/-- All walks of length at most `n` starting at `x`, paired with their endpoint. -/
def walksFrom : ℕ → Vtx → List (List Arc × Vtx)
  | 0, x => [([], x)]
  | n + 1, x => ([], x) :: (outOf x).flatMap (fun e =>
      (walksFrom n (hd e)).map (fun q => (e :: q.1, q.2)))

theorem walksFrom_complete : ∀ (n : ℕ) (x : Vtx) (l : List Arc) (y : Vtx),
    l.length ≤ n → IsWalk tl hd x l y → (l, y) ∈ walksFrom n x := by
  intro n
  induction n with
  | zero =>
    intro x l y hl hw
    cases l with
    | nil => obtain rfl : x = y := hw; simp [walksFrom]
    | cons e l => simp at hl
  | succ n ih =>
    intro x l y hl hw
    cases l with
    | nil => obtain rfl : x = y := hw; simp [walksFrom]
    | cons e l =>
      obtain ⟨he, hw'⟩ := hw
      have hl' : l.length ≤ n := by simp at hl; omega
      have hmem := ih (hd e) l y hl' hw'
      simp only [walksFrom, List.mem_cons, List.mem_flatMap, List.mem_map]
      exact Or.inr ⟨e, mem_outOf he, (l, y), hmem, rfl⟩

/-- A topological rank certifying acyclicity. -/
def rank : Vtx → ℕ
  | .s => 0 | .u => 1 | .v => 2 | .w => 3 | .t1 => 4 | .t2 => 4 | .t3 => 4

theorem rank_arc : ∀ e : Arc, rank (tl e) < rank (hd e) := by decide

theorem rank_le_four : ∀ z : Vtx, rank z ≤ 4 := by decide

theorem walk_len : ∀ (x : Vtx) (l : List Arc) (y : Vtx),
    IsWalk tl hd x l y → l.length + rank x ≤ rank y := by
  intro x l
  induction l generalizing x with
  | nil => intro y hw; obtain rfl : x = y := hw; simp
  | cons e l ih =>
    intro y hw
    obtain ⟨he, hw'⟩ := hw
    have h1 := rank_arc e
    have h2 := ih (hd e) y hw'
    subst he
    simp only [List.length_cons] at *
    omega

theorem walk_from_s_mem (l : List Arc) (y : Vtx) (h : IsWalk tl hd Vtx.s l y) :
    (l, y) ∈ walksFrom 4 Vtx.s := by
  have hb := walk_len _ _ _ h
  have h4 := rank_le_four y
  have h0 : rank Vtx.s = 0 := rfl
  refine walksFrom_complete 4 _ _ _ ?_ h
  omega

/-- The explicit enumeration of all walks of length ≤ 4 out of the source. -/
theorem walksFrom_s_eq : walksFrom 4 Vtx.s =
    [([], Vtx.s),
     ([Arc.st1], Vtx.t1),
     ([Arc.st2], Vtx.t2),
     ([Arc.su], Vtx.u),
     ([Arc.su, Arc.ut3], Vtx.t3),
     ([Arc.su, Arc.uv], Vtx.v),
     ([Arc.su, Arc.uv, Arc.vt1], Vtx.t1),
     ([Arc.su, Arc.uv, Arc.vw], Vtx.w),
     ([Arc.su, Arc.uv, Arc.vw, Arc.wt2], Vtx.t2),
     ([Arc.su, Arc.uv, Arc.vw, Arc.wt3], Vtx.t3)] := by rfl

/-- The two s-t1 paths. -/
def E1 : List Arc := [.st1]
def Z1 : List Arc := [.su, .uv, .vt1]
/-- The two s-t2 paths. -/
def E2 : List Arc := [.st2]
def Z2 : List Arc := [.su, .uv, .vw, .wt2]
/-- The two s-t3 paths. -/
def E3 : List Arc := [.su, .ut3]
def Z3 : List Arc := [.su, .uv, .vw, .wt3]

theorem paths_t1 (l : List Arc) (h : IsWalk tl hd Vtx.s l Vtx.t1) : l = E1 ∨ l = Z1 := by
  have hm := walk_from_s_mem l Vtx.t1 h
  rw [walksFrom_s_eq] at hm
  simpa [E1, Z1] using hm

theorem paths_t2 (l : List Arc) (h : IsWalk tl hd Vtx.s l Vtx.t2) : l = E2 ∨ l = Z2 := by
  have hm := walk_from_s_mem l Vtx.t2 h
  rw [walksFrom_s_eq] at hm
  simpa [E2, Z2] using hm

theorem paths_t3 (l : List Arc) (h : IsWalk tl hd Vtx.s l Vtx.t3) : l = E3 ∨ l = Z3 := by
  have hm := walk_from_s_mem l Vtx.t3 h
  rw [walksFrom_s_eq] at hm
  simpa [E3, Z3] using hm

/-- The cheap ("E") path for commodity `i`. -/
def pathE (i : Fin 3) : List Arc := if i = 0 then E1 else if i = 1 then E2 else E3
/-- The zero-cost ("Z") path for commodity `i`. -/
def pathZ (i : Fin 3) : List Arc := if i = 0 then Z1 else if i = 1 then Z2 else Z3

/-- **Path completeness.**  For each commodity `i`, the arc-lists forming a walk from the
source `s` to the terminal `t_i` are *exactly* the two listed paths.  This is derived from
the arc list — via the enumeration `walksFrom` together with the topological rank bounding
every walk by 4 arcs — and not assumed. -/
theorem path_complete (i : Fin 3) (l : List Arc) :
    IsWalk tl hd Vtx.s l (trm i) ↔ (l = pathE i ∨ l = pathZ i) := by
  constructor
  · intro h
    fin_cases i
    · exact paths_t1 l h
    · exact paths_t2 l h
    · exact paths_t3 l h
  · intro h
    fin_cases i <;> rcases h with rfl | rfl <;> decide

/-- Conversely, all six really are walks. -/
theorem the_six_are_walks :
    IsWalk tl hd Vtx.s E1 Vtx.t1 ∧ IsWalk tl hd Vtx.s Z1 Vtx.t1 ∧
    IsWalk tl hd Vtx.s E2 Vtx.t2 ∧ IsWalk tl hd Vtx.s Z2 Vtx.t2 ∧
    IsWalk tl hd Vtx.s E3 Vtx.t3 ∧ IsWalk tl hd Vtx.s Z3 Vtx.t3 := by decide

/-- The vertex sequence visited by a walk. -/
def vseq (x : Vtx) (l : List Arc) : List Vtx := x :: l.map hd

/-- Each of the six s-t_i walks is a *simple path* (no repeated vertex), so restricting
Conjecture 1.3 to simple paths would not help. -/
theorem the_six_walks_are_simple :
    (vseq Vtx.s E1).Nodup ∧ (vseq Vtx.s Z1).Nodup ∧
    (vseq Vtx.s E2).Nodup ∧ (vseq Vtx.s Z2).Nodup ∧
    (vseq Vtx.s E3).Nodup ∧ (vseq Vtx.s Z3).Nodup := by decide

/-! ## 4.  Layer A: the eight-case check and the cost lower bound -/

/-- The load written as a function of the three chosen paths. -/
def load3 (q0 q1 q2 : List Arc) (a : Arc) : ℤ :=
  (if a ∈ q0 then dem 0 else 0) + (if a ∈ q1 then dem 1 else 0) + (if a ∈ q2 then dem 2 else 0)

def tcost3 (q0 q1 q2 : List Arc) : ℤ := ∑ a : Arc, cf a * load3 q0 q1 q2 a

theorem uload_eq (p : Fin 3 → List Arc) (a : Arc) :
    uload dem p a = load3 (p 0) (p 1) (p 2) a := by
  simp only [uload, load3, Fin.sum_univ_three]

theorem tcost_eq (p : Fin 3 → List Arc) : tcost p = tcost3 (p 0) (p 1) (p 2) :=
  Finset.sum_congr rfl fun a _ => by rw [uload_eq]

/-- **The eight-case kernel check.**  Over the eight combinations of path choices, every
capacity-good one costs at least 60. -/
theorem enum_check : ∀ q0 ∈ [E1, Z1], ∀ q1 ∈ [E2, Z2], ∀ q2 ∈ [E3, Z3],
    (∀ a : Arc, load3 q0 q1 q2 a ≤ xf a + Dmax) → 60 ≤ tcost3 q0 q1 q2 := by decide

/-- **Layer A (main).**  Every unsplittable routing of the three demands along arbitrary
walks out of `s` whose arc loads stay within `x(a) + d_max` costs at least 60 — strictly
more than the fractional cost 58. -/
theorem min_cost_capacity_good (p : Fin 3 → List Arc) (hr : IsRouting p) (hc : CapGood p) :
    60 ≤ tcost p := by
  have h0 : p 0 ∈ [E1, Z1] := by
    have := paths_t1 (p 0) (hr 0); simpa using this
  have h1 : p 1 ∈ [E2, Z2] := by
    have := paths_t2 (p 1) (hr 1); simpa using this
  have h2 : p 2 ∈ [E3, Z3] := by
    have := paths_t3 (p 2) (hr 2); simpa using this
  rw [tcost_eq]
  refine enum_check _ h0 _ h1 _ h2 (fun a => ?_)
  have := hc a
  rwa [uload_eq] at this

/-! ### Non-vacuity and tightness -/

/-- Route every commodity on its "expensive" path. -/
def routeEEE : Fin 3 → List Arc := fun i => if i = 0 then E1 else if i = 1 then E2 else E3

/-- Route `t1`, `t2` expensively and `t3` on the zero-cost path: cost exactly 60. -/
def routeEEZ : Fin 3 → List Arc := fun i => if i = 0 then E1 else if i = 1 then E2 else Z3

theorem exists_capacity_good : IsRouting routeEEE ∧ CapGood routeEEE := by
  constructor
  · intro i; revert i; decide
  · intro a; revert a; decide

theorem cost_sixty_attained :
    IsRouting routeEEZ ∧ CapGood routeEEZ ∧ tcost routeEEZ = 60 := by
  refine ⟨?_, ?_, by decide⟩
  · intro i; revert i; decide
  · intro a; revert a; decide

/-- **Positive control.**  The instance *does* satisfy the conclusion of DGG Theorem 1.2
(the capacity clause (i) on its own): an unsplittable routing with
`flow_P(a) ≤ x(a) + d_max` for every arc `a` exists.  So the refutation isolates
clause (ii), the cost clause — it is not an artifact of an unsatisfiable capacity
requirement. -/
theorem dgg_theorem_holds_here :
    ∃ p : Fin 3 → List Arc, IsRouting p ∧ ∀ a : Arc, uload dem p a ≤ xf a + Dmax :=
  ⟨routeEEE, exists_capacity_good.1, exists_capacity_good.2⟩

/-- Route every commodity on its zero-cost path. -/
def routeZZZ : Fin 3 → List Arc := fun i => if i = 0 then Z1 else if i = 1 then Z2 else Z3

/-- **Positive control for the other clause.**  Clause (ii) of Conjecture 1.3 -- the cost
clause -- is *also* satisfiable on its own here: the all-`Z` routing costs `0 ≤ 58 = c^T x`.
So neither clause is individually unsatisfiable at this instance; only their conjunction
fails, which is what makes the instance a counterexample to Conjecture 1.3 rather than to
either half of it. -/
theorem cost_clause_alone_satisfiable :
    IsRouting routeZZZ ∧ tcost routeZZZ ≤ ∑ a : Arc, cf a * xf a := by
  refine ⟨?_, ?_⟩
  · intro i; revert i; decide
  · decide

/-- **No conflict with the primary source's planar theorems.**  The underlying undirected
graph of this instance is planar (a subdivision of `K₄` — see the README; planarity is
*not* formalized here), and the instance is acyclic, so it is a PSSUF instance in the sense
of arXiv:2308.02651.  Theorem 1.8 of that paper grants a two-sided violation of `2·d_max`
together with the cost bound, and its conclusion *is* satisfied here: the all-`Z` routing
keeps every arc load within `2·d_max = 30` of `x` on both sides and costs `0 ≤ 58`.  The
counterexample therefore refutes the `d_max` grade only, exactly as Conjecture 1.3 states
it. -/
theorem two_dmax_conclusion_holds_here :
    IsRouting routeZZZ ∧
    (∀ a : Arc, xf a - 2 * Dmax ≤ uload dem routeZZZ a ∧
      uload dem routeZZZ a ≤ xf a + 2 * Dmax) ∧
    tcost routeZZZ ≤ ∑ a : Arc, cf a * xf a := by
  refine ⟨?_, ?_, ?_⟩
  · intro i; revert i; decide
  · intro a; revert a; decide
  · decide

/-- 60 is exactly the optimum: it is a lower bound and it is attained. -/
theorem optimum_is_sixty :
    (∀ p : Fin 3 → List Arc, IsRouting p → CapGood p → 60 ≤ tcost p) ∧
    (∃ p : Fin 3 → List Arc, IsRouting p ∧ CapGood p ∧ tcost p = 60) :=
  ⟨min_cost_capacity_good, routeEEZ, cost_sixty_attained.1, cost_sixty_attained.2.1,
    cost_sixty_attained.2.2⟩

/-! ## 5.  Layer B: the conjecture, and its refutation -/

/-- **Goemans' cost conjecture** (Dinitz–Garg–Goemans / SSUF), Conjecture 1.3 of
arXiv:2308.02651, stated over a linearly ordered commutative ring `R`.

Read: for every finite digraph `(W, E)` with arc endpoints `tail`, `head`, every source
`src`, every finite family of commodities `K` with distinct terminals `term k ≠ src` and
positive demands `d k`, every `dmax` equal to the maximum demand, every nonnegative cost
vector `c` and every nonnegative feasible single-source flow `x` routing the demands,
there is an unsplittable routing `P` (one walk per commodity) with

* `flow_P(a) ≤ x(a) + dmax` for every arc `a`, and
* `c^T flow_P ≤ c^T x`.

See the header of this file for the clause-by-clause comparison with the primary source;
every deviation weakens the statement, so `not_DGGCostConjecture` refutes Conjecture 1.3. -/
def DGGCostConjecture (R : Type) [CommRing R] [LinearOrder R] [IsStrictOrderedRing R] : Prop :=
  ∀ (W E K : Type) [Fintype W] [DecidableEq W] [Fintype E] [DecidableEq E] [Fintype K]
    (tail head : E → W) (src : W) (term : K → W) (d : K → R) (dmax : R) (x c : E → R),
    -- the terminals are distinct from each other and from the source
    Function.Injective term →
    (∀ k, term k ≠ src) →
    -- demands are positive and `dmax` is the maximum demand
    (∀ k, 0 < d k) →
    (∀ k, d k ≤ dmax) →
    (∃ k, d k = dmax) →
    -- nonnegative costs and a nonnegative flow
    (∀ a, 0 ≤ c a) →
    (∀ a, 0 ≤ x a) →
    -- `x` is a feasible single-source flow for the demands
    (∀ z : W, z ≠ src →
      (∑ a : E, if head a = z then x a else 0) - (∑ a : E, if tail a = z then x a else 0)
        = ∑ k : K, if term k = z then d k else 0) →
    ((∑ a : E, if tail a = src then x a else 0)
        - (∑ a : E, if head a = src then x a else 0) = ∑ k : K, d k) →
    -- conclusion
    ∃ P : K → List E,
      (∀ k, IsWalk tail head src (P k) (term k)) ∧
      (∀ a, uload d P a ≤ x a + dmax) ∧
      (∑ a : E, c a * uload d P a) ≤ ∑ a : E, c a * x a

/-- **The Full form is the weaker Prop.**  It is `DGGCostConjecture` with four hypotheses
added (simple, loopless, acyclic, `x ≤ u`), so the bare conjecture implies it.  Hence
`¬ DGGCostConjectureFull` is strictly the stronger statement, and it implies
`¬ DGGCostConjecture`. -/
theorem DGGCostConjectureFull_of_DGGCostConjecture
    (R : Type) [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
    (h : DGGCostConjecture R) : DGGCostConjectureFull R := by
  intro W E K _ _ _ _ _ tail head src term d dmax x c _u _hsimple _hloop _hacyc _hxu
    hinj hns hpos hle hex hc hx hcons hsrc
  exact h W E K tail head src term d dmax x c hinj hns hpos hle hex hc hx hcons hsrc

section Transfer

variable {R : Type} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]

omit [LinearOrder R] [IsStrictOrderedRing R] in
private theorem cast_sum_ite {ι : Type} [Fintype ι] (P : ι → Prop) [DecidablePred P]
    (f : ι → ℤ) :
    (∑ i : ι, if P i then ((f i : R)) else 0) = (((∑ i : ι, if P i then f i else 0 : ℤ) : R)) := by
  rw [Int.cast_sum]
  exact Finset.sum_congr rfl fun i _ => by split <;> simp

omit [LinearOrder R] [IsStrictOrderedRing R] in
private theorem uload_cast {K E : Type} [Fintype K] [DecidableEq E]
    (d : K → ℤ) (P : K → List E) (a : E) :
    uload (fun k => ((d k : R))) P a = ((uload d P a : ℤ) : R) := by
  simp only [uload]
  exact cast_sum_ite (R := R) (fun k => a ∈ P k) d

/-- If the conjecture held over `R`, it would hold over `ℤ` (an integral instance is an
`R`-instance, and the conclusion pulls back along the order embedding `ℤ ↪ R`). -/
theorem DGGCostConjecture_int_of (h : DGGCostConjecture R) : DGGCostConjecture ℤ := by
  intro W E K _ _ _ _ _ tail head src term d dmax x c hinj hns hpos hle hex hc hx hcons hsrc
  obtain ⟨P, hw, hcap, hcost⟩ :=
    h W E K tail head src term (fun k => ((d k : R))) ((dmax : R))
      (fun a => ((x a : R))) (fun a => ((c a : R)))
      hinj hns
      (fun k => by exact_mod_cast hpos k)
      (fun k => by exact_mod_cast hle k)
      (by obtain ⟨k, hk⟩ := hex; exact ⟨k, by exact_mod_cast hk⟩)
      (fun a => by exact_mod_cast hc a)
      (fun a => by exact_mod_cast hx a)
      (fun z hz => by
        rw [cast_sum_ite, cast_sum_ite, cast_sum_ite]
        exact_mod_cast congrArg (fun t : ℤ => ((t : R))) (hcons z hz))
      (by
        rw [cast_sum_ite, cast_sum_ite, ← Int.cast_sum]
        exact_mod_cast congrArg (fun t : ℤ => ((t : R))) hsrc)
  refine ⟨P, hw, fun a => ?_, ?_⟩
  · have := hcap a
    rw [uload_cast] at this
    exact_mod_cast this
  · have := hcost
    simp only [uload_cast] at this
    exact_mod_cast this

/-- The same transfer for the literature-faithful form: if the Full conjecture held over
`R`, it would hold over `ℤ`.  The four extra hypotheses (simple, loopless, acyclic,
`x ≤ u`) transfer verbatim -- the first three do not mention the ring at all, and `x ≤ u`
pushes forward along the order embedding `ℤ ↪ R`. -/
theorem DGGCostConjectureFull_int_of (h : DGGCostConjectureFull R) :
    DGGCostConjectureFull ℤ := by
  intro W E K _ _ _ _ _ tail head src term d dmax x c u hsimple hloop hacyc hxu
    hinj hns hpos hle hex hc hx hcons hsrc
  obtain ⟨P, hw, hcap, hcost⟩ :=
    h W E K tail head src term (fun k => ((d k : R))) ((dmax : R))
      (fun a => ((x a : R))) (fun a => ((c a : R))) (fun a => ((u a : R)))
      hsimple hloop hacyc (fun a => by exact_mod_cast hxu a)
      hinj hns
      (fun k => by exact_mod_cast hpos k)
      (fun k => by exact_mod_cast hle k)
      (by obtain ⟨k, hk⟩ := hex; exact ⟨k, by exact_mod_cast hk⟩)
      (fun a => by exact_mod_cast hc a)
      (fun a => by exact_mod_cast hx a)
      (fun z hz => by
        rw [cast_sum_ite, cast_sum_ite, cast_sum_ite]
        exact_mod_cast congrArg (fun t : ℤ => ((t : R))) (hcons z hz))
      (by
        rw [cast_sum_ite, cast_sum_ite, ← Int.cast_sum]
        exact_mod_cast congrArg (fun t : ℤ => ((t : R))) hsrc)
  refine ⟨P, hw, fun a => ?_, ?_⟩
  · have := hcap a
    rw [uload_cast] at this
    exact_mod_cast this
  · have := hcost
    simp only [uload_cast] at this
    exact_mod_cast this

end Transfer

/-- **Layer B (main), literature-faithful form, over `ℤ`.**  The counterexample instance
discharges every hypothesis of `DGGCostConjectureFull`: it is simple (`arcs_simple`),
loopless (`no_self_loops`), acyclic (`⟨rank, rank_arc⟩`), and takes `u := x` (the worst
case the primary source identifies), so `x ≤ u` holds by reflexivity. -/
theorem not_DGGCostConjectureFull_int : ¬ DGGCostConjectureFull ℤ := by
  intro h
  obtain ⟨P, hw, hcap, hcost⟩ :=
    h Vtx Arc (Fin 3) tl hd Vtx.s trm dem Dmax xf cf xf
      arcs_simple no_self_loops ⟨rank, rank_arc⟩ (fun a => le_refl _)
      trm_injective trm_ne_source dem_pos Dmax_is_max.1 Dmax_is_max.2
      cf_nonneg xf_nonneg flow_feasible conservation_source
  have hlow : (60 : ℤ) ≤ ∑ a : Arc, cf a * uload dem P a :=
    min_cost_capacity_good P hw hcap
  rw [fractional_cost] at hcost
  omega

/-- **Layer B (main), literature-faithful form, general coefficient ring.**  Goemans' cost
conjecture -- capacities restored, digraph simple, loopless and acyclic -- is false over
every linearly ordered commutative ring. -/
theorem not_DGGCostConjectureFull (R : Type) [CommRing R] [LinearOrder R]
    [IsStrictOrderedRing R] : ¬ DGGCostConjectureFull R :=
  fun h => not_DGGCostConjectureFull_int (DGGCostConjectureFull_int_of h)

/-- The literature-faithful form over `ℚ`, the setting of Conjecture 1.3. -/
theorem not_DGGCostConjectureFull_rat : ¬ DGGCostConjectureFull ℚ :=
  not_DGGCostConjectureFull ℚ

/-- **THE HEADLINE.**  Goemans' cost conjecture for single-source unsplittable flow
(Conjecture 1.3 of arXiv:2308.02651, the cost version of the Dinitz–Garg–Goemans theorem)
is **false** over `ℚ`, in the form that keeps every piece of the literature's data: arc
capacities `u` with `x ≤ u`, and a simple, loopless, acyclic digraph.

`dgg_cost_conjecture_false` below is the same refutation for the bare form
`DGGCostConjecture` and is kept as the searchable alias. -/
theorem goemans_cost_conjecture_false : ¬ DGGCostConjectureFull ℚ :=
  not_DGGCostConjectureFull ℚ

/-- The headline over the reals. -/
theorem goemans_cost_conjecture_false_real : ¬ DGGCostConjectureFull ℝ :=
  not_DGGCostConjectureFull ℝ

/-- **Layer B, bare form.**  Goemans' cost conjecture is false over `ℤ`. -/
theorem not_DGGCostConjecture_int : ¬ DGGCostConjecture ℤ := by
  intro h
  obtain ⟨P, hw, hcap, hcost⟩ :=
    h Vtx Arc (Fin 3) tl hd Vtx.s trm dem Dmax xf cf
      trm_injective trm_ne_source dem_pos Dmax_is_max.1 Dmax_is_max.2
      cf_nonneg xf_nonneg flow_feasible conservation_source
  have hlow : (60 : ℤ) ≤ ∑ a : Arc, cf a * uload dem P a :=
    min_cost_capacity_good P hw hcap
  rw [fractional_cost] at hcost
  omega

/-- **Layer B, bare form, general coefficient ring.**  Goemans' cost conjecture is false
over every linearly ordered commutative ring — in particular over `ℚ`, the setting of
Conjecture 1.3 of arXiv:2308.02651, and over `ℝ`. -/
theorem not_DGGCostConjecture (R : Type) [CommRing R] [LinearOrder R] [IsStrictOrderedRing R] :
    ¬ DGGCostConjecture R :=
  fun h => not_DGGCostConjecture_int (DGGCostConjecture_int_of h)

/-- The bare form over `ℚ`; the searchable alias of the headline
`goemans_cost_conjecture_false`.  (It also follows from the headline without re-running the
instance, via `DGGCostConjectureFull_of_DGGCostConjecture` — see
`dgg_cost_conjecture_false_of_headline` — since the Full form is the weaker Prop.) -/
theorem dgg_cost_conjecture_false : ¬ DGGCostConjecture ℚ := not_DGGCostConjecture ℚ

/-- The same over the reals. -/
theorem dgg_cost_conjecture_false_real : ¬ DGGCostConjecture ℝ := not_DGGCostConjecture ℝ

/-- The headline implies the bare-form refutation, with no second appeal to the instance:
the Full form is the weaker Prop, so refuting it refutes the bare one. -/
theorem dgg_cost_conjecture_false_of_headline : ¬ DGGCostConjecture ℚ :=
  fun h => goemans_cost_conjecture_false (DGGCostConjectureFull_of_DGGCostConjecture ℚ h)

/-! ## 6.  Axiom report -/

-- the headline first
#print axioms goemans_cost_conjecture_false
#print axioms goemans_cost_conjecture_false_real
#print axioms not_DGGCostConjectureFull
#print axioms not_DGGCostConjectureFull_rat
#print axioms not_DGGCostConjectureFull_int
#print axioms DGGCostConjectureFull_int_of
#print axioms DGGCostConjectureFull_of_DGGCostConjecture
#print axioms dgg_cost_conjecture_false_of_headline

#print axioms min_cost_capacity_good
#print axioms enum_check
#print axioms fractional_cost
#print axioms flow_feasible
#print axioms conservation_source
#print axioms exists_capacity_good
#print axioms cost_sixty_attained
#print axioms optimum_is_sixty
#print axioms paths_t1
#print axioms paths_t2
#print axioms paths_t3
#print axioms path_complete
#print axioms arcs_simple
#print axioms no_self_loops
#print axioms rank_arc
#print axioms Dmax_is_max
#print axioms the_six_are_walks
#print axioms the_six_walks_are_simple
#print axioms walksFrom_complete
#print axioms DGGCostConjecture_int_of
#print axioms not_DGGCostConjecture_int
#print axioms not_DGGCostConjecture
#print axioms dgg_theorem_holds_here
#print axioms cost_clause_alone_satisfiable
#print axioms two_dmax_conclusion_holds_here
#print axioms dgg_cost_conjecture_false
#print axioms dgg_cost_conjecture_false_real

end Submission
