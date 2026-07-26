/-
# The challenge: Goemans' (Dinitz–Garg–Goemans) cost conjecture for single-source
  unsplittable flow, stated.

This is the **statement** file.  It imports nothing but Mathlib, and it declares nothing but

* `IsWalk` and `uload`, the two auxiliary definitions the conjecture is phrased with, and
* `DGGCostConjectureFull`, the literature-faithful transcription of Conjecture 1.3 of
  Traub–Vargas Koch–Zenklusen, arXiv:2308.02651,

followed by the theorem itself, whose body here is `sorry`.  Nothing is proved in this file,
so a reviewer has only to *read* it — against the verbatim quotes from the primary source,
which are in the header of `Submission.lean` — and judge whether `DGGCostConjectureFull` is
a faithful (indeed weaker) rendering of the conjecture.  That reading is the boundary of the
kernel-checked claim.

The proof is in `Submission.lean`, which imports this file; both therefore refer to the
*same* `DGGCostConjectureFull` constant, so the statement cannot drift between them.
`check.py` type-checks the bridge

    example : ¬ DGGCostConjectureFull ℚ := Submission.goemans_cost_conjecture_false

and checks that the proof's axioms are within `[propext, Classical.choice, Quot.sound]` —
in particular that it does not go through the `sorry` below.

Provenance — the counterexample is not ours; it is due to Dmitry Rybin and the GPT-5.6 Pro
session he ran on 2026-07-22 — is in `README.md` and in the header of `Submission.lean`.
The layout (trusted statement file, separate proof file, mechanical bridge between them)
follows the comparator convention of leanprover/lean-eval.
-/
import Mathlib

namespace DGG

section Walks

variable {W E : Type}

/-- `IsWalk tail head x l y`: the list of arcs `l`, read left to right, is a walk from
vertex `x` to vertex `y`.  Repeated vertices and arcs are permitted. -/
def IsWalk (tail head : E → W) : W → List E → W → Prop
  | x, [], y => x = y
  | x, e :: l, y => tail e = x ∧ IsWalk tail head (head e) l y

end Walks

/-- Load induced on arc `a` by an unsplittable routing `P` with demands `d`:
`flow_P(a) = sum_{k : a in P k} d k`. -/
def uload {R K E : Type} [AddCommMonoid R] [Fintype K] [DecidableEq E]
    (d : K → R) (P : K → List E) (a : E) : R :=
  ∑ k : K, if a ∈ P k then d k else 0

/-- **Goemans' cost conjecture, literature-faithful form.**  Conjecture 1.3 of
arXiv:2308.02651 with nothing elided: the capacity vector `u` is present together with the
source's standing hypothesis `x ≤ u`, and the digraph `G = (W, E)` is required to be
*simple* (no two arcs share both endpoints), *loopless*, and *acyclic* (witnessed by a
topological rank `r`), the source itself noting that `G` may be assumed acyclic.

Each of these four is an **added** hypothesis relative to `DGGCostConjecture`, so this Prop
is weaker -- see `DGGCostConjectureFull_of_DGGCostConjecture`, which proves that
implication in the kernel -- and `not_DGGCostConjectureFull` is correspondingly the
stronger refutation.  It is also weaker than any reading of Conjecture 1.3: no reading of
"directed graph" or of the SSUF instance data is excluded. -/
def DGGCostConjectureFull (R : Type) [CommRing R] [LinearOrder R] [IsStrictOrderedRing R] :
    Prop :=
  ∀ (W E K : Type) [Fintype W] [DecidableEq W] [Fintype E] [DecidableEq E] [Fintype K]
    (tail head : E → W) (src : W) (term : K → W) (d : K → R) (dmax : R) (x c u : E → R),
    -- the digraph is simple, loopless and acyclic
    Function.Injective (fun a : E => (tail a, head a)) →
    (∀ a, tail a ≠ head a) →
    (∃ r : W → ℕ, ∀ a, r (tail a) < r (head a)) →
    -- capacities, with the source's standing hypothesis
    (∀ a, x a ≤ u a) →
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

end DGG

namespace Challenge

open DGG

/-- **THE CHALLENGE.**  Goemans' cost conjecture for single-source unsplittable flow
(Conjecture 1.3 of arXiv:2308.02651, the cost version of the Dinitz–Garg–Goemans theorem),
in the form that keeps every piece of the literature's data — arc capacities `u` with
`x ≤ u`, and a simple, loopless, acyclic digraph — is **false** over `ℚ`.

Proved in `Submission.lean` as `Submission.goemans_cost_conjecture_false`; the `sorry` here
is the placeholder that keeps this file free of proof. -/
theorem goemans_cost_conjecture_false : ¬ DGGCostConjectureFull ℚ := sorry

end Challenge
