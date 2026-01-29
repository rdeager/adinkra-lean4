/-
Copyright (c) 2026 Richard Eager. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Richard Eager, Claude (Anthropic)
-/
import Adinkra.Basic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-!
# Direct Adinkra Definition

This module formalizes the direct definition of Adinkras from Eager et al. (2024).

## Main definitions

- `AdinkraDirect`: A graph with 4 decoration functions satisfying 4 axioms
- `AdinkraDirect.bosons`: The set of vertices with parity 0
- `AdinkraDirect.fermions`: The set of vertices with parity 1

## Main results

- `AdinkraDirect.partition`: Bosons and fermions partition the vertex set
- `AdinkraDirect.edge_crosses_partition`: Every edge connects a boson to a fermion

## Implementation notes

The 4 axioms in the direct definition are:
1. **Odd**: Edges connect vertices of different parity (bipartite)
2. **Unimodular**: Edges connect vertices differing by 1 in height
3. **N-color-regular**: Each vertex has exactly one edge of each color
4. **Odd 4-cycles**: Every 2-colored 4-cycle has odd dashing sum

This is equivalent to the layered definition; see `Adinkra.Equiv`.

## References

- [Eager et al., *Adinkras and Pure Spinors*][eager2024], Definition 2.1
-/

namespace Adinkra

/-- Direct definition of an Adinkra: a graph with 4 decoration functions
(parity `|·|`, height `𝔥`, color `𝔠`, dashing `𝔭`) satisfying 4 axioms.

This is a more direct definition compared to the layered approach.
Source: Eager et al. (2024), Definition 2.1 -/
structure AdinkraDirect (V : Type*) [DecidableEq V] [Fintype V] (N : ℕ) where
  /-- The underlying simple graph. -/
  graph : SimpleGraph V
  /-- Decidable adjacency for computational definitions. -/
  [decAdj : DecidableRel graph.Adj]
  /-- The graph is connected. -/
  connected : graph.Connected
  /-- Parity function `|·| : V → ℤ₂` where bosons = 0, fermions = 1. -/
  parity : V → ZMod 2
  /-- Height function `𝔥 : V → ℤ` (engineering dimension in physics). -/
  height : V → ℤ
  /-- Edge coloring `𝔠` assigning colors `0, 1, ..., N-1` to each edge. -/
  edgeColor : EdgeColoring graph N
  /-- Edge dashing `𝔭` assigning solid (0) or dashed (1) to each edge. -/
  dashing : EdgeDashing graph

  /-- Axiom 1 (Odd): Edges connect vertices of different parity.
  `|v| ≠ |w|` for all edges `(v, w)`. -/
  ax_odd : IsBipartiteLabeling graph parity

  /-- Axiom 2 (Unimodular): Edge heights differ by exactly 1.
  `|𝔥(w) - 𝔥(v)| = 1` for all edges `(v, w)`. -/
  ax_unimod : ∀ v w, graph.Adj v w → |height w - height v| = 1

  /-- Axiom 3 (N-color-regular): Each vertex has exactly one edge of each color.
  For all `v` and `i`, there exists a unique `w` such that `(v, w)` has color `i`. -/
  ax_regular : IsColorRegular graph N edgeColor

  /-- Axiom 4a (4-cycle existence): For any vertex `v` and distinct colors `i, j`,
  there exists a unique 2-colored 4-cycle starting at `v` with those colors.
  This is the "chromotopology" axiom from the layered definition. -/
  ax_fourCycle : ∀ i j : Fin N, i ≠ j → ∀ v : V,
    ∃! cyc : TwoColoredFourCycle graph N edgeColor,
      cyc.v₀ = v ∧ cyc.color₁ = i ∧ cyc.color₂ = j

  /-- Axiom 4b (Odd 4-cycles): Every 2-colored 4-cycle has odd dashing sum.
  For any 4-cycle using colors `i, j`, the sum of dashings is 1 mod 2. -/
  ax_oddCycles : ∀ (c : TwoColoredFourCycle graph N edgeColor),
    c.toFourCycle.dashingSum dashing = 1

attribute [instance] AdinkraDirect.decAdj

/-- The number of colors N in an Adinkra.
    In physics, N is the number of supersymmetries. -/
def AdinkraDirect.numColors {V : Type*} [DecidableEq V] [Fintype V] {N : ℕ}
    (_ : AdinkraDirect V N) : ℕ := N

/-- The set of bosons (parity 0 vertices). -/
def AdinkraDirect.bosons {V : Type*} [DecidableEq V] [Fintype V] {N : ℕ}
    (A : AdinkraDirect V N) : Set V :=
  {v | A.parity v = 0}

/-- The set of fermions (parity 1 vertices). -/
def AdinkraDirect.fermions {V : Type*} [DecidableEq V] [Fintype V] {N : ℕ}
    (A : AdinkraDirect V N) : Set V :=
  {v | A.parity v = 1}

/-- Every element of ZMod 2 is 0 or 1. -/
private lemma zmod2_cases (x : ZMod 2) : x = 0 ∨ x = 1 := by
  fin_cases x <;> simp

/-- Bosons and fermions partition the vertex set. -/
theorem AdinkraDirect.partition {V : Type*} [DecidableEq V] [Fintype V] {N : ℕ}
    (A : AdinkraDirect V N) : A.bosons ∪ A.fermions = Set.univ := by
  ext v
  simp only [Set.mem_union, AdinkraDirect.bosons, AdinkraDirect.fermions,
             Set.mem_setOf, Set.mem_univ, iff_true]
  exact zmod2_cases (A.parity v)

/-- An edge goes from boson to fermion or vice versa. -/
theorem AdinkraDirect.edge_crosses_partition {V : Type*} [DecidableEq V] [Fintype V] {N : ℕ}
    (A : AdinkraDirect V N) (v w : V) (hadj : A.graph.Adj v w) :
    (v ∈ A.bosons ∧ w ∈ A.fermions) ∨ (v ∈ A.fermions ∧ w ∈ A.bosons) := by
  have hp := A.ax_odd v w hadj
  simp only [AdinkraDirect.bosons, AdinkraDirect.fermions, Set.mem_setOf]
  rcases zmod2_cases (A.parity v) with hv | hv <;>
  rcases zmod2_cases (A.parity w) with hw | hw <;> simp_all

end Adinkra
