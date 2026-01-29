/-
Copyright (c) 2026 Richard Eager. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Richard Eager, Claude (Anthropic)
-/
import Adinkra.Basic
import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Combinatorics.SimpleGraph.Finite

/-!
# Adinkras

This module defines Adinkras as a predicate on `SimpleGraph`, following mathlib conventions.

An Adinkra is a finite, connected, bipartite, N-regular graph with:
- An N-edge-coloring (each vertex has exactly one edge of each color)
- A dashing function on edges
- The "odd 4-cycle" property: every 2-colored 4-cycle has odd dashing sum

## Main definitions

- `SimpleGraph.IsChromotopology`: Predicate for a chromotopology (Adinkra without dashing)
- `SimpleGraph.IsAdinkra`: Predicate asserting a graph with coloring/dashing is an N-Adinkra
- `SimpleGraph.IsRankedAdinkra`: Adinkra with explicit height function
- `SimpleGraph.IsValise`: Ranked Adinkra with heights in {0, 1}
- `SimpleGraph.IsChromotopology.qOp`: The q_i operator (unique neighbor of color i)

## Main results

- `SimpleGraph.IsChromotopology.qOp_involutive`: q_i is an involution
- `SimpleGraph.IsChromotopology.qOp_comm`: q_i and q_j commute (from 4-cycle axiom)

## Implementation notes

This definition follows the `IsSRGWith` pattern from mathlib: a predicate structure
on `SimpleGraph` that bundles propositional properties.

Since `EdgeColoring` and `Dashing` are data (not propositions), they are parameters
to the predicate rather than fields. This is similar to how `IsSRGWith` takes
numerical parameters.

We reuse mathlib's `IsBipartite` and `IsRegularOfDegree` where possible.

## References

- [Zhang, *Adinkras for Mathematicians*][zhang2011]
- [Eager et al., *Adinkras and Pure Spinors*][eager2024]

## See also

- `Adinkra.Basic`: Core types (EdgeColoring, EdgeDashing, TwoColoredFourCycle)
- `Adinkra.Layered`: Bundled layered definition (Topology → Chromotopology → Adinkra)
- `Adinkra.Direct`: Bundled direct 4-axiom definition
- `Adinkra.Equiv`: Equivalence proofs between all definitions
-/

namespace SimpleGraph

open Adinkra

variable {V : Type*} [DecidableEq V] [Fintype V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- A chromotopology is a connected bipartite N-regular graph with edge coloring
satisfying the 4-cycle axiom. This is the HEIGHT-FREE base structure.

For the full Adinkra (with dashing), see `IsAdinkra`. -/
structure IsChromotopology (N : ℕ) (c : EdgeColoring G N) : Prop where
  /-- The graph is connected. -/
  connected : G.Connected
  /-- The graph is bipartite (2-colorable). -/
  bipartite : G.IsBipartite
  /-- The graph is N-regular: each vertex has degree N. -/
  regular : G.IsRegularOfDegree N
  /-- Each vertex has exactly one neighbor of each color (N-color-regularity). -/
  colorRegular : IsColorRegular G N c
  /-- For any two distinct colors, every vertex lies in a unique 2-colored 4-cycle
  using those colors. This is the chromotopology axiom. -/
  fourCycleAxiom : ∀ i j : Fin N, i ≠ j → ∀ v : V,
    ∃! cyc : TwoColoredFourCycle G N c,
      cyc.v₀ = v ∧ cyc.color₁ = i ∧ cyc.color₂ = j

namespace IsChromotopology

variable {G} {N : ℕ} {c : EdgeColoring G N}
variable (h : G.IsChromotopology N c)

/-- The unique neighbor of v with color i.
    This is the q_i operator from Zhang's algebraic characterization. -/
noncomputable def qOp (i : Fin N) (v : V) : V :=
  (h.colorRegular v i).choose

/-- qOp i v is adjacent to v. -/
lemma qOp_adj (i : Fin N) (v : V) : G.Adj v (h.qOp i v) :=
  (h.colorRegular v i).choose_spec.1.choose

/-- The edge from v to qOp i v has color i. -/
lemma qOp_color (i : Fin N) (v : V) :
    c.get v (h.qOp i v) (h.qOp_adj i v) = i :=
  (h.colorRegular v i).choose_spec.1.choose_spec

/-- qOp i v is the unique vertex adjacent to v with color i. -/
lemma qOp_unique (i : Fin N) (v w : V)
    (hadj : G.Adj v w) (hcolor : c.get v w hadj = i) :
    w = h.qOp i v :=
  (h.colorRegular v i).choose_spec.2 w ⟨hadj, hcolor⟩

/-- q_i is an involution: applying it twice returns to the original vertex. -/
theorem qOp_involutive (i : Fin N) : Function.Involutive (h.qOp i) := by
  intro v
  set w := h.qOp i v with hw_def
  have h_adj_sym : G.Adj w v := G.symm (h.qOp_adj i v)
  have h_color_sym : c.get w v h_adj_sym = i := by
    rw [SimpleGraph.EdgeLabeling.get_comm]
    exact h.qOp_color i v
  exact (h.qOp_unique i w v h_adj_sym h_color_sym).symm

/-- Applying `qOp i` twice returns to the original vertex. -/
@[simp]
theorem qOp_qOp (i : Fin N) (v : V) : h.qOp i (h.qOp i v) = v :=
  h.qOp_involutive i v

/-- q_i operators commute: q_i(q_j(v)) = q_j(q_i(v)).
    This is equivalent to the 4-cycle axiom. -/
theorem qOp_comm (i j : Fin N) (v : V) :
    h.qOp i (h.qOp j v) = h.qOp j (h.qOp i v) := by
  by_cases hij : i = j
  · simp only [hij]
  -- Use the 4-cycle axiom
  obtain ⟨cyc, ⟨hv₀, hc₁, hc₂⟩, _⟩ := h.fourCycleAxiom i j hij v
  -- cyc.v₁ = qOp i v
  have hadj₀₁ : G.Adj v cyc.v₁ := hv₀ ▸ cyc.adj₀₁
  have hcolor₀₁ : c.get v cyc.v₁ hadj₀₁ = i := by
    have hc := cyc.edge₀₁_color
    simp only [hv₀, hc₁] at hc
    convert hc using 2
  have hv₁ : cyc.v₁ = h.qOp i v := h.qOp_unique i v cyc.v₁ hadj₀₁ hcolor₀₁
  -- cyc.v₃ = qOp j v
  have hadj₃₀ : G.Adj v cyc.v₃ := G.symm (hv₀ ▸ cyc.adj₃₀)
  have hcolor₃₀ : c.get v cyc.v₃ hadj₃₀ = j := by
    have hc := cyc.edge₃₀_color
    simp only [hv₀, hc₂] at hc
    rw [SimpleGraph.EdgeLabeling.get_comm] at hc
    convert hc using 2
  have hv₃ : cyc.v₃ = h.qOp j v := h.qOp_unique j v cyc.v₃ hadj₃₀ hcolor₃₀
  -- cyc.v₂ = qOp j (qOp i v)
  have hadj₁₂ : G.Adj (h.qOp i v) cyc.v₂ := hv₁ ▸ cyc.adj₁₂
  have hcolor₁₂ : c.get (h.qOp i v) cyc.v₂ hadj₁₂ = j := by
    have hc := cyc.edge₁₂_color
    simp only [hv₁, hc₂] at hc
    convert hc using 2
  have hv₂_from_v₁ : cyc.v₂ = h.qOp j (h.qOp i v) :=
    h.qOp_unique j (h.qOp i v) cyc.v₂ hadj₁₂ hcolor₁₂
  -- cyc.v₂ = qOp i (qOp j v)
  have hadj₂₃ : G.Adj (h.qOp j v) cyc.v₂ := G.symm (hv₃ ▸ cyc.adj₂₃)
  have hcolor₂₃ : c.get (h.qOp j v) cyc.v₂ hadj₂₃ = i := by
    have hc := cyc.edge₂₃_color
    simp only [hv₃, hc₁] at hc
    rw [SimpleGraph.EdgeLabeling.get_comm] at hc
    convert hc using 2
  have hv₂_from_v₃ : cyc.v₂ = h.qOp i (h.qOp j v) :=
    h.qOp_unique i (h.qOp j v) cyc.v₂ hadj₂₃ hcolor₂₃
  -- Combine
  rw [← hv₂_from_v₁, hv₂_from_v₃]

end IsChromotopology

/-- A graph with given edge coloring and dashing is an N-Adinkra if it satisfies all axioms.

This is the mathlib-style predicate definition, following the `IsSRGWith` pattern.
The coloring and dashing are parameters (data), while the axioms are fields (propositions).

For the bundled layered definition, see `Adinkra.Layered.AdinkraLayered`.
For the bundled direct definition, see `Adinkra.Direct.AdinkraDirect`. -/
structure IsAdinkra (N : ℕ) (c : EdgeColoring G N) (d : EdgeDashing G) : Prop where
  /-- The underlying chromotopology structure. -/
  chromotopology : G.IsChromotopology N c
  /-- Every 2-colored 4-cycle has odd dashing sum (= 1 mod 2).
  This encodes the supersymmetry algebra via Clifford anticommutation. -/
  oddDashing : ∀ (cyc : TwoColoredFourCycle G N c),
    cyc.toFourCycle.dashingSum d = 1

namespace IsAdinkra

variable {G} {N : ℕ} {c : EdgeColoring G N} {d : EdgeDashing G}
variable (h : G.IsAdinkra N c d)

/-- Convenience accessor: the graph is connected. -/
def connected' : G.Connected := h.chromotopology.connected

/-- Convenience accessor: the graph is bipartite. -/
def bipartite' : G.IsBipartite := h.chromotopology.bipartite

/-- Convenience accessor: the graph is N-regular. -/
def regular' : G.IsRegularOfDegree N := h.chromotopology.regular

/-- Convenience accessor: each vertex has exactly one neighbor of each color. -/
def colorRegular' : IsColorRegular G N c := h.chromotopology.colorRegular

/-- Convenience accessor: the 4-cycle axiom holds. -/
def fourCycleAxiom' : ∀ i j : Fin N, i ≠ j → ∀ v : V,
    ∃! cyc : TwoColoredFourCycle G N c, cyc.v₀ = v ∧ cyc.color₁ = i ∧ cyc.color₂ = j :=
  h.chromotopology.fourCycleAxiom

end IsAdinkra

-- IsAdinkra inherits qOp from IsChromotopology
namespace IsAdinkra

variable {G} {N : ℕ} {c : EdgeColoring G N} {d : EdgeDashing G}
variable (h : G.IsAdinkra N c d)

/-- The unique neighbor of v with color i, delegated to chromotopology. -/
noncomputable def qOp (i : Fin N) (v : V) : V :=
  h.chromotopology.qOp i v

/-- qOp i v is adjacent to v. -/
lemma qOp_adj (i : Fin N) (v : V) : G.Adj v (h.qOp i v) :=
  h.chromotopology.qOp_adj i v

/-- The edge from v to qOp i v has color i. -/
lemma qOp_color (i : Fin N) (v : V) :
    c.get v (h.qOp i v) (h.qOp_adj i v) = i :=
  h.chromotopology.qOp_color i v

/-- qOp i v is the unique vertex adjacent to v with color i. -/
lemma qOp_unique (i : Fin N) (v w : V)
    (hadj : G.Adj v w) (hcolor : c.get v w hadj = i) :
    w = h.qOp i v :=
  h.chromotopology.qOp_unique i v w hadj hcolor

/-- q_i is an involution: applying it twice returns to the original vertex. -/
theorem qOp_involutive (i : Fin N) : Function.Involutive (h.qOp i) :=
  h.chromotopology.qOp_involutive i

/-- Applying `qOp i` twice returns to the original vertex. -/
@[simp]
theorem qOp_qOp (i : Fin N) (v : V) : h.qOp i (h.qOp i v) = v :=
  h.chromotopology.qOp_qOp i v

/-- q_i operators commute: q_i(q_j(v)) = q_j(q_i(v)). -/
theorem qOp_comm (i j : Fin N) (v : V) :
    h.qOp i (h.qOp j v) = h.qOp j (h.qOp i v) :=
  h.chromotopology.qOp_comm i j v

end IsAdinkra

/-- A ranked Adinkra is an Adinkra with an explicit height function `h : V → ℤ`
satisfying `|h(w) - h(v)| = 1` for adjacent `v`, `w`.

The height function makes the graph into a Hasse diagram of a ranked poset.
Every Adinkra admits such a height function via `exists_ranked`. -/
structure IsRankedAdinkra (N : ℕ) (c : EdgeColoring G N) (d : EdgeDashing G)
    (height : V → ℤ) : Prop where
  /-- The underlying Adinkra structure. -/
  adinkra : G.IsAdinkra N c d
  /-- Adjacent vertices have height difference exactly 1. -/
  heightDiff : ∀ v w, G.Adj v w → |height w - height v| = 1

/-- A valise is a ranked Adinkra with height values in `{0, 1}`.
This is the minimal ranking, corresponding to parity.

Construction: Use the bipartite coloring as height via `exists_valise`. -/
structure IsValise (N : ℕ) (c : EdgeColoring G N) (d : EdgeDashing G)
    (height : V → ℤ) : Prop where
  /-- The underlying Adinkra structure. -/
  adinkra : G.IsAdinkra N c d
  /-- Height is 0 or 1 for every vertex. -/
  heightRange : ∀ v, height v = 0 ∨ height v = 1
  /-- Adjacent vertices have height difference exactly 1. -/
  heightDiff : ∀ v w, G.Adj v w → |height w - height v| = 1

namespace IsValise

variable {G} {N : ℕ} {c : EdgeColoring G N} {d : EdgeDashing G} {height : V → ℤ}

/-- Every valise is a ranked Adinkra. -/
theorem isRankedAdinkra (h : G.IsValise N c d height) :
    G.IsRankedAdinkra N c d height :=
  ⟨h.adinkra, h.heightDiff⟩

end IsValise

end SimpleGraph
