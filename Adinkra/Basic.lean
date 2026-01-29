/-
Copyright (c) 2026 Richard Eager. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Richard Eager, Claude (Anthropic)
-/
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.EdgeLabeling
import Mathlib.Data.Fin.Basic
import Mathlib.Data.ZMod.Basic

/-!
# Adinkra Core Definitions

This module defines the basic structures needed for Adinkras:
edge colorings, dashings, bipartite structure, and four-cycles with colorings.

## Main definitions

- `IsBipartiteLabeling`: Predicate for a valid bipartite labeling function
- `EdgeColoring`: Type alias for `N`-color edge labeling (via `EdgeLabeling (Fin N)`)
- `EdgeDashing`: Type alias for edge dashing (via `EdgeLabeling (ZMod 2)`)
- `IsColorRegular`: Predicate asserting each vertex has exactly one neighbor of each color
- `FourCycle`: A 4-cycle in a graph specified by its four vertices
- `TwoColoredFourCycle`: A 4-cycle using exactly 2 colors, alternating

## Implementation notes

We use mathlib's `SimpleGraph.EdgeLabeling` for both edge coloring and dashing:
- Edge coloring: `G.EdgeLabeling (Fin N)` assigns colors 0..N-1 to edges
- Edge dashing: `G.EdgeLabeling (ZMod 2)` assigns solid (0) or dashed (1) to edges

## References

- [Zhang, *Adinkras for Mathematicians*][zhang2011]
- [Eager et al., *Adinkras and Pure Spinors*][eager2024]
-/

namespace Adinkra

/-- A bipartite labeling assigns a parity (boson/fermion) to each vertex. -/
def IsBipartiteLabeling {V : Type*} (G : SimpleGraph V) (parity : V → ZMod 2) : Prop :=
  ∀ v w, G.Adj v w → parity v ≠ parity w

/-- Type alias for edge coloring with N colors. -/
abbrev EdgeColoring {V : Type*} (G : SimpleGraph V) (N : ℕ) := G.EdgeLabeling (Fin N)

/-- Type alias for edge dashing (solid=0, dashed=1). -/
abbrev EdgeDashing {V : Type*} (G : SimpleGraph V) := G.EdgeLabeling (ZMod 2)

/-- Each vertex has exactly one neighbor of each color (N-color-regular). -/
def IsColorRegular {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (N : ℕ) (c : EdgeColoring G N) : Prop :=
  ∀ v : V, ∀ i : Fin N, ∃! w : V, ∃ h : G.Adj v w, c.get v w h = i

/-- A 4-cycle in a graph specified by its four vertices in order.

The vertices form a cycle: `v₀ ~ v₁ ~ v₂ ~ v₃ ~ v₀`. -/
structure FourCycle {V : Type*} (G : SimpleGraph V) where
  /-- First vertex of the 4-cycle. -/
  v₀ : V
  /-- Second vertex of the 4-cycle. -/
  v₁ : V
  /-- Third vertex of the 4-cycle. -/
  v₂ : V
  /-- Fourth vertex of the 4-cycle. -/
  v₃ : V
  /-- Edge from `v₀` to `v₁`. -/
  adj₀₁ : G.Adj v₀ v₁
  /-- Edge from `v₁` to `v₂`. -/
  adj₁₂ : G.Adj v₁ v₂
  /-- Edge from `v₂` to `v₃`. -/
  adj₂₃ : G.Adj v₂ v₃
  /-- Edge from `v₃` to `v₀`, completing the cycle. -/
  adj₃₀ : G.Adj v₃ v₀
  /-- All four vertices are pairwise distinct. -/
  distinct : v₀ ≠ v₁ ∧ v₀ ≠ v₂ ∧ v₀ ≠ v₃ ∧ v₁ ≠ v₂ ∧ v₁ ≠ v₃ ∧ v₂ ≠ v₃

/-- The dashing sum of a 4-cycle. -/
def FourCycle.dashingSum {V : Type*} {G : SimpleGraph V}
    (c : FourCycle G) (d : EdgeDashing G) : ZMod 2 :=
  d.get c.v₀ c.v₁ c.adj₀₁ + d.get c.v₁ c.v₂ c.adj₁₂ +
  d.get c.v₂ c.v₃ c.adj₂₃ + d.get c.v₃ c.v₀ c.adj₃₀

/-- A 2-colored 4-cycle uses exactly 2 colors, alternating.

The edge colors alternate: `v₀ ~[color₁] v₁ ~[color₂] v₂ ~[color₁] v₃ ~[color₂] v₀`. -/
structure TwoColoredFourCycle {V : Type*} (G : SimpleGraph V) (N : ℕ)
    (c : EdgeColoring G N) extends FourCycle G where
  /-- First color used on edges `v₀-v₁` and `v₂-v₃`. -/
  color₁ : Fin N
  /-- Second color used on edges `v₁-v₂` and `v₃-v₀`. -/
  color₂ : Fin N
  /-- The two colors are distinct. -/
  colors_distinct : color₁ ≠ color₂
  /-- Edge `v₀-v₁` has color `color₁`. -/
  edge₀₁_color : c.get v₀ v₁ adj₀₁ = color₁
  /-- Edge `v₁-v₂` has color `color₂`. -/
  edge₁₂_color : c.get v₁ v₂ adj₁₂ = color₂
  /-- Edge `v₂-v₃` has color `color₁`. -/
  edge₂₃_color : c.get v₂ v₃ adj₂₃ = color₁
  /-- Edge `v₃-v₀` has color `color₂`. -/
  edge₃₀_color : c.get v₃ v₀ adj₃₀ = color₂

end Adinkra
