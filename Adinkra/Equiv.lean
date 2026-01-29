/-
Copyright (c) 2026 Richard Eager. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Richard Eager, Claude (Anthropic)
-/
import Adinkra.Layered
import Adinkra.Direct
import Adinkra.Adinkra
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Combinatorics.SimpleGraph.ConcreteColorings

/-!
# Equivalence of Adinkra Definitions

This module proves equivalences between the three Adinkra definitions:
- `SimpleGraph.IsAdinkra`: mathlib-style predicate on SimpleGraph
- `AdinkraLayered` (Zhang 2011): layered (Topology → Chromotopology → RankedChromotopology → Adinkra)
- `AdinkraDirect` (Eager 2024): direct (4 axioms)

## Main definitions

### Layered ↔ Direct conversions
- `AdinkraLayered.toDirect`: Convert Layered definition to Direct definition
- `AdinkraDirect.toLayered`: Convert Direct definition to Layered definition

### → IsAdinkra conversions
- `AdinkraLayered.isChromotopology`: Layered → IsChromotopology
- `AdinkraLayered.isAdinkra`: Layered → IsAdinkra
- `AdinkraDirect.isChromotopology`: Direct → IsChromotopology
- `AdinkraDirect.isAdinkra`: Direct → IsAdinkra

### IsAdinkra → Layered conversion
- `SimpleGraph.IsAdinkra.toAdinkraLayered`: IsAdinkra → AdinkraLayered
- `SimpleGraph.IsAdinkra.exists_ranked`: Every Adinkra admits a height function
- `SimpleGraph.IsAdinkra.exists_valise`: Every Adinkra admits a valise structure

## Main results

- `adinkra_equiv`: Layered ↔ Direct preserves the underlying graph
- `layered_direct_same_graph`: Layered → Direct preserves the graph
- `direct_layered_same_graph`: Direct → Layered preserves the graph
- `bipartite_iff_odd`: Layered's bipartite = Direct's ax_odd
- `heightDiff_iff_unimod`: Layered's heightDiff = Direct's ax_unimod
- `colorRegular_iff_regular`: Layered's colorRegular = Direct's ax_regular
- `oddDashing_iff_oddCycles`: Layered's oddDashing = Direct's ax_oddCycles

## Implementation notes

The key observations are:
1. All three definitions have compatible underlying data (graph, coloring, dashing)
2. Layered axioms correspond directly to Direct's 4 axioms
3. IsAdinkra captures the predicate form, with data as parameters

The conversions are definitionally equal on the data; they only differ in
how the axioms are organized (layered vs flat vs predicate).

## References

- [Zhang, *Adinkras for Mathematicians*][zhang2011]
- [Eager et al., *Adinkras and Pure Spinors*][eager2024]
-/

namespace Adinkra

variable {V : Type*} [DecidableEq V] [Fintype V] {N : ℕ}

/-! ### Shared helper lemmas -/

/-- The direct definition's color-regularity axiom implies N-regularity.
    Each vertex has exactly N neighbors (one per color). -/
lemma AdinkraDirect.isRegularOfDegree (A : AdinkraDirect V N) :
    A.graph.IsRegularOfDegree N := by
  intro v
  -- Strategy: construct bijection Fin N ≃ neighborFinset v using color-regularity
  -- Define f : (i : ℕ) → i < N → V as the unique neighbor with color ⟨i, hi⟩
  refine Finset.card_eq_of_bijective (fun i hi => (A.ax_regular v ⟨i, hi⟩).choose) ?_ ?_ ?_
  -- Surjective: every neighbor w has some color i with f(i) = w
  · intro w hw
    rw [SimpleGraph.mem_neighborFinset] at hw
    -- The edge v-w has some color c
    let c := A.edgeColor.get v w hw
    use c.val, c.isLt
    -- w is the unique neighbor with color c, and f(c.val) = (ax_regular v c).choose
    -- By uniqueness, (ax_regular v c).choose = w
    have huniq := (A.ax_regular v c).choose_spec.2 w ⟨hw, rfl⟩
    -- Need to show f c.val c.isLt = w, i.e., (ax_regular v ⟨c.val, c.isLt⟩).choose = w
    simp only [Fin.eta] at huniq ⊢
    exact huniq.symm
  -- f maps into neighborFinset: f(i) is adjacent to v
  · intro i hi
    rw [SimpleGraph.mem_neighborFinset]
    exact (A.ax_regular v ⟨i, hi⟩).choose_spec.1.choose
  -- Injective: if f(i) = f(j) then i = j
  · intro i j hi hj heq
    -- heq has form (fun i hi => ...) i hi = (fun i hi => ...) j hj
    -- Beta reduce it to get wi = wj
    simp only at heq
    -- Now heq : (A.ax_regular v ⟨i, hi⟩).choose = (A.ax_regular v ⟨j, hj⟩).choose
    have hi_spec := (A.ax_regular v ⟨i, hi⟩).choose_spec
    have hj_spec := (A.ax_regular v ⟨j, hj⟩).choose_spec
    -- f(i) is adjacent to v with color i
    have hadj_i : A.graph.Adj v (A.ax_regular v ⟨i, hi⟩).choose := hi_spec.1.choose
    have hcol_i : A.edgeColor.get v _ hadj_i = ⟨i, hi⟩ := hi_spec.1.choose_spec
    -- f(j) is adjacent to v with color j
    have hadj_j : A.graph.Adj v (A.ax_regular v ⟨j, hj⟩).choose := hj_spec.1.choose
    have hcol_j : A.edgeColor.get v _ hadj_j = ⟨j, hj⟩ := hj_spec.1.choose_spec
    -- Transport hadj_j along heq to get adjacency proof for same vertex as hadj_i
    have hadj_i' : A.graph.Adj v (A.ax_regular v ⟨i, hi⟩).choose := heq ▸ hadj_j
    -- All adjacency proofs are equal (Subsingleton)
    have hadj_eq : hadj_i = hadj_i' := Subsingleton.elim _ _
    -- Color at hadj_i' equals color at hadj_j (by heq)
    have hcol_j' : A.edgeColor.get v _ hadj_i' = ⟨j, hj⟩ := by
      have h : A.edgeColor.get v _ hadj_i' = A.edgeColor.get v _ hadj_j := by
        simp only [heq]
      rw [h, hcol_j]
    -- Since hadj_i = hadj_i', colors must be equal
    rw [hadj_eq] at hcol_i
    rw [hcol_i] at hcol_j'
    -- hcol_j' : ⟨i, hi⟩ = ⟨j, hj⟩, extract i = j
    exact Fin.mk.inj hcol_j'

/-! ### Layered → Direct direction -/

/-- Extract the Direct structure from a Layered Adinkra.
    The key insight is that all the data is the same; we just need to verify
    that the layered axioms imply the direct axioms. -/
def AdinkraLayered.toDirect (A : AdinkraLayered V N) : AdinkraDirect V N where
  graph := A.graph
  decAdj := A.decAdj
  connected := A.connected
  parity := A.parity
  height := A.height
  edgeColor := A.edgeColor
  dashing := A.dashing
  -- Axiom 1: bipartite → odd edges
  ax_odd := A.bipartite
  -- Axiom 2: heightDiff → unimodular
  ax_unimod := A.heightDiff
  -- Axiom 3: colorRegular → N-regular
  ax_regular := A.colorRegular
  -- Axiom 4a: fourCycleAxiom → 4-cycle existence
  ax_fourCycle := A.fourCycleAxiom
  -- Axiom 4b: oddDashing → odd cycles
  ax_oddCycles := A.oddDashing

/-! ### Direct → Layered direction -/

/-- Extract the Layered structure from a Direct Adinkra.
    We need to show that the direct axioms imply the layered structure. -/
noncomputable def AdinkraDirect.toLayered (A : AdinkraDirect V N) : AdinkraLayered V N where
  -- Topology layer
  graph := A.graph
  decAdj := A.decAdj
  connected := A.connected
  parity := A.parity
  bipartite := A.ax_odd
  regular := A.isRegularOfDegree
  -- Chromotopology layer
  edgeColor := A.edgeColor
  colorRegular := A.ax_regular
  fourCycleAxiom := A.ax_fourCycle
  -- Ranked layer
  height := A.height
  heightDiff := A.ax_unimod
  heightParity := by
    intro v w hadj hdiff
    -- Height differs by 1 and edges are odd → parity differs
    exact (A.ax_odd v w hadj).symm
  -- Dashed layer
  dashing := A.dashing
  oddDashing := A.ax_oddCycles

/-! ### Main equivalence theorem -/

/-- The two Adinkra definitions are equivalent.
    Layered → Direct → Layered gives back the original (up to definitional equality).
    Direct → Layered → Direct gives back the original (up to definitional equality). -/
theorem adinkra_equiv :
    (∀ (A : AdinkraLayered V N), A.toDirect.toLayered.graph = A.graph) ∧
    (∀ (A : AdinkraDirect V N), A.toLayered.toDirect.graph = A.graph) := by
  constructor
  · intro A
    rfl
  · intro A
    rfl

/-- Layered and Direct definitions have the same underlying graph. -/
theorem layered_direct_same_graph (A : AdinkraLayered V N) :
    A.toDirect.graph = A.graph := rfl

/-- Direct and Layered definitions have the same underlying graph. -/
theorem direct_layered_same_graph (A : AdinkraDirect V N) :
    A.toLayered.graph = A.graph := rfl

/-! ### Correspondence of axioms -/

/-- Layered's bipartite property is exactly Direct's ax_odd. -/
theorem bipartite_iff_odd (A : AdinkraLayered V N) :
    A.bipartite = A.toDirect.ax_odd := rfl

/-- Layered's heightDiff property is exactly Direct's ax_unimod. -/
theorem heightDiff_iff_unimod (A : AdinkraLayered V N) :
    A.heightDiff = A.toDirect.ax_unimod := rfl

/-- Layered's colorRegular property is exactly Direct's ax_regular. -/
theorem colorRegular_iff_regular (A : AdinkraLayered V N) :
    A.colorRegular = A.toDirect.ax_regular := rfl

/-- Layered's oddDashing property is exactly Direct's ax_oddCycles. -/
theorem oddDashing_iff_oddCycles (A : AdinkraLayered V N) :
    A.oddDashing = A.toDirect.ax_oddCycles := rfl

/-! ### Layered/Direct → IsAdinkra conversions -/

/-- Helper: convert ZMod 2 parity to Fin 2 for coloring. -/
private def parityToFin2 (x : ZMod 2) : Fin 2 :=
  if x = 0 then 0 else 1

/-- In ZMod 2, x ≠ 0 implies x = 1. -/
private lemma zmod2_ne_zero_eq_one {x : ZMod 2} (h : x ≠ 0) : x = 1 := by
  fin_cases x <;> simp_all

/-- Helper: construct IsBipartite from a bipartite labeling. -/
private lemma isBipartite_of_labeling {V : Type*} {G : SimpleGraph V}
    (parity : V → ZMod 2) (hbip : IsBipartiteLabeling G parity) : G.IsBipartite := by
  have valid : ∀ {v w : V}, G.Adj v w → parityToFin2 (parity v) ≠ parityToFin2 (parity w) := by
    intro v w hadj
    simp only [parityToFin2]
    have hne := hbip v w hadj
    split_ifs with h1 h2 h2
    · exact absurd (h1.trans h2.symm) hne
    · decide
    · decide
    · have hv1 := zmod2_ne_zero_eq_one h1
      have hw1 := zmod2_ne_zero_eq_one h2
      exact absurd (hv1.trans hw1.symm) hne
  exact ⟨SimpleGraph.Coloring.mk (parityToFin2 ∘ parity) (fun hadj => valid hadj)⟩

/-- Convert Layered definition to IsChromotopology predicate. -/
theorem AdinkraLayered.isChromotopology (A : AdinkraLayered V N) :
    A.graph.IsChromotopology N A.edgeColor where
  connected := A.connected
  bipartite := isBipartite_of_labeling A.parity A.bipartite
  regular := A.regular
  colorRegular := A.colorRegular
  fourCycleAxiom := A.fourCycleAxiom

/-- Convert Layered definition to IsAdinkra predicate. -/
theorem AdinkraLayered.isAdinkra (A : AdinkraLayered V N) :
    A.graph.IsAdinkra N A.edgeColor A.dashing where
  chromotopology := A.isChromotopology
  oddDashing := A.oddDashing

/-- Convert Direct definition to IsChromotopology predicate. -/
theorem AdinkraDirect.isChromotopology (A : AdinkraDirect V N) :
    A.graph.IsChromotopology N A.edgeColor where
  connected := A.connected
  bipartite := isBipartite_of_labeling A.parity A.ax_odd
  regular := A.isRegularOfDegree
  colorRegular := A.ax_regular
  fourCycleAxiom := A.ax_fourCycle

/-- Convert Direct definition to IsAdinkra predicate. -/
theorem AdinkraDirect.isAdinkra (A : AdinkraDirect V N) :
    A.graph.IsAdinkra N A.edgeColor A.dashing where
  chromotopology := A.isChromotopology
  oddDashing := A.ax_oddCycles

/-! ### IsAdinkra → AdinkraLayered conversion -/

/-- Extract a parity function from IsBipartite (which is Colorable 2).
    Maps Fin 2 coloring values to ZMod 2. -/
noncomputable def parityFromBipartite' {V : Type*} {G : SimpleGraph V}
    (hbip : G.IsBipartite) : V → ZMod 2 :=
  fun v => (hbip.toColoring (by decide : 2 ≤ Fintype.card (Fin 2)) v).val

/-- The parity function extracted from bipartite satisfies the bipartite labeling property. -/
lemma parityFromBipartite'_valid {V : Type*} {G : SimpleGraph V}
    (hbip : G.IsBipartite) :
    IsBipartiteLabeling G (parityFromBipartite' hbip) := by
  intro v w hadj
  unfold parityFromBipartite'
  -- The coloring maps adjacent vertices to different colors
  set col := hbip.toColoring (by decide : 2 ≤ Fintype.card (Fin 2)) with hcol
  have hne := col.valid hadj
  intro heq
  apply hne
  -- heq : ↑(col v).val = ↑(col w).val in ZMod 2
  -- Since col v, col w : Fin 2, their vals are 0 or 1
  -- In ZMod 2, ↑0 = 0 and ↑1 = 1, so equal vals means equal Fin 2 values
  have hv : (col v).val < 2 := (col v).isLt
  have hw : (col w).val < 2 := (col w).isLt
  ext
  have hv' : (col v).val = (col v).val % 2 := by omega
  have hw' : (col w).val = (col w).val % 2 := by omega
  rw [hv', hw']
  have h := congr_arg ZMod.val heq
  simp only [ZMod.val_natCast] at h
  exact h

/-- Height function defined as graph distance from a chosen base vertex.
    Uses a fixed arbitrary vertex from Nonempty (obtained from Connected). -/
noncomputable def heightFromDist {V : Type*} {G : SimpleGraph V}
    (hconn : G.Connected) : V → ℤ :=
  fun v => (G.dist hconn.nonempty.some v : ℤ)

/-- In a bipartite connected graph, adjacent vertices have distances of opposite parity
    from any fixed vertex. -/
lemma bipartite_dist_parity_ne {V : Type*} {G : SimpleGraph V}
    (hbip : G.IsBipartite) (hconn : G.Connected)
    {v w : V} (hadj : G.Adj v w) (u : V) :
    (G.dist u v) % 2 ≠ (G.dist u w) % 2 := by
  -- Use the characterization: bipartite ⟺ all cycles have even length
  have hloop : ∀ (x : V) (w : G.Walk x x), Even w.length :=
    SimpleGraph.two_colorable_iff_forall_loop_even.mp hbip
  -- Suppose for contradiction that distances have the same parity
  intro h_same_parity
  -- Get shortest paths from u to v and from u to w
  obtain ⟨pv, hpv_dist⟩ := hconn.exists_walk_length_eq_dist u v
  obtain ⟨pw, hpw_dist⟩ := hconn.exists_walk_length_eq_dist u w
  -- Construct a closed walk: u → v → w → u
  -- Walk from u to v, then edge v→w, then reverse of walk u to w
  let edge_vw : G.Walk v w := SimpleGraph.Walk.cons hadj SimpleGraph.Walk.nil
  let loop : G.Walk u u := pv.append (edge_vw.append pw.reverse)
  -- The loop length is dist(u,v) + 1 + dist(u,w)
  have hlen : loop.length = G.dist u v + 1 + G.dist u w := by
    simp only [loop, SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_reverse]
    rw [hpv_dist, hpw_dist]
    simp only [edge_vw, SimpleGraph.Walk.length_cons, SimpleGraph.Walk.length_nil]
    ring
  -- By bipartite property, all closed walks have even length
  have heven := hloop u loop
  rw [hlen] at heven
  -- If dist u v ≡ dist u w (mod 2), then dist u v + 1 + dist u w is odd
  -- Same parity means: dist u v % 2 = dist u w % 2
  -- (dist u v + dist u w) % 2 = 0, so (dist u v + dist u w) + 1 is odd
  have hodd : ¬ Even (G.dist u v + 1 + G.dist u w) := by
    rw [Nat.not_even_iff_odd, Nat.odd_iff]
    -- Goal: (dist u v + 1 + dist u w) % 2 = 1
    have hsum : (G.dist u v + G.dist u w) % 2 = 0 := by omega
    omega
  exact hodd heven

/-- Adjacent vertices in a connected bipartite graph have distance difference exactly 1. -/
lemma adj_dist_diff_one {V : Type*} {G : SimpleGraph V}
    (hbip : G.IsBipartite) (hconn : G.Connected) (u : V)
    {v w : V} (hadj : G.Adj v w) :
    G.dist u w = G.dist u v + 1 ∨ G.dist u w + 1 = G.dist u v := by
  -- By Adj.diff_dist_adj, we have three cases
  rcases hadj.diff_dist_adj with heq | hplus | hminus
  · -- Case: dist u w = dist u v
    -- This contradicts bipartite_dist_parity_ne
    exfalso
    have hparity := bipartite_dist_parity_ne hbip hconn hadj u
    rw [heq] at hparity
    exact hparity rfl
  · -- Case: dist u w = dist u v + 1
    left; exact hplus
  · -- Case: dist u w = dist u v - 1, equivalently dist u v = dist u w + 1
    right
    -- hminus : G.dist u w = G.dist u v - 1
    -- This means G.dist u v ≥ 1 and G.dist u w + 1 = G.dist u v
    -- We need to be careful with natural number subtraction
    have hparity := bipartite_dist_parity_ne hbip hconn hadj u
    omega

/-- Height from distance satisfies the height difference axiom: |h(w) - h(v)| = 1 for adjacent v, w. -/
lemma heightFromDist_diff {V : Type*} {G : SimpleGraph V}
    (hbip : G.IsBipartite) (hconn : G.Connected)
    {v w : V} (hadj : G.Adj v w) :
    |heightFromDist hconn w - heightFromDist hconn v| = 1 := by
  unfold heightFromDist
  let u := hconn.nonempty.some
  rcases adj_dist_diff_one hbip hconn u hadj with h | h
  · -- dist u w = dist u v + 1
    have heq : (G.dist u w : ℤ) - (G.dist u v : ℤ) = 1 := by omega
    rw [heq]
    rfl
  · -- dist u w + 1 = dist u v
    have heq : (G.dist u w : ℤ) - (G.dist u v : ℤ) = -1 := by omega
    rw [heq]
    rfl

end Adinkra

/-! ### IsAdinkra → Layered and existence theorems -/

namespace SimpleGraph.IsAdinkra

open Adinkra

/-- Convert IsAdinkra predicate to Layered bundled structure. -/
noncomputable def toAdinkraLayered {V : Type*} [DecidableEq V] [Fintype V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {N : ℕ}
    {c : EdgeColoring G N} {d : EdgeDashing G}
    (h : G.IsAdinkra N c d) : AdinkraLayered V N where
  -- Topology layer
  graph := G
  decAdj := inferInstance
  connected := h.chromotopology.connected
  parity := parityFromBipartite' h.chromotopology.bipartite
  bipartite := parityFromBipartite'_valid h.chromotopology.bipartite
  regular := h.chromotopology.regular
  -- Chromotopology layer
  edgeColor := c
  colorRegular := h.chromotopology.colorRegular
  fourCycleAxiom := h.chromotopology.fourCycleAxiom
  -- Ranked layer
  height := heightFromDist h.chromotopology.connected
  heightDiff := fun _ _ hadj => heightFromDist_diff h.chromotopology.bipartite h.chromotopology.connected hadj
  heightParity := fun _ w hadj _ => (parityFromBipartite'_valid h.chromotopology.bipartite _ w hadj).symm
  -- Dashed layer
  dashing := d
  oddDashing := h.oddDashing

/-- Converting to Layered and back to IsAdinkra recovers the graph, coloring, and dashing. -/
theorem toAdinkraLayered_components {V : Type*} [DecidableEq V] [Fintype V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {N : ℕ}
    {c : EdgeColoring G N} {d : EdgeDashing G}
    (h : G.IsAdinkra N c d) :
    h.toAdinkraLayered.graph = G ∧
    h.toAdinkraLayered.edgeColor = c ∧
    h.toAdinkraLayered.dashing = d :=
  ⟨rfl, rfl, rfl⟩

/-- The Layered structure constructed from IsAdinkra satisfies IsAdinkra. -/
theorem toAdinkraLayered_isAdinkra {V : Type*} [DecidableEq V] [Fintype V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {N : ℕ}
    {c : EdgeColoring G N} {d : EdgeDashing G}
    (h : G.IsAdinkra N c d) :
    h.toAdinkraLayered.graph.IsAdinkra N h.toAdinkraLayered.edgeColor h.toAdinkraLayered.dashing := by
  -- The graph, edgeColor, and dashing are the same, so this is definitionally h
  exact h

/-- Every Adinkra admits a ranked structure via distance-based height (Hanging Gardens). -/
theorem exists_ranked {V : Type*} [DecidableEq V] [Fintype V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {N : ℕ}
    {c : EdgeColoring G N} {d : EdgeDashing G}
    (h : G.IsAdinkra N c d) :
    ∃ height : V → ℤ, G.IsRankedAdinkra N c d height :=
  ⟨heightFromDist h.chromotopology.connected,
   h,
   fun _ _ hadj => heightFromDist_diff h.chromotopology.bipartite h.chromotopology.connected hadj⟩

/-- Valise height: maps parity to integers {0, 1}.
    Uses the Fin 2 coloring value directly (which is 0 or 1). -/
noncomputable def valiseHeight {V : Type*} {G : SimpleGraph V}
    (hbip : G.IsBipartite) : V → ℤ :=
  fun v => ((hbip.toColoring (by decide : 2 ≤ Fintype.card (Fin 2)) v).val : ℤ)

/-- Every Adinkra admits a valise structure via parity-based height. -/
theorem exists_valise {V : Type*} [DecidableEq V] [Fintype V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {N : ℕ}
    {c : EdgeColoring G N} {d : EdgeDashing G}
    (h : G.IsAdinkra N c d) :
    ∃ height : V → ℤ, G.IsValise N c d height := by
  use valiseHeight h.chromotopology.bipartite
  constructor
  · exact h
  · -- Height is 0 or 1
    intro v
    simp only [valiseHeight]
    set col := h.chromotopology.bipartite.toColoring (by decide : 2 ≤ Fintype.card (Fin 2)) with hcol
    have hlt : (col v).val < 2 := (col v).isLt
    omega
  · -- Height difference is 1 for adjacent vertices
    intro v w hadj
    simp only [valiseHeight]
    set col := h.chromotopology.bipartite.toColoring (by decide : 2 ≤ Fintype.card (Fin 2)) with hcol
    have hv_lt : (col v).val < 2 := (col v).isLt
    have hw_lt : (col w).val < 2 := (col w).isLt
    -- The coloring maps adjacent to different colors (Fin 2)
    have hcol_ne : col v ≠ col w := col.valid hadj
    -- So their vals are different and both < 2
    have hval_ne : (col v).val ≠ (col w).val := fun heq => hcol_ne (Fin.ext heq)
    -- With vals in {0, 1} and different, the absolute difference is 1
    -- Case analysis: (col v).val and (col w).val are each 0 or 1, and they're different
    interval_cases hv : (col v).val <;> interval_cases hw : (col w).val <;> simp_all

end SimpleGraph.IsAdinkra
