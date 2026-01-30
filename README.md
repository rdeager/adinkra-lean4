# Adinkra Formalization for Mathlib

A Lean4/mathlib formalization of **Adinkras**—decorated bipartite graphs from supersymmetry theory.

## What is an Adinkra?

**Physics motivation:** Adinkras are combinatorial representations of supersymmetric multiplets, encoding the transformation rules between bosonic and fermionic fields.

**Mathematical definition:** An Adinkra is a finite, connected, bipartite, N-regular simple graph equipped with:
- An **N-edge-coloring** where each vertex has exactly one incident edge of each color
- A **dashing** function assigning solid (0) or dashed (1) to each edge
- The **odd 4-cycle property**: every 2-colored 4-cycle has dashing sum ≡ 1 (mod 2)

## Building

```bash
# Install dependencies (requires elan and Lean 4)
lake exe cache get
lake build
```

## File Structure

| File | Lines | Contents |
|------|-------|----------|
| `Adinkra/Basic.lean` | 105 | Core types: `EdgeColoring`, `EdgeDashing`, `FourCycle`, `TwoColoredFourCycle` |
| `Adinkra/Adinkra.lean` | 284 | Predicate definitions: `IsChromotopology`, `IsAdinkra`, `IsRankedAdinkra`, `IsValise`, `qOp` theorems |
| `Adinkra/Layered.lean` | 376 | Bundled layered definition: `Topology`, `Chromotopology`, `RankedChromotopology`, `AdinkraLayered` |
| `Adinkra/Direct.lean` | 125 | Bundled direct definition: `AdinkraDirect` with 4 axioms |
| `Adinkra/Equiv.lean` | 480 | Equivalence proofs, `exists_ranked`, `exists_valise` |
| **Total** | 1370 | |

## Main Definitions

### `SimpleGraph.IsChromotopology`
The base structure: a chromotopology (Adinkra without dashing).

```lean
structure IsChromotopology (N : ℕ) (c : EdgeColoring G N) : Prop where
  connected : G.Connected
  bipartite : G.IsBipartite
  regular : G.IsRegularOfDegree N
  colorRegular : IsColorRegular G N c
  fourCycleAxiom : ∀ i j : Fin N, i ≠ j → ∀ v : V,
    ∃! cyc : TwoColoredFourCycle G N c, cyc.v₀ = v ∧ cyc.color₁ = i ∧ cyc.color₂ = j
```

### `SimpleGraph.IsAdinkra`
A chromotopology with dashing satisfying the odd 4-cycle axiom.

```lean
structure IsAdinkra (N : ℕ) (c : EdgeColoring G N) (d : EdgeDashing G) : Prop where
  chromotopology : G.IsChromotopology N c
  oddDashing : ∀ (cyc : TwoColoredFourCycle G N c), cyc.toFourCycle.dashingSum d = 1
```

## Key Theorems

### Hanging Garden Theorem (Partial Proof)

**`IsAdinkra.exists_ranked`**: Every Adinkra admits a height function.
```lean
theorem exists_ranked (h : G.IsAdinkra N c d) :
    ∃ height : V → ℤ, G.IsRankedAdinkra N c d height
```

**`IsAdinkra.exists_valise`**: Every Adinkra admits a valise structure.
```lean
theorem exists_valise (h : G.IsAdinkra N c d) :
    ∃ height : V → ℤ, G.IsValise N c d height
```

### Algebraic Characterization

**`IsChromotopology.qOp_comm`**: The q_i operators (unique neighbor by color) commute.
```lean
theorem qOp_comm (i j : Fin N) (v : V) :
    h.qOp i (h.qOp j v) = h.qOp j (h.qOp i v)
```

**`AdinkraLayered.qTilde_anticommute_iff`**: The signed q̃_i operators anticommute iff dashing is odd.

This connects Adinkras to Clifford algebras: the anticommutation encodes {Q_i, Q_j} = 2δ_{ij}H.

## Three Equivalent Definitions

All three styles proven equivalent:

| Style | Structure | Source |
|-------|-----------|--------|
| **Predicate** (`IsAdinkra`) | Mathlib-compatible predicate on `SimpleGraph` | This formalization |
| **Layered** (`AdinkraLayered`) | Topology → Chromotopology → RankedChromotopology → Adinkra | Zhang (2011) |
| **Direct** (`AdinkraDirect`) | 4-axiom bundled structure | Eager et al. (2024) |

## References

### Papers
- **Zhang (2011)**: "Adinkras for Mathematicians", [arXiv:1111.6055](https://arxiv.org/abs/1111.6055)
  - Primary source for layered definition and algebraic characterization
- **Eager, Noja, Senghaas, Walcher (2024)**: "Adinkras and Pure Spinors", [arXiv:2404.07167](https://arxiv.org/abs/2404.07167)
  - Direct 4-axiom definition (Definition 2.3)

### Mathlib
- [Naming conventions](https://leanprover-community.github.io/contribute/naming.html)
- [Style guidelines](https://leanprover-community.github.io/contribute/style.html)
- [SimpleGraph docs](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Combinatorics/SimpleGraph/Basic.html)

## License

Apache 2.0
