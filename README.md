# trace-logic-lean

[![thread](https://img.shields.io/badge/%F0%9F%A7%B5-how%20it%20works-1DA1F2)](https://x.com/thevelvetmonke)
[![Lean 4](https://img.shields.io/badge/Lean-4.28.0-blue)](https://lean-lang.org/)
[![Mathlib](https://img.shields.io/badge/Mathlib-v4.28.0-purple)](https://github.com/leanprover-community/mathlib4)
[![License: MIT](https://img.shields.io/badge/License-MIT-green.svg)](LICENSE)
[![Proofs](https://img.shields.io/badge/proofs-Phase%205%20%2F%200%20sorry-brightgreen)](TraceLogic)

Lean 4 / Mathlib formalisation of Phase 5 Hoffman trace logic for finite Markov chains.

## What this is, and why it matters

The headline theorem is `trace_tower_transient` in `RequestProject/TraceLogicPhase5.lean`. For a matrix with two hidden-state layers, it proves that eliminating the first layer and then the second produces the same trace matrix as eliminating their combined hidden block in one step.

The underlying `trace_tower` theorem establishes the Schur-complement composition identity from three invertibility hypotheses. Phase 5 defines a transient hidden block as a nonnegative matrix for which some power has all row sums strictly below one, proves that `1 - A` is invertible from this condition, and supplies those results to the tower theorem.

Transience is required for all three blocks appearing in the staged calculation: the first hidden block, the hidden block after the first trace, and the combined hidden block. The headline equality does not itself assert that the input or output is row-stochastic, and it uses this finite-power row-sum definition rather than a spectral-radius characterization.

## Mathematical Setting

The library works with finite row-stochastic Markov transition matrices over `ℝ`, decomposed into visible and hidden states. It defines the visible-visible, visible-hidden, hidden-visible, and hidden-hidden blocks, and the trace matrix

```lean
P_VV + P_VH * (1 - P_HH)⁻¹ * P_HV
```

as a Schur-complement-style effective transition matrix on visible states. It also includes nonnegativity predicates and a matrix operator norm wrapper via `Matrix.toEuclideanCLM`.

## Theorems Proved

| Name | Statement |
| --- | --- |
| `hidden_block_transient` | If `‖P_HH‖ < 1`, then `I - P_HH` is invertible. |
| `neumann_series` | Under `‖P_HH‖ < 1`, the inverse `(I - P_HH)⁻¹` exists as the hidden-block resolvent. |
| `row_stochastic_mulVec_ones` | A row-stochastic matrix maps the all-ones vector to the all-ones vector. |
| `blockHV_mulVec_ones` | The hidden-visible and hidden-hidden blocks satisfy the hidden-row all-ones identity. |
| `blockVV_blockVH_mulVec_ones` | The visible-visible and visible-hidden blocks satisfy the visible-row all-ones identity. |
| `IsNonneg.mul` | Products of nonnegative matrices are nonnegative. |
| `IsNonneg.add` | Sums of nonnegative matrices are nonnegative. |
| `IsNonneg.submatrix` | Submatrices of nonnegative matrices are nonnegative. |
| `trace_nonneg` | Under the stated Phase 1 hypotheses, the trace matrix is nonnegative. |
| `inv_blockHV_mulVec_ones` | The hidden-block inverse identity used in the trace row-sum proof. |
| `trace_row_sum` | Each row of the trace matrix sums to `1`. |
| `trace_row_stochastic` | The trace matrix is row-stochastic. |
| `trace_order_refl` | Trace order is reflexive in the Phase 1 skeleton. |
| `trace_order` | Entrywise dominance order on matrices: `A <= B` iff `A i j <= B i j` for all entries. |
| `trace_order_trans` | Transitivity of the entrywise dominance order, proved by `le_trans`. |
| `trace_order_Trans` | `Trans` instance for the entrywise dominance order, enabling `calc` chains. |

## Target 5 Scope

Target 5 proves transitivity of the **entrywise dominance order**:

```lean
trace_order A B := forall i j, A i j <= B i j
```

This is not the Schur-complement / trace-quotient order. The deeper trace-quotient direction is handled separately in Phase 3 through identities such as

```text
Tr_H2 (Tr_H1 P) = Tr_(H1+H2) P
```

requires a block-matrix-inversion formalisation for nested hidden-state eliminations.

## Phase 3: Trace Tower

Phase 3 proves the **Trace Tower Property**, also called the Schur-complement composition law:

```lean
trace_tower :
  traceTwo P = traceMatrix P
```

This states that tracing out `h1` and then `h2` agrees with tracing out the combined hidden block `h1 ⊕ h2` in one step. The theorem assumes the three invertibility conditions required for the Schur complements to be defined:

- `IsUnit (1 - blockHH (reindexForTrace P))`
- `IsUnit (1 - blockHH (traceMatrix (reindexForTrace P)))`
- `IsUnit (1 - blockHH P)`

The proof is zero-sorry. Because Mathlib does not currently provide the full 2x2 block-matrix inversion formula needed here, the development proves roughly fifteen block-equation helper lemmas, including the reindexing block identities, the `Y1`/`Y2` elimination equations, the `Q_matrix` block identities, and the final correction identity used to assemble the tower law.

Phase 3 also introduces the trace-semantic order:

```lean
trace_sem_le A B
```

This means that `B` is obtained from `A` by extending with finitely many hidden states and applying `traceMatrix`. Reflexivity is proved by the empty-hidden witness, and `trace_sem_le_implies_trace_order` proves that, under nonnegativity hypotheses on the witness matrix and hidden-block inverse, the trace-semantic order refines the entrywise dominance order.

## Phase 4: Semantic Transitivity

Phase 4 proves `trace_sem_le_trans`. The theorem composes a witness `P1` on `n ⊕ Fin k1` and a witness `P2` on `n ⊕ Fin k2` into a combined hidden-state witness, using six private helper lemmas for hidden-type reindexing, block-diagonal inverses, and Schur-correction splitting.

The transitivity result is unconditional modulo the pre-existing invertibility hypotheses inherent to the Schur complement. No definitions were changed and no positivity or nonnegativity assumptions were added.

## Phase 5: Transient Hidden Blocks

Phase 5 discharges the Schur-complement invertibility hypotheses for transient hidden blocks. It introduces:

- `IsStrictlySubstochastic`: entrywise nonnegative square matrices whose row sums are all strictly less than `1`.
- `IsTransientHidden`: entrywise nonnegative square matrices whose some power has all row sums strictly less than `1`.
- `mulVec_one_sub_injective`: injectivity of `(1 - A).mulVec` for strictly substochastic `A`.
- `isUnit_one_sub_of_strictly_substochastic`: `1 - A` is a unit for strictly substochastic `A`.
- `isUnit_one_sub_of_transient`: `1 - A` is a unit for transient hidden blocks.
- `trace_row_stochastic_substochastic`: trace row-stochasticity without a separate invertibility hypothesis.
- `trace_tower_substochastic`: the trace tower law with invertibility discharged from strict substochasticity.
- `trace_sem_le_trans_substochastic`: trace-semantic order transitivity with invertibility discharged from strict substochasticity.
- `trace_tower_transient`: the trace tower law with invertibility discharged from transient-hidden-block hypotheses.
- `trace_sem_le_trans_transient`: trace-semantic order transitivity with invertibility discharged from transient-hidden-block hypotheses.

For all transient Markov-chain hidden blocks in this formal sense, the trace tower and trace-semantic transitivity results are unconditional: the required inverses are proved from the finite-power row-sum escape condition rather than assumed separately. The proof avoids Perron-Frobenius by reducing the transient case to the same maximum-entry argument applied to `A^N`.

## Future Work

Optional future work is to connect this finite-power row-sum definition of transience to spectral-radius and Perron-Frobenius formulations once Mathlib has more infrastructure for nonnegative matrices.

## Building

```bash
lake exe cache get
lake build
```

## Verification

The Phase 5 source compiles cleanly with Mathlib v4.28.0 and contains no `sorry` or `admit`.
## Part of the Lean proof corpus

One of a family of small, machine-checked Lean 4 developments. Index: [velvetmonkey/lean](https://github.com/velvetmonkey/lean) ([live index](https://velvetmonkey.github.io/lean)).
