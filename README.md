# trace-logic-lean

[![Lean 4](https://img.shields.io/badge/Lean-4.28.0-blue)](https://lean-lang.org/)
[![Mathlib](https://img.shields.io/badge/Mathlib-v4.28.0-purple)](https://github.com/leanprover-community/mathlib4)
[![License: MIT](https://img.shields.io/badge/License-MIT-green.svg)](LICENSE)
[![Proofs](https://img.shields.io/badge/proofs-Phase%201%20compiled%20%2F%20Target%205%20open-yellowgreen)](TraceLogic)

Lean 4 / Mathlib formalisation of Phase 1 Hoffman trace logic for finite Markov chains.

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
| `trace_order_trans` | Phase 2 target: transitivity is represented by the Aristotle placeholder theorem and proof sketch. This is a formalisation gap, not a mathematical gap. |

## Phase 2 Gap

`trace_order_trans` is the only open target from the Aristotle run. In the imported Phase 1 file it is preserved exactly as supplied: a placeholder statement with a proof sketch, awaiting the full transitivity formalisation in Phase 2.

## Building

```bash
lake exe cache get
lake build
```

## Verification

The Phase 1 source is expected to compile cleanly with Mathlib v4.28.0. The only intended open formalisation target is `trace_order_trans`.
