import Mathlib
import RequestProject.TraceLogic

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

/-! # Phase 3: Trace Tower Property (Composition Law) and Trace-Semantic Order

This file builds on the Phase 1–2 trace-logic formalization in `TraceLogic.lean`,
adding:

1. **Partial trace as a first-class operation**: `sumReindex`, `reindexForTrace`,
   `traceTwo` generalise `traceMatrix` so the traced-out block is a parameter.

2. **Trace tower property (composition law)**:
   `Tr_{h2}(Tr_{h1}(P)) = Tr_{h1 ⊕ h2}(P)`,
   proved via block-equation elimination and the Schur-complement quotient identity.

3. **Trace-semantic order** (`trace_sem_le`): `A ≤_ts B` iff `B` is obtained from
   `A` by extending with hidden states and marginalising. Reflexivity is proved;
   relationship to the entrywise order is established.

## Proof architecture for the composition law

The proof avoids the full 2×2 block matrix inversion formula. Instead it
works with the defining equation `(1 - P_HH) · Y = P_HV` and decomposes it
into block equations on the h1- and h2-rows of `Y`. Block elimination
then expresses `Y₂` as `(1 - blockHH Q)⁻¹ · blockHV Q` where `Q` is the
intermediate (first-step) trace. The rest is algebraic reassembly.
-/

open Matrix BigOperators Finset

noncomputable section

namespace TraceLogic

/-! ## Phase 3 definitions -/

/-! ### Reindexing equivalences for multi-step traces -/

/-- Equivalence that reindexes `v ⊕ (h1 ⊕ h2)` as `(v ⊕ h2) ⊕ h1`,
    enabling a two-step trace: first trace out h1, then trace out h2. -/
def sumReindex (v h1 h2 : Type*) : v ⊕ (h1 ⊕ h2) ≃ (v ⊕ h2) ⊕ h1 :=
  (Equiv.sumCongr (Equiv.refl v) (Equiv.sumComm h1 h2)).trans (Equiv.sumAssoc v h2 h1).symm

/-- Reindex a matrix from `v ⊕ (h1 ⊕ h2)` to `(v ⊕ h2) ⊕ h1` coordinates,
    preparing for a two-step trace (first trace out h1, then trace out h2). -/
def reindexForTrace {v h1 h2 : Type*}
    (P : Matrix (v ⊕ (h1 ⊕ h2)) (v ⊕ (h1 ⊕ h2)) ℝ) :
    Matrix ((v ⊕ h2) ⊕ h1) ((v ⊕ h2) ⊕ h1) ℝ :=
  P.submatrix (sumReindex v h1 h2).symm (sumReindex v h1 h2).symm

/-- The two-step trace: first trace out h1, then trace out h2,
    yielding a matrix on v. -/
def traceTwo {v h1 h2 : Type*} [Fintype v] [Fintype h1] [Fintype h2]
    [DecidableEq v] [DecidableEq h1] [DecidableEq h2]
    (P : Matrix (v ⊕ (h1 ⊕ h2)) (v ⊕ (h1 ⊕ h2)) ℝ) : Matrix v v ℝ :=
  traceMatrix (traceMatrix (reindexForTrace P))

/-! ### Nine-block decomposition -/

variable {v h1 h2 : Type*} [Fintype v] [Fintype h1] [Fintype h2]
    [DecidableEq v] [DecidableEq h1] [DecidableEq h2]

/-- P_{v,h1} block -/
abbrev P_vh1 (P : Matrix (v ⊕ (h1 ⊕ h2)) (v ⊕ (h1 ⊕ h2)) ℝ) : Matrix v h1 ℝ :=
  P.submatrix Sum.inl (Sum.inr ∘ Sum.inl)

/-- P_{v,h2} block -/
abbrev P_vh2 (P : Matrix (v ⊕ (h1 ⊕ h2)) (v ⊕ (h1 ⊕ h2)) ℝ) : Matrix v h2 ℝ :=
  P.submatrix Sum.inl (Sum.inr ∘ Sum.inr)

/-- P_{h1,v} block -/
abbrev P_h1v (P : Matrix (v ⊕ (h1 ⊕ h2)) (v ⊕ (h1 ⊕ h2)) ℝ) : Matrix h1 v ℝ :=
  P.submatrix (Sum.inr ∘ Sum.inl) Sum.inl

/-- P_{h2,v} block -/
abbrev P_h2v (P : Matrix (v ⊕ (h1 ⊕ h2)) (v ⊕ (h1 ⊕ h2)) ℝ) : Matrix h2 v ℝ :=
  P.submatrix (Sum.inr ∘ Sum.inr) Sum.inl

/-- P_{h1,h1} block -/
abbrev P_h1h1 (P : Matrix (v ⊕ (h1 ⊕ h2)) (v ⊕ (h1 ⊕ h2)) ℝ) : Matrix h1 h1 ℝ :=
  P.submatrix (Sum.inr ∘ Sum.inl) (Sum.inr ∘ Sum.inl)

/-- P_{h1,h2} block -/
abbrev P_h1h2 (P : Matrix (v ⊕ (h1 ⊕ h2)) (v ⊕ (h1 ⊕ h2)) ℝ) : Matrix h1 h2 ℝ :=
  P.submatrix (Sum.inr ∘ Sum.inl) (Sum.inr ∘ Sum.inr)

/-- P_{h2,h1} block -/
abbrev P_h2h1 (P : Matrix (v ⊕ (h1 ⊕ h2)) (v ⊕ (h1 ⊕ h2)) ℝ) : Matrix h2 h1 ℝ :=
  P.submatrix (Sum.inr ∘ Sum.inr) (Sum.inr ∘ Sum.inl)

/-- P_{h2,h2} block -/
abbrev P_h2h2 (P : Matrix (v ⊕ (h1 ⊕ h2)) (v ⊕ (h1 ⊕ h2)) ℝ) : Matrix h2 h2 ℝ :=
  P.submatrix (Sum.inr ∘ Sum.inr) (Sum.inr ∘ Sum.inr)

/-- P_{v,v} block -/
abbrev P_vv (P : Matrix (v ⊕ (h1 ⊕ h2)) (v ⊕ (h1 ⊕ h2)) ℝ) : Matrix v v ℝ :=
  P.submatrix Sum.inl Sum.inl

/-- The intermediate matrix Q = traceMatrix (reindexForTrace P). -/
abbrev Q_matrix (P : Matrix (v ⊕ (h1 ⊕ h2)) (v ⊕ (h1 ⊕ h2)) ℝ) :
    Matrix (v ⊕ h2) (v ⊕ h2) ℝ :=
  traceMatrix (reindexForTrace P)

/-- Abbreviation for Inv1 = (1 - P_{h1,h1})⁻¹ -/
abbrev Inv1 (P : Matrix (v ⊕ (h1 ⊕ h2)) (v ⊕ (h1 ⊕ h2)) ℝ) : Matrix h1 h1 ℝ :=
  (1 - P_h1h1 P)⁻¹

/-! ## Block identities for reindexForTrace -/

lemma reindex_blockHH (P : Matrix (v ⊕ (h1 ⊕ h2)) (v ⊕ (h1 ⊕ h2)) ℝ) :
    blockHH (reindexForTrace P) = P.submatrix (Sum.inr ∘ Sum.inl) (Sum.inr ∘ Sum.inl) := by
  ext i j
  simp [reindexForTrace, sumReindex, blockHH, Equiv.sumAssoc, Equiv.sumComm, Equiv.sumCongr]

lemma reindex_blockHV (P : Matrix (v ⊕ (h1 ⊕ h2)) (v ⊕ (h1 ⊕ h2)) ℝ) :
    blockHV (reindexForTrace P) = fun (i : h1) (j : v ⊕ h2) =>
      match j with
      | Sum.inl jv => P (Sum.inr (Sum.inl i)) (Sum.inl jv)
      | Sum.inr jh2 => P (Sum.inr (Sum.inl i)) (Sum.inr (Sum.inr jh2)) := by
  ext i (j | j) <;>
    simp [reindexForTrace, sumReindex, blockHV, Equiv.sumAssoc, Equiv.sumComm, Equiv.sumCongr]

lemma reindex_blockVH (P : Matrix (v ⊕ (h1 ⊕ h2)) (v ⊕ (h1 ⊕ h2)) ℝ) :
    blockVH (reindexForTrace P) = fun (i : v ⊕ h2) (j : h1) =>
      match i with
      | Sum.inl iv => P (Sum.inl iv) (Sum.inr (Sum.inl j))
      | Sum.inr ih2 => P (Sum.inr (Sum.inr ih2)) (Sum.inr (Sum.inl j)) := by
  ext (i | i) j <;>
    simp [reindexForTrace, sumReindex, blockVH, Equiv.sumAssoc, Equiv.sumComm, Equiv.sumCongr]

omit [Fintype v] [Fintype h1] [Fintype h2] [DecidableEq v] [DecidableEq h1] [DecidableEq h2] in
lemma reindex_blockVV (P : Matrix (v ⊕ (h1 ⊕ h2)) (v ⊕ (h1 ⊕ h2)) ℝ) :
    blockVV (reindexForTrace P) = fun (i : v ⊕ h2) (j : v ⊕ h2) =>
      match i, j with
      | Sum.inl iv, Sum.inl jv => P (Sum.inl iv) (Sum.inl jv)
      | Sum.inl iv, Sum.inr jh2 => P (Sum.inl iv) (Sum.inr (Sum.inr jh2))
      | Sum.inr ih2, Sum.inl jv => P (Sum.inr (Sum.inr ih2)) (Sum.inl jv)
      | Sum.inr ih2, Sum.inr jh2 => P (Sum.inr (Sum.inr ih2)) (Sum.inr (Sum.inr jh2)) := by
  ext (i | i) (j | j) <;>
    simp [reindexForTrace, sumReindex, blockVV, Equiv.sumAssoc, Equiv.sumComm, Equiv.sumCongr]

lemma reindex_blockHH_eq (P : Matrix (v ⊕ (h1 ⊕ h2)) (v ⊕ (h1 ⊕ h2)) ℝ) :
    blockHH (reindexForTrace P) = P_h1h1 P :=
  reindex_blockHH P

lemma hunit_h1_iff (P : Matrix (v ⊕ (h1 ⊕ h2)) (v ⊕ (h1 ⊕ h2)) ℝ) :
    IsUnit (1 - blockHH (reindexForTrace P)) ↔ IsUnit (1 - P_h1h1 P) := by
  rw [reindex_blockHH_eq]

/-! ## Block equation decomposition

We define `Y = (1 - blockHH P)⁻¹ * blockHV P` and decompose the defining
equation `(1 - blockHH P) * Y = blockHV P` into h1- and h2-row components. -/

abbrev Y_full (P : Matrix (v ⊕ (h1 ⊕ h2)) (v ⊕ (h1 ⊕ h2)) ℝ) :
    Matrix (h1 ⊕ h2) v ℝ :=
  (1 - blockHH P)⁻¹ * blockHV P

abbrev Y1 (P : Matrix (v ⊕ (h1 ⊕ h2)) (v ⊕ (h1 ⊕ h2)) ℝ) : Matrix h1 v ℝ :=
  (Y_full P).submatrix Sum.inl id

abbrev Y2 (P : Matrix (v ⊕ (h1 ⊕ h2)) (v ⊕ (h1 ⊕ h2)) ℝ) : Matrix h2 v ℝ :=
  (Y_full P).submatrix Sum.inr id

lemma Y_full_eq (P : Matrix (v ⊕ (h1 ⊕ h2)) (v ⊕ (h1 ⊕ h2)) ℝ)
    (hunit : IsUnit (1 - blockHH P)) :
    (1 - blockHH P) * Y_full P = blockHV P := by
  simp_all +decide [Matrix.isUnit_iff_isUnit_det]

lemma block_eq_h1 (P : Matrix (v ⊕ (h1 ⊕ h2)) (v ⊕ (h1 ⊕ h2)) ℝ)
    (hunit : IsUnit (1 - blockHH P)) :
    (1 - P_h1h1 P) * Y1 P - P_h1h2 P * Y2 P = P_h1v P := by
  ext i j
  have := congr_fun (congr_fun (Y_full_eq P hunit) (Sum.inl i)) j
  simp_all +decide [Matrix.mul_apply, Fintype.sum_sum_type]
  simpa [Matrix.one_apply, sub_mul, mul_add, Finset.sum_add_distrib,
    Finset.mul_sum, Finset.sum_mul, sub_eq_add_neg] using this

lemma block_eq_h2 (P : Matrix (v ⊕ (h1 ⊕ h2)) (v ⊕ (h1 ⊕ h2)) ℝ)
    (hunit : IsUnit (1 - blockHH P)) :
    (1 - P_h2h2 P) * Y2 P - P_h2h1 P * Y1 P = P_h2v P := by
  ext i j
  convert congr_arg (fun x : Matrix (h1 ⊕ h2) v ℝ => x (Sum.inr i) j) (Y_full_eq P hunit) using 1
  simp +decide [Matrix.mul_apply, Fintype.sum_sum_type]
  simp +decide [Matrix.one_apply, sub_mul]; ring

lemma Y1_eq (P : Matrix (v ⊕ (h1 ⊕ h2)) (v ⊕ (h1 ⊕ h2)) ℝ)
    (hunit : IsUnit (1 - blockHH P))
    (hunit1 : IsUnit (1 - P_h1h1 P)) :
    Y1 P = Inv1 P * (P_h1v P + P_h1h2 P * Y2 P) := by
  have hY1 : (1 - P_h1h1 P) * Y1 P = P_h1v P + P_h1h2 P * Y2 P := by
    convert congr_arg (fun x => x + P_h1h2 P * Y2 P) (block_eq_h1 P hunit) using 1; abel_nf
  cases hunit1.nonempty_invertible
  simp +decide [← hY1, ← Matrix.mul_assoc]

lemma Y2_schur_eq (P : Matrix (v ⊕ (h1 ⊕ h2)) (v ⊕ (h1 ⊕ h2)) ℝ)
    (hunit : IsUnit (1 - blockHH P))
    (hunit1 : IsUnit (1 - P_h1h1 P)) :
    (1 - P_h2h2 P - P_h2h1 P * Inv1 P * P_h1h2 P) * Y2 P =
    P_h2v P + P_h2h1 P * Inv1 P * P_h1v P := by
  have h_subst : (1 - P_h2h2 P) * Y2 P -
      P_h2h1 P * (Inv1 P * (P_h1v P + P_h1h2 P * Y2 P)) = P_h2v P := by
    rw [← Y1_eq P hunit hunit1, ← block_eq_h2 P hunit]
  simp_all +decide [Matrix.mul_add, Matrix.sub_mul, Matrix.mul_assoc]
  exact eq_add_of_sub_eq h_subst ▸ by abel1

omit [Fintype v] [DecidableEq v] in
lemma blockVH_Y_decomp (P : Matrix (v ⊕ (h1 ⊕ h2)) (v ⊕ (h1 ⊕ h2)) ℝ) :
    blockVH P * Y_full P = P_vh1 P * Y1 P + P_vh2 P * Y2 P := by
  ext i j; simp +decide [Matrix.mul_apply, Fintype.sum_sum_type]

lemma traceMatrix_decomp (P : Matrix (v ⊕ (h1 ⊕ h2)) (v ⊕ (h1 ⊕ h2)) ℝ) :
    traceMatrix P = P_vv P + P_vh1 P * Y1 P + P_vh2 P * Y2 P := by
  convert congr_arg (fun x : Matrix v v ℝ => P_vv P + x) (blockVH_Y_decomp P) using 1
  · unfold traceMatrix Y_full; rw [Matrix.mul_assoc]
  · rw [add_assoc]

/-! ## Q_matrix block identities -/

lemma Q_blockVV (P : Matrix (v ⊕ (h1 ⊕ h2)) (v ⊕ (h1 ⊕ h2)) ℝ) :
    blockVV (Q_matrix P) = P_vv P + P_vh1 P * Inv1 P * P_h1v P := by
  ext i j; simp [Matrix.mul_apply]
  unfold Q_matrix traceMatrix
  simp +decide [Matrix.mul_apply, blockVV, blockVH, blockHV,
    reindex_blockVV, reindex_blockVH, reindex_blockHV, reindex_blockHH_eq]

lemma Q_blockVH (P : Matrix (v ⊕ (h1 ⊕ h2)) (v ⊕ (h1 ⊕ h2)) ℝ) :
    blockVH (Q_matrix P) = P_vh2 P + P_vh1 P * Inv1 P * P_h1h2 P := by
  congr! 2

lemma Q_blockHV (P : Matrix (v ⊕ (h1 ⊕ h2)) (v ⊕ (h1 ⊕ h2)) ℝ) :
    blockHV (Q_matrix P) = P_h2v P + P_h2h1 P * Inv1 P * P_h1v P := by
  ext i j
  simp +decide [Matrix.mul_apply, blockHV, reindex_blockHH_eq,
    reindex_blockVV, reindex_blockHV, reindex_blockVH, traceMatrix]

lemma Q_blockHH (P : Matrix (v ⊕ (h1 ⊕ h2)) (v ⊕ (h1 ⊕ h2)) ℝ) :
    blockHH (Q_matrix P) = P_h2h2 P + P_h2h1 P * Inv1 P * P_h1h2 P := by
  congr! 3

lemma Q_one_sub_blockHH (P : Matrix (v ⊕ (h1 ⊕ h2)) (v ⊕ (h1 ⊕ h2)) ℝ) :
    1 - blockHH (Q_matrix P) = 1 - P_h2h2 P - P_h2h1 P * Inv1 P * P_h1h2 P := by
  rw [Q_blockHH]; simp [sub_sub, add_comm]

lemma Y2_eq_inv_blockHV_Q (P : Matrix (v ⊕ (h1 ⊕ h2)) (v ⊕ (h1 ⊕ h2)) ℝ)
    (hunit : IsUnit (1 - blockHH P))
    (hunit1 : IsUnit (1 - P_h1h1 P))
    (hunit2 : IsUnit (1 - blockHH (Q_matrix P))) :
    Y2 P = (1 - blockHH (Q_matrix P))⁻¹ * blockHV (Q_matrix P) := by
  convert congr_arg _ (Y2_schur_eq P hunit hunit1) using 1
  rw [← Q_one_sub_blockHH]
  cases hunit2.nonempty_invertible; aesop

lemma traceMatrix_eq_Q_plus_correction (P : Matrix (v ⊕ (h1 ⊕ h2)) (v ⊕ (h1 ⊕ h2)) ℝ)
    (hunit : IsUnit (1 - blockHH P))
    (hunit1 : IsUnit (1 - P_h1h1 P)) :
    traceMatrix P = blockVV (Q_matrix P) + blockVH (Q_matrix P) * Y2 P := by
  rw [traceMatrix_decomp, Q_blockVV, Q_blockVH]
  rw [Y1_eq P hunit hunit1]
  simp +decide [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
  abel1

/-! ## Trace tower property (composition law) -/

/-- **Trace Tower Property (Composition Law / Schur Complement Quotient Property)**.
    Tracing out h1 then h2 equals tracing out h1 ⊕ h2 in one step:
    `Tr_{h2}(Tr_{h1}(P)) = Tr_{h1 ⊕ h2}(P)`.

    **Hypotheses** (all genuinely required for the Schur complements to exist):
    - `hunit_h1`: `1 - P_{h1,h1}` is invertible (for the first trace step).
    - `hunit_h2`: `1 - (blockHH of first-step trace)` is invertible (for the second step).
    - `hunit_combined`: `1 - P_{h1⊕h2, h1⊕h2}` is invertible (for the combined trace).

    **Proof method**: block-equation elimination. We decompose
    `(1 - blockHH P) · Y = blockHV P` into h1- and h2-row equations,
    solve by elimination to express `Y₂ = (1 - blockHH Q)⁻¹ · blockHV Q`
    where `Q` is the first-step trace, then reassemble to show both sides
    equal `blockVV Q + blockVH Q · (1 - blockHH Q)⁻¹ · blockHV Q`. -/
theorem trace_tower {v h1 h2 : Type*} [Fintype v] [Fintype h1] [Fintype h2]
    [DecidableEq v] [DecidableEq h1] [DecidableEq h2]
    (P : Matrix (v ⊕ (h1 ⊕ h2)) (v ⊕ (h1 ⊕ h2)) ℝ)
    (hunit_h1 : IsUnit (1 - blockHH (reindexForTrace P)))
    (hunit_h2 : IsUnit (1 - blockHH (traceMatrix (reindexForTrace P))))
    (hunit_combined : IsUnit (1 - blockHH P)) :
    traceTwo P = traceMatrix P := by
  have hunit1 : IsUnit (1 - P_h1h1 P) := (hunit_h1_iff P).mp hunit_h1
  rw [traceMatrix_eq_Q_plus_correction P hunit_combined hunit1]
  rw [Y2_eq_inv_blockHV_Q P hunit_combined hunit1 hunit_h2]
  unfold traceTwo Q_matrix traceMatrix
  simp [Matrix.mul_assoc]

/-! ## Trace with empty hidden set (general version) -/

/-- Tracing with an empty hidden type yields the visible-visible block.
    Generalises `trace_order_refl` from `Fin v` to arbitrary `n`. -/
lemma traceMatrix_empty {n : Type*} [Fintype n] [DecidableEq n]
    (P : Matrix (n ⊕ Fin 0) (n ⊕ Fin 0) ℝ) :
    traceMatrix P = blockVV P := by
  unfold traceMatrix
  have hVH : blockVH P = 0 := by ext i j; exact (Fin.elim0 j)
  simp [hVH]

/-! ## Trace-semantic order -/

/-- The trace-semantic partial order: `trace_sem_le A B` iff `B` is obtained
    from `A` by extending with hidden states and marginalising via the Schur
    complement. Concretely, there exists `k : ℕ` and a matrix
    `P : Matrix (n ⊕ Fin k) (n ⊕ Fin k) ℝ` such that `blockVV P = A` and
    `traceMatrix P = B`.

    Intuitively, `trace_sem_le A B` means `B` is a "coarser" view of `A`
    that absorbs the effect of hidden-state transitions. -/
def trace_sem_le {n : Type*} [Fintype n] [DecidableEq n]
    (A B : Matrix n n ℝ) : Prop :=
  ∃ (k : ℕ) (P : Matrix (n ⊕ Fin k) (n ⊕ Fin k) ℝ),
    blockVV P = A ∧ traceMatrix P = B

/-- Reflexivity of the trace-semantic order. Taking k = 0 (no hidden states),
    any matrix is its own trace. -/
theorem trace_sem_le_refl {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) : trace_sem_le A A := by
  use 0, Matrix.fromBlocks A 0 0 0
  unfold blockVV traceMatrix; aesop

/-- The trace-semantic order refines the entrywise order when the witness
    matrix has nonneg entries and the hidden-block inverse is nonneg.
    Since `traceMatrix P = blockVV P + (nonneg correction)`, we get
    `blockVV P ≤ traceMatrix P` entrywise. -/
theorem trace_sem_le_implies_trace_order {n : Type*} [Fintype n] [DecidableEq n]
    {A B : Matrix n n ℝ}
    {k : ℕ} {P : Matrix (n ⊕ Fin k) (n ⊕ Fin k) ℝ}
    (hVV : blockVV P = A) (htr : traceMatrix P = B)
    (hP_nn : IsNonneg P)
    (hinv_nn : IsNonneg ((1 - blockHH P)⁻¹)) :
    trace_order A B := by
  intro i j; subst_vars; simp +decide [traceMatrix]
  exact IsNonneg.mul (IsNonneg.mul (IsNonneg.submatrix hP_nn _ _) hinv_nn)
    (IsNonneg.submatrix hP_nn _ _) i j

/-! ## Helpers for trace_sem_le_trans -/

/-
The inverse of a matrix commutes with submatrix by an equivalence.
-/
private lemma inv_submatrix_equiv {m₁ m₂ : Type*} [Fintype m₁] [Fintype m₂]
    [DecidableEq m₁] [DecidableEq m₂]
    (A : Matrix m₁ m₁ ℝ) (e : m₂ ≃ m₁) :
    (A.submatrix e e)⁻¹ = A⁻¹.submatrix e e := by
      by_cases h : IsUnit A.det <;> simp_all +decide [ Matrix.nonsing_inv_apply_not_isUnit ]

/-
traceMatrix is invariant under reindexing the hidden type by an equivalence.
-/
private lemma traceMatrix_reindex_hidden {n h₁ h₂ : Type*}
    [Fintype n] [Fintype h₁] [Fintype h₂]
    [DecidableEq n] [DecidableEq h₁] [DecidableEq h₂]
    (P : Matrix (n ⊕ h₁) (n ⊕ h₁) ℝ) (e : h₂ ≃ h₁) :
    let f : (n ⊕ h₂) → (n ⊕ h₁) := Equiv.sumCongr (Equiv.refl n) e
    traceMatrix (P.submatrix f f) = traceMatrix P := by
      convert Matrix.ext _;
      intro i j; unfold traceMatrix; simp +decide [ Matrix.mul_apply, Matrix.submatrix ] ;
      rw [ show ( 1 - of fun i j => P ( Sum.inr ( e i ) ) ( Sum.inr ( e j ) ) ) ⁻¹ = ( 1 - of fun i j => P ( Sum.inr i ) ( Sum.inr j ) ) ⁻¹.submatrix e e from ?_ ];
      · conv_rhs => rw [ ← Equiv.sum_comp e ] ;
        simp +decide [ Matrix.submatrix, Matrix.mul_apply ];
        exact Finset.sum_congr rfl fun _ _ => by rw [ ← Equiv.sum_comp e ] ;
      · convert inv_submatrix_equiv _ _ using 2;
        ext i j; simp +decide [ Matrix.submatrix ] ;
        simp +decide [ Matrix.one_apply, e.injective.eq_iff ]

/-
blockVV is invariant under reindexing the hidden type by an equivalence.
-/
private lemma blockVV_reindex_hidden {n h₁ h₂ : Type*}
    (P : Matrix (n ⊕ h₁) (n ⊕ h₁) ℝ) (e : h₂ ≃ h₁) :
    let f : (n ⊕ h₂) → (n ⊕ h₁) := Equiv.sumCongr (Equiv.refl n) e
    blockVV (P.submatrix f f) = blockVV P := by
      unfold blockVV; aesop;

/-- If there exists a witness matrix on `n ⊕ h` for an arbitrary finite hidden
    type `h`, then `trace_sem_le` holds (converting to `Fin k`). -/
private lemma trace_sem_le_of_exists {n h : Type*}
    [Fintype n] [DecidableEq n] [Fintype h] [DecidableEq h]
    {A B : Matrix n n ℝ} (P : Matrix (n ⊕ h) (n ⊕ h) ℝ)
    (hVV : blockVV P = A) (hTr : traceMatrix P = B) :
    trace_sem_le A B := by
  use Fintype.card h
  let e := Fintype.equivFin h
  let f : (n ⊕ Fin (Fintype.card h)) → (n ⊕ h) :=
    Equiv.sumCongr (Equiv.refl n) e.symm
  exact ⟨P.submatrix f f,
    (blockVV_reindex_hidden P e.symm).trans hVV,
    (traceMatrix_reindex_hidden P e.symm).trans hTr⟩

/-
The inverse of a block-diagonal `fromBlocks A 0 0 D` is `fromBlocks A⁻¹ 0 0 D⁻¹`
    when both blocks are units.
-/
private lemma fromBlocks_inv_diag {k₁ k₂ : Type*} [Fintype k₁] [Fintype k₂]
    [DecidableEq k₁] [DecidableEq k₂]
    (A : Matrix k₁ k₁ ℝ) (D : Matrix k₂ k₂ ℝ)
    (hA : IsUnit A) (hD : IsUnit D) :
    (Matrix.fromBlocks A 0 0 D)⁻¹ = Matrix.fromBlocks A⁻¹ 0 0 D⁻¹ := by
      rw [ Matrix.inv_eq_right_inv ];
      simp_all +decide [ Matrix.isUnit_iff_isUnit_det ];
      simp +decide [ fromBlocks_multiply, hA, hD, isUnit_iff_ne_zero ]

/-
The Schur correction for a block-diagonal hidden block splits as a sum.
    If VH = [VH₁ | VH₂], HV = [HV₁ ; HV₂], and
    Inv = fromBlocks Inv₁ 0 0 Inv₂, then
    VH * Inv * HV = VH₁ * Inv₁ * HV₁ + VH₂ * Inv₂ * HV₂.
-/
private lemma schur_correction_split {n k₁ k₂ : Type*}
    [Fintype n] [Fintype k₁] [Fintype k₂] [DecidableEq k₁] [DecidableEq k₂]
    (VH₁ : Matrix n k₁ ℝ) (VH₂ : Matrix n k₂ ℝ)
    (HV₁ : Matrix k₁ n ℝ) (HV₂ : Matrix k₂ n ℝ)
    (Inv₁ : Matrix k₁ k₁ ℝ) (Inv₂ : Matrix k₂ k₂ ℝ)
    (VH : Matrix n (k₁ ⊕ k₂) ℝ)
    (HV : Matrix (k₁ ⊕ k₂) n ℝ)
    (hVH : ∀ i j₁, VH i (Sum.inl j₁) = VH₁ i j₁)
    (hVH' : ∀ i j₂, VH i (Sum.inr j₂) = VH₂ i j₂)
    (hHV : ∀ i₁ j, HV (Sum.inl i₁) j = HV₁ i₁ j)
    (hHV' : ∀ i₂ j, HV (Sum.inr i₂) j = HV₂ i₂ j) :
    VH * Matrix.fromBlocks Inv₁ 0 0 Inv₂ * HV =
    VH₁ * Inv₁ * HV₁ + VH₂ * Inv₂ * HV₂ := by
      ext i j;
      simp +decide [ Matrix.mul_apply, Fintype.sum_sum_type, * ]

/-- Transitivity of the trace-semantic order.

    Given `trace_sem_le A B` via hidden block `Fin k₁` and
    `trace_sem_le B C` via hidden block `Fin k₂`, we construct a combined
    matrix on `n ⊕ (Fin k₁ ⊕ Fin k₂)` whose visible block is `A` and whose
    trace is `C`, then convert to `Fin (k₁ + k₂)` via `trace_sem_le_of_exists`.

    **Construction**: The combined witness has block-diagonal hidden block
    `fromBlocks (blockHH P₁) 0 0 (blockHH P₂)`, with blockVH/blockHV
    assembled from P₁ and P₂. The Schur correction splits as a sum
    `(B - A) + (C - B) = C - A`, so `traceMatrix Q = A + (C - A) = C`.

    Requires invertibility of the hidden blocks at each step, stated as
    explicit hypotheses since they are genuinely needed for the Schur
    complements to be defined.

    **Unconditional** modulo the invertibility hypotheses (which are inherent
    to the trace/Schur complement being well-defined). No extra positivity
    or nonnegativity conditions were added. -/
theorem trace_sem_le_trans {n : Type*} [Fintype n] [DecidableEq n]
    {A B C : Matrix n n ℝ}
    (hAB : trace_sem_le A B) (hBC : trace_sem_le B C)
    (hunit_AB : ∀ (k : ℕ) (P : Matrix (n ⊕ Fin k) (n ⊕ Fin k) ℝ),
      blockVV P = A → traceMatrix P = B → IsUnit (1 - blockHH P))
    (hunit_BC : ∀ (k : ℕ) (P : Matrix (n ⊕ Fin k) (n ⊕ Fin k) ℝ),
      blockVV P = B → traceMatrix P = C → IsUnit (1 - blockHH P)) :
    trace_sem_le A C := by
  obtain ⟨k₁, P₁, hVV₁, hTr₁⟩ := hAB
  obtain ⟨k₂, P₂, hVV₂, hTr₂⟩ := hBC
  have hU₁ := hunit_AB k₁ P₁ hVV₁ hTr₁
  have hU₂ := hunit_BC k₂ P₂ hVV₂ hTr₂
  -- Define VH, HV, HH blocks for the combined witness on n ⊕ (Fin k₁ ⊕ Fin k₂)
  let VH : Matrix n (Fin k₁ ⊕ Fin k₂) ℝ := fun i j =>
    match j with | Sum.inl j₁ => blockVH P₁ i j₁ | Sum.inr j₂ => blockVH P₂ i j₂
  let HV : Matrix (Fin k₁ ⊕ Fin k₂) n ℝ := fun i j =>
    match i with | Sum.inl i₁ => blockHV P₁ i₁ j | Sum.inr i₂ => blockHV P₂ i₂ j
  let HH : Matrix (Fin k₁ ⊕ Fin k₂) (Fin k₁ ⊕ Fin k₂) ℝ :=
    Matrix.fromBlocks (blockHH P₁) 0 0 (blockHH P₂)
  let Q : Matrix (n ⊕ (Fin k₁ ⊕ Fin k₂)) (n ⊕ (Fin k₁ ⊕ Fin k₂)) ℝ :=
    Matrix.fromBlocks A VH HV HH
  -- Show blockVV Q = A
  have hVV_Q : blockVV Q = A := by ext i j; simp [Q, blockVV]
  -- Compute (1 - blockHH Q)⁻¹ using block-diagonal inverse
  have hHH_Q : blockHH Q = HH := by ext i j; simp [Q, blockHH]
  have h1HH : 1 - blockHH Q = Matrix.fromBlocks (1 - blockHH P₁) 0 0 (1 - blockHH P₂) := by
    rw [hHH_Q]; ext (i | i) (j | j) <;>
      simp [HH, Matrix.fromBlocks, Matrix.one_apply, Sum.inl.injEq, Sum.inr.injEq]
  have hInv : (1 - blockHH Q)⁻¹ =
      Matrix.fromBlocks (1 - blockHH P₁)⁻¹ 0 0 (1 - blockHH P₂)⁻¹ := by
    rw [h1HH]; exact fromBlocks_inv_diag _ _ hU₁ hU₂
  -- Compute the Schur correction
  have hVH_Q : blockVH Q = VH := by ext i j; simp [Q, blockVH]
  have hHV_Q : blockHV Q = HV := by ext i j; simp [Q, blockHV]
  have hCorr : blockVH Q * (1 - blockHH Q)⁻¹ * blockHV Q =
      blockVH P₁ * (1 - blockHH P₁)⁻¹ * blockHV P₁ +
      blockVH P₂ * (1 - blockHH P₂)⁻¹ * blockHV P₂ := by
    rw [hVH_Q, hHV_Q, hInv]
    exact schur_correction_split (blockVH P₁) (blockVH P₂) (blockHV P₁) (blockHV P₂)
      (1 - blockHH P₁)⁻¹ (1 - blockHH P₂)⁻¹ VH HV
      (fun i j₁ => rfl) (fun i j₂ => rfl) (fun i₁ j => rfl) (fun i₂ j => rfl)
  -- Assemble: traceMatrix Q = A + correction = A + (B-A) + (C-B) = C
  have hC₁ : blockVH P₁ * (1 - blockHH P₁)⁻¹ * blockHV P₁ = B - A := by
    have h : blockVV P₁ + blockVH P₁ * (1 - blockHH P₁)⁻¹ * blockHV P₁ = B := by
      rw [← hTr₁]; rfl
    rw [← h, hVV₁]; abel
  have hC₂ : blockVH P₂ * (1 - blockHH P₂)⁻¹ * blockHV P₂ = C - B := by
    have h : blockVV P₂ + blockVH P₂ * (1 - blockHH P₂)⁻¹ * blockHV P₂ = C := by
      rw [← hTr₂]; rfl
    rw [← h, hVV₂]; abel
  have hTr_Q : traceMatrix Q = C := by
    unfold traceMatrix; rw [hVV_Q, hCorr, hC₁, hC₂]; abel
  exact trace_sem_le_of_exists Q hVV_Q hTr_Q

end TraceLogic
