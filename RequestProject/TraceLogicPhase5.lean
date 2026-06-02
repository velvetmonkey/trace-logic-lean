import Mathlib
import RequestProject.TraceLogicPhase3

set_option linter.unusedSimpArgs false

/-! # Phase 5: Discharging Invertibility for Transient Markov Chains

This file proves that the invertibility hypothesis `IsUnit (1 - P_HH)` — which
conditions `traceMatrix`, `trace_tower`, and `trace_sem_le_trans` — holds
automatically for genuine transient Markov chains.

## Main results

### Clean case: strictly substochastic hidden block

* `IsStrictlySubstochastic` — entrywise nonneg, every row sum < 1.
* `isUnit_one_sub_of_strictly_substochastic` — if `P_HH` is strictly substochastic
  then `1 - P_HH` is a unit.

### General transient case

* `isUnit_one_sub_of_transient` — if there exists `N` such that every row sum of
  `A^N` is strictly less than 1, then `1 - A` is invertible. Proved without
  Perron-Frobenius, by reducing to the max-entry argument on `A^N`.

### Corollaries

* `trace_tower_substochastic` / `trace_tower_transient`
* `trace_sem_le_trans_substochastic` / `trace_sem_le_trans_transient`
-/

open Matrix BigOperators Finset

noncomputable section

namespace TraceLogic

/-! ## Strictly substochastic matrices -/

/-- A square matrix is strictly substochastic: nonneg entries and every row sum
    is strictly less than 1. -/
structure IsStrictlySubstochastic {n : Type*} [Fintype n]
    (A : Matrix n n ℝ) : Prop where
  nonneg : ∀ i j, 0 ≤ A i j
  row_sum_lt : ∀ i, ∑ j, A i j < 1

/-! ## Case 1: Strictly substochastic ⟹ IsUnit (1 - A) -/

theorem mulVec_one_sub_injective {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℝ} (hA : IsStrictlySubstochastic A) :
    Function.Injective (1 - A).mulVec := by
  have h_inv : ∀ x : n → ℝ, (1 - A).mulVec x = 0 → x = 0 := by
    intro x hx
    have h_abs : ∀ i, |x i| ≤ ∑ j, A i j * |x j| := by
      intro i
      have h_abs_i : |x i| = |∑ j, A i j * x j| := by
        simp_all +decide [ funext_iff, Matrix.mulVec, dotProduct ];
        simp_all +decide [ sub_mul, Matrix.one_apply ];
        rw [ sub_eq_zero.mp ( hx i ) ];
      exact h_abs_i.symm ▸ le_trans ( Finset.abs_sum_le_sum_abs _ _ ) ( Finset.sum_le_sum fun j _ => by rw [ abs_mul, abs_of_nonneg ( hA.nonneg i j ) ] );
    by_cases h_nonzero : ∃ i, x i ≠ 0;
    · obtain ⟨i₀, hi₀⟩ : ∃ i₀, ∀ i, |x i| ≤ |x i₀| := by
        simpa using Finset.exists_max_image Finset.univ ( fun i => |x i| ) ⟨ h_nonzero.choose, Finset.mem_univ _ ⟩;
      have h_abs_i₀ : |x i₀| ≤ (∑ j, A i₀ j) * |x i₀| := by
        exact le_trans ( h_abs i₀ ) ( by rw [ Finset.sum_mul _ _ _ ] ; exact Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left ( hi₀ j ) ( hA.nonneg i₀ j ) );
      exact False.elim ( h_nonzero.elim fun i hi => hi <| by nlinarith [ hA.row_sum_lt i₀, abs_pos.mpr hi, abs_pos.mpr ( show x i₀ ≠ 0 from fun hi₀' => hi <| by simp_all +decide [ funext_iff ] ) ] );
    · exact funext fun i => Classical.not_not.1 fun hi => h_nonzero ⟨ i, hi ⟩;
  exact fun x y hxy => sub_eq_zero.mp ( h_inv ( x - y ) ( by simpa [ Matrix.mulVec_sub ] using sub_eq_zero.mpr hxy ) )

/-- If `A` is strictly substochastic, then `1 - A` is a unit (invertible). -/
theorem isUnit_one_sub_of_strictly_substochastic {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℝ} (hA : IsStrictlySubstochastic A) :
    IsUnit (1 - A) := by
  rw [← Matrix.linearIndependent_cols_iff_isUnit]
  rw [← Matrix.mulVec_injective_iff]
  exact mulVec_one_sub_injective hA

/-! ## Case 2: General transient case -/

/-- A matrix `A` on hidden states is *transient* if it is nonneg and there exists
    `N` such that every row sum of `A^N` is strictly less than 1. -/
structure IsTransientHidden {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) : Prop where
  nonneg : ∀ i j, 0 ≤ A i j
  exists_N : ∃ N : ℕ, ∀ i, ∑ j, (A ^ N) i j < 1

/-
Power of a nonneg matrix is nonneg.
-/
theorem IsNonneg_pow {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℝ} (hA : ∀ i j, 0 ≤ A i j) (k : ℕ) :
    ∀ i j, 0 ≤ (A ^ k) i j := by
  induction' k with k ih <;> simp +decide [ *, pow_succ', Matrix.mul_apply ];
  · exact fun i j => by rw [ Matrix.one_apply ] ; split_ifs <;> norm_num;
  · exact fun i j => Finset.sum_nonneg fun _ _ => mul_nonneg ( hA _ _ ) ( ih _ _ )

/-
If `A.mulVec x = x` then `(A ^ k).mulVec x = x` for all `k`.
-/
theorem mulVec_pow_eq_of_mulVec_eq {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℝ} {x : n → ℝ} (h : A.mulVec x = x) (k : ℕ) :
    (A ^ k).mulVec x = x := by
  induction k <;> simp_all +decide [ pow_succ', Matrix.mulVec_mulVec ];
  simp_all +decide [ ← Matrix.mulVec_mulVec ]

/-
If `A` is transient, then `(1 - A).mulVec` is injective.

    **Proof**: Suppose `(1-A)x = 0`, i.e. `Ax = x`. By induction, `A^N x = x`.
    Since `A` is nonneg, `A^N` is nonneg. The transience hypothesis gives
    row sums of `A^N` < 1. The max-entry argument on `A^N` forces `x = 0`.
-/
theorem mulVec_one_sub_injective_of_transient {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℝ} (hA : IsTransientHidden A) :
    Function.Injective (1 - A).mulVec := by
  obtain ⟨ N, hN ⟩ := hA.exists_N;
  -- By the properties of the matrix exponential and the definition of transient hidden, we know that $(1 - A^N)$ is invertible.
  have h_inv : IsUnit (1 - A^N) := by
    apply isUnit_one_sub_of_strictly_substochastic;
    exact ⟨ fun i j => IsNonneg_pow hA.nonneg N i j, hN ⟩;
  -- Since $(1 - A^N)$ is invertible, $(1 - A)$ must also be invertible.
  have h_inv_A : IsUnit (1 - A) := by
    have h_inv_A : (1 - A) * (∑ i ∈ Finset.range N, A ^ i) = 1 - A ^ N := by
      rw [ mul_neg_geom_sum ];
    grind +splitImp;
  obtain ⟨ u, hu ⟩ := h_inv_A.exists_left_inv; intro x y hxy; apply_fun u.mulVec at hxy; aesop;

/-- If the hidden block is transient, then `1 - A` is invertible.

    Proved without Perron-Frobenius: from `(1-A)x=0` we get `Ax=x`, hence
    `A^N x = x` by induction. Since `A` nonneg implies `A^N` nonneg, the
    max-entry argument (same as for strictly substochastic) on `A^N` forces
    `x=0`. -/
theorem isUnit_one_sub_of_transient {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℝ} (hA : IsTransientHidden A) :
    IsUnit (1 - A) := by
  rw [← Matrix.linearIndependent_cols_iff_isUnit]
  rw [← Matrix.mulVec_injective_iff]
  exact mulVec_one_sub_injective_of_transient hA

/-- Strictly substochastic implies transient (with N = 1). -/
theorem IsStrictlySubstochastic.toTransient {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℝ} (hA : IsStrictlySubstochastic A) :
    IsTransientHidden A :=
  ⟨hA.nonneg, ⟨1, by simpa using hA.row_sum_lt⟩⟩

/-! ## Corollaries: unconditional results for strictly substochastic chains -/

/-- The trace of a row-stochastic matrix with strictly substochastic hidden block
    is row-stochastic. -/
theorem trace_row_stochastic_substochastic
    {v h : Type*} [Fintype v] [Fintype h] [DecidableEq v] [DecidableEq h]
    {P : Matrix (v ⊕ h) (v ⊕ h) ℝ} (hP : IsRowStochastic P)
    (hHH : IsStrictlySubstochastic (blockHH P))
    (hinv_nn : IsNonneg ((1 - blockHH P)⁻¹)) :
    IsRowStochastic (traceMatrix P) :=
  trace_row_stochastic hP (isUnit_one_sub_of_strictly_substochastic hHH) hinv_nn

/-- The trace tower property for matrices with strictly substochastic hidden
    blocks. -/
theorem trace_tower_substochastic
    {v h1 h2 : Type*} [Fintype v] [Fintype h1] [Fintype h2]
    [DecidableEq v] [DecidableEq h1] [DecidableEq h2]
    (P : Matrix (v ⊕ (h1 ⊕ h2)) (v ⊕ (h1 ⊕ h2)) ℝ)
    (hHH_h1 : IsStrictlySubstochastic (blockHH (reindexForTrace P)))
    (hHH_Q : IsStrictlySubstochastic (blockHH (traceMatrix (reindexForTrace P))))
    (hHH_combined : IsStrictlySubstochastic (blockHH P)) :
    traceTwo P = traceMatrix P :=
  trace_tower P
    (isUnit_one_sub_of_strictly_substochastic hHH_h1)
    (isUnit_one_sub_of_strictly_substochastic hHH_Q)
    (isUnit_one_sub_of_strictly_substochastic hHH_combined)

/-- Transitivity of the trace-semantic order for strictly substochastic
    witnesses. -/
theorem trace_sem_le_trans_substochastic {n : Type*} [Fintype n] [DecidableEq n]
    {A B C : Matrix n n ℝ}
    (hAB : trace_sem_le A B) (hBC : trace_sem_le B C)
    (hunit_AB : ∀ (k : ℕ) (P : Matrix (n ⊕ Fin k) (n ⊕ Fin k) ℝ),
      blockVV P = A → traceMatrix P = B →
      IsStrictlySubstochastic (blockHH P))
    (hunit_BC : ∀ (k : ℕ) (P : Matrix (n ⊕ Fin k) (n ⊕ Fin k) ℝ),
      blockVV P = B → traceMatrix P = C →
      IsStrictlySubstochastic (blockHH P)) :
    trace_sem_le A C :=
  trace_sem_le_trans hAB hBC
    (fun k P hVV hTr => isUnit_one_sub_of_strictly_substochastic (hunit_AB k P hVV hTr))
    (fun k P hVV hTr => isUnit_one_sub_of_strictly_substochastic (hunit_BC k P hVV hTr))

/-! ## Corollaries: unconditional results for transient chains -/

/-- The trace tower property for matrices with transient hidden blocks. -/
theorem trace_tower_transient
    {v h1 h2 : Type*} [Fintype v] [Fintype h1] [Fintype h2]
    [DecidableEq v] [DecidableEq h1] [DecidableEq h2]
    (P : Matrix (v ⊕ (h1 ⊕ h2)) (v ⊕ (h1 ⊕ h2)) ℝ)
    (hHH_h1 : IsTransientHidden (blockHH (reindexForTrace P)))
    (hHH_Q : IsTransientHidden (blockHH (traceMatrix (reindexForTrace P))))
    (hHH_combined : IsTransientHidden (blockHH P)) :
    traceTwo P = traceMatrix P :=
  trace_tower P
    (isUnit_one_sub_of_transient hHH_h1)
    (isUnit_one_sub_of_transient hHH_Q)
    (isUnit_one_sub_of_transient hHH_combined)

/-- Transitivity of the trace-semantic order for transient witnesses. -/
theorem trace_sem_le_trans_transient {n : Type*} [Fintype n] [DecidableEq n]
    {A B C : Matrix n n ℝ}
    (hAB : trace_sem_le A B) (hBC : trace_sem_le B C)
    (hunit_AB : ∀ (k : ℕ) (P : Matrix (n ⊕ Fin k) (n ⊕ Fin k) ℝ),
      blockVV P = A → traceMatrix P = B →
      IsTransientHidden (blockHH P))
    (hunit_BC : ∀ (k : ℕ) (P : Matrix (n ⊕ Fin k) (n ⊕ Fin k) ℝ),
      blockVV P = B → traceMatrix P = C →
      IsTransientHidden (blockHH P)) :
    trace_sem_le A C :=
  trace_sem_le_trans hAB hBC
    (fun k P hVV hTr => isUnit_one_sub_of_transient (hunit_AB k P hVV hTr))
    (fun k P hVV hTr => isUnit_one_sub_of_transient (hunit_BC k P hVV hTr))

end TraceLogic
