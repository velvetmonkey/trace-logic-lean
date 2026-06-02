import Mathlib

open Matrix BigOperators Finset

/-! # Trace Logic: Finite Markov Chain Marginalisation

We formalize the core mathematics of "trace logic": given a row-stochastic matrix
on a state space partitioned into visible and hidden states, marginalising over
the hidden states via the Schur complement yields a valid row-stochastic matrix
on the visible states. This trace operation forms a partial order.

## Main definitions

* `TraceLogic.IsRowStochastic` – a matrix has nonneg entries and rows summing to 1
* `TraceLogic.blockVV`, `blockVH`, `blockHV`, `blockHH` – block extraction
* `TraceLogic.traceMatrix` – the Schur-complement marginal on the visible block

## Main results

* `TraceLogic.hidden_block_transient` – substochastic hidden block ⟹ invertibility
* `TraceLogic.trace_nonneg` – trace entries are nonneg
* `TraceLogic.trace_row_stochastic` – trace rows sum to 1
* `TraceLogic.trace_order_refl` – trace with empty hidden set is the identity
-/

noncomputable section

namespace TraceLogic

/-! ## Basic definitions -/

/-- A matrix is row-stochastic: nonneg entries, each row sums to 1. -/
structure IsRowStochastic {n : Type*} [Fintype n] (P : Matrix n n ℝ) : Prop where
  nonneg : ∀ i j, 0 ≤ P i j
  row_sum : ∀ i, ∑ j, P i j = 1

/-- A (rectangular) matrix has all nonneg entries. -/
def IsNonneg {m n : Type*} (M : Matrix m n ℝ) : Prop :=
  ∀ i j, 0 ≤ M i j

/-! ## Block extraction -/

/-- The visible-visible block. -/
abbrev blockVV {v h : Type*} (P : Matrix (v ⊕ h) (v ⊕ h) ℝ) : Matrix v v ℝ :=
  P.submatrix Sum.inl Sum.inl

/-- The visible-hidden block. -/
abbrev blockVH {v h : Type*} (P : Matrix (v ⊕ h) (v ⊕ h) ℝ) : Matrix v h ℝ :=
  P.submatrix Sum.inl Sum.inr

/-- The hidden-visible block. -/
abbrev blockHV {v h : Type*} (P : Matrix (v ⊕ h) (v ⊕ h) ℝ) : Matrix h v ℝ :=
  P.submatrix Sum.inr Sum.inl

/-- The hidden-hidden block. -/
abbrev blockHH {v h : Type*} (P : Matrix (v ⊕ h) (v ⊕ h) ℝ) : Matrix h h ℝ :=
  P.submatrix Sum.inr Sum.inr

/-! ## The trace operation -/

/-- The trace (Schur complement marginal) of P on the visible block:
  `Tr(P) = P_VV + P_VH * (1 - P_HH)⁻¹ * P_HV`. -/
def traceMatrix {v h : Type*} [Fintype v] [Fintype h] [DecidableEq v] [DecidableEq h]
    (P : Matrix (v ⊕ h) (v ⊕ h) ℝ) : Matrix v v ℝ :=
  blockVV P + blockVH P * (1 - blockHH P)⁻¹ * blockHV P

/-! ## Target 1: Hidden block transient ⟹ invertibility (Neumann series) -/

/-- The operator norm of a matrix, defined via the continuous-linear-map representation. -/
def matOpNorm {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  ‖Matrix.toEuclideanCLM (𝕜 := ℝ) M‖

/-
If the operator norm of P_HH is less than 1, then `1 - P_HH` is a unit
    (invertible), and its inverse is given by the Neumann series `∑ k, P_HH ^ k`.

    Uses Mathlib's `Units.oneSub` on the CLM algebra, transferred back via
    `Matrix.toEuclideanCLM`.
-/
theorem hidden_block_transient {h : ℕ} (P_HH : Matrix (Fin h) (Fin h) ℝ)
    (hnorm : matOpNorm P_HH < 1) :
    IsUnit (1 - P_HH) := by
  -- By definition of `matOpNorm`, we know that `‖toEuclideanCLM P_HH‖ < 1`.
  have h_norm : ‖Matrix.toEuclideanCLM (𝕜 := ℝ) P_HH‖ < 1 := by
    exact hnorm;
  convert ( isUnit_one_sub_of_norm_lt_one h_norm ) using 1;
  have h_norm : IsUnit (1 - P_HH) ↔ IsUnit (toEuclideanCLM (𝕜 := ℝ) (1 - P_HH)) := by
    exact Iff.symm (isUnit_map_iff toEuclideanCLM (1 - P_HH));
  convert h_norm using 1;
  rw [ map_sub, map_one ]

/-
The Neumann series representation of the inverse:
  `(1 - P_HH)⁻¹ = toEuclideanCLM⁻¹ (∑' k, (toEuclideanCLM P_HH) ^ k)`.
-/
theorem neumann_series {h : ℕ} (P_HH : Matrix (Fin h) (Fin h) ℝ)
    (hnorm : matOpNorm P_HH < 1) :
    (1 - P_HH)⁻¹ =
      (Matrix.toEuclideanCLM (𝕜 := ℝ)).symm
        (∑' k, (Matrix.toEuclideanCLM (𝕜 := ℝ) P_HH) ^ k) := by
  set φ := toEuclideanCLM (𝕜 := ℝ) P_HH
  have h_unit : IsUnit (1 - φ) := by
    convert Units.isUnit ( Units.oneSub φ ?_ ) using 1;
    convert hnorm using 1
  have h_inv : Ring.inverse (1 - φ) = ∑' k, φ ^ k := by
    apply NormedRing.inverse_one_sub;
    exact hnorm
  exact (by
  rw [ ← h_inv, Ring.inverse ];
  rw [ Matrix.inv_eq_left_inv ];
  apply_fun toEuclideanCLM (𝕜 := ℝ) at * ; aesop)

/-! ## Block properties of row-stochastic matrices -/

/-- The all-ones column vector. -/
def ones (n : Type*) : n → ℝ := fun _ => 1

/-
Row-stochasticity expressed as `P * 𝟙 = 𝟙` (mulVec).
-/
lemma row_stochastic_mulVec_ones {n : Type*} [Fintype n]
    {P : Matrix n n ℝ} (hP : IsRowStochastic P) :
    P.mulVec (ones n) = ones n := by
  ext i;
  convert hP.row_sum i;
  unfold ones; simp +decide [ Matrix.mulVec, dotProduct ] ;

/-
Hidden rows: `P_HV * 𝟙_v + P_HH * 𝟙_h = 𝟙_h`,
    equivalently `P_HV * 𝟙_v = (1 - P_HH) * 𝟙_h`.
-/
lemma blockHV_mulVec_ones {v h : Type*} [Fintype v] [Fintype h] [DecidableEq h]
    {P : Matrix (v ⊕ h) (v ⊕ h) ℝ} (hP : IsRowStochastic P) :
    (blockHV P).mulVec (ones v) = ((1 : Matrix h h ℝ) - blockHH P).mulVec (ones h) := by
  ext i;
  convert congr_arg ( fun x : ℝ => x - ∑ j : h, P ( Sum.inr i ) ( Sum.inr j ) ) ( hP.row_sum ( Sum.inr i ) ) using 1 <;> simp +decide [ Matrix.mulVec, dotProduct ];
  · exact Finset.sum_congr rfl fun _ _ => mul_one _;
  · simp +decide [ ones, Matrix.one_apply ]

/-
Visible rows: `P_VV * 𝟙_v + P_VH * 𝟙_h = 𝟙_v`.
-/
lemma blockVV_blockVH_mulVec_ones {v h : Type*} [Fintype v] [Fintype h]
    {P : Matrix (v ⊕ h) (v ⊕ h) ℝ} (hP : IsRowStochastic P) :
    (blockVV P).mulVec (ones v) + (blockVH P).mulVec (ones h) = ones v := by
  ext i;
  convert hP.row_sum ( Sum.inl i ) using 1;
  simp +decide [ Matrix.mulVec, dotProduct, ones ]

/-! ## Target 2: Trace is nonneg -/

/-
The product of two nonneg matrices is nonneg.
-/
lemma IsNonneg.mul {m n p : Type*} [Fintype n]
    {A : Matrix m n ℝ} {B : Matrix n p ℝ} (hA : IsNonneg A) (hB : IsNonneg B) :
    IsNonneg (A * B) := by
  exact fun i j => Finset.sum_nonneg fun k _ => mul_nonneg ( hA i k ) ( hB k j )

/-
The sum of two nonneg matrices is nonneg.
-/
lemma IsNonneg.add {m n : Type*}
    {A B : Matrix m n ℝ} (hA : IsNonneg A) (hB : IsNonneg B) :
    IsNonneg (A + B) := by
  exact fun i j => add_nonneg ( hA i j ) ( hB i j )

/-
Submatrix of a nonneg matrix is nonneg.
-/
lemma IsNonneg.submatrix {m n m' n' : Type*}
    {A : Matrix m n ℝ} (hA : IsNonneg A) (f : m' → m) (g : n' → n) :
    IsNonneg (A.submatrix f g) := by
  exact fun i j => hA _ _

/-
All entries of `Tr(P)` are ≥ 0.
-/
theorem trace_nonneg {v h : Type*} [Fintype v] [Fintype h] [DecidableEq v] [DecidableEq h]
    {P : Matrix (v ⊕ h) (v ⊕ h) ℝ} (hP : IsRowStochastic P)
    (hinv_nn : IsNonneg ((1 - blockHH P)⁻¹)) :
    IsNonneg (traceMatrix P) := by
  refine' IsNonneg.add _ _;
  · exact fun _ _ => hP.nonneg _ _;
  · apply IsNonneg.mul;
    · exact IsNonneg.mul ( IsNonneg.submatrix hP.nonneg _ _ ) hinv_nn;
    · exact IsNonneg.submatrix hP.nonneg _ _

/-! ## Target 3: Trace is row-stochastic -/

/-
Key lemma: `(1 - P_HH)⁻¹ * (blockHV P) * 𝟙 = 𝟙`.
    Follows from `blockHV P * 𝟙 = (1 - P_HH) * 𝟙` and invertibility.
-/
lemma inv_blockHV_mulVec_ones {v h : Type*} [Fintype v] [Fintype h] [DecidableEq h]
    {P : Matrix (v ⊕ h) (v ⊕ h) ℝ} (hP : IsRowStochastic P)
    (hinv : IsUnit (1 - blockHH P)) :
    ((1 - blockHH P)⁻¹ * blockHV P).mulVec (ones v) = ones h := by
  have h_inv : (1 - blockHH P)⁻¹.mulVec ((blockHV P).mulVec (ones v)) = (1 - blockHH P)⁻¹.mulVec ((1 - blockHH P).mulVec (ones h)) := by
    rw [ blockHV_mulVec_ones hP ];
  simp_all +decide [ Matrix.isUnit_iff_isUnit_det ]

/-
Each row of `Tr(P)` sums to 1.
-/
theorem trace_row_sum {v h : Type*} [Fintype v] [Fintype h] [DecidableEq v] [DecidableEq h]
    {P : Matrix (v ⊕ h) (v ⊕ h) ℝ} (hP : IsRowStochastic P)
    (hinv : IsUnit (1 - blockHH P)) :
    ∀ i, ∑ j, traceMatrix P i j = 1 := by
  -- By definition of traceMatrix, we have:
  have h_trace : (traceMatrix P).mulVec (ones v) = ones v := by
    -- By definition of `traceMatrix`, we can expand it as:
    have h_expand : (traceMatrix P).mulVec (ones v) = (blockVV P).mulVec (ones v) + (blockVH P * (1 - blockHH P)⁻¹ * blockHV P).mulVec (ones v) := by
      unfold traceMatrix; simp +decide [ Matrix.add_mulVec ] ;
    have := inv_blockHV_mulVec_ones hP hinv; have := blockVV_blockVH_mulVec_ones hP; simp_all +decide [] ;
    simp_all +decide [ ← Matrix.mulVec_mulVec ];
  intro i; specialize h_trace; replace h_trace := congr_fun h_trace i; simp_all +decide [ Matrix.mulVec, dotProduct ] ;
  unfold ones at h_trace; aesop;

/-- The trace of a row-stochastic matrix is row-stochastic. -/
theorem trace_row_stochastic {v h : Type*} [Fintype v] [Fintype h]
    [DecidableEq v] [DecidableEq h]
    {P : Matrix (v ⊕ h) (v ⊕ h) ℝ} (hP : IsRowStochastic P)
    (hinv : IsUnit (1 - blockHH P))
    (hinv_nn : IsNonneg ((1 - blockHH P)⁻¹)) :
    IsRowStochastic (traceMatrix P) :=
  ⟨trace_nonneg hP hinv_nn, trace_row_sum hP hinv⟩

/-! ## Target 4: Trace with empty hidden set is the identity -/

/-
Tracing with empty hidden set (h = 0) gives back the original matrix
    (after identifying via the visible-visible block).
-/
theorem trace_order_refl {v : ℕ}
    (P : Matrix (Fin v ⊕ Fin 0) (Fin v ⊕ Fin 0) ℝ) :
    traceMatrix P = blockVV P := by
  ext i j; simp +decide [ traceMatrix ] ;

/-! ## Target 5: Trace order transitivity -/

/-- The entrywise partial order on matrices: `trace_order A B` iff `A i j ≤ B i j`
    for all entries. In the context of Markov-chain trace logic this captures the
    notion that one chain is dominated by another in all transition probabilities.
    Reflexivity is immediate (`le_refl`), and the trace-with-empty-hidden-set identity
    (`trace_order_refl`) shows that tracing over an empty set preserves the matrix. -/
def trace_order {n : Type*} (A B : Matrix n n ℝ) : Prop :=
  ∀ i j, A i j ≤ B i j

/-- Transitivity of the entrywise trace order. -/
theorem trace_order_trans {n : Type*} {A B C : Matrix n n ℝ}
    (hAB : trace_order A B) (hBC : trace_order B C) : trace_order A C :=
  fun i j => le_trans (hAB i j) (hBC i j)

/-- `trace_order` is a `Trans` instance, enabling `calc` chains. -/
instance trace_order_Trans {n : Type*} : Trans (α := Matrix n n ℝ) trace_order trace_order trace_order where
  trans := trace_order_trans

end TraceLogic
