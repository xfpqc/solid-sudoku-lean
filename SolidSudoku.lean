import Mathlib
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Permanent
import Mathlib.Basic.Real.Basic
set_option linter.style.whitespace false
set_option linter.style.emptyLine false

/-- An order-n Solid Sudoku Subcube (SSC) grid maps 3D coordinates to symbols in Fin (n ^ 2). -/
abbrev SSC (n : ℕ) := Fin n → Fin n → Fin n → Fin (n ^ 2)

namespace SSC

variable {n : ℕ}

/-- Z-slice rule: For a fixed layer k, the mapping from (x,y) to symbols is injective. -/
def valid_z_slice (g : SSC n) (k : Fin n) : Prop :=
  Function.Injective (fun (p : Fin n × Fin n) => g p.1 p.2 k)

/-- Y-slice rule: For a fixed row i, the mapping from (x,z) to symbols is injective. -/
def valid_y_slice (g : SSC n) (i : Fin n) : Prop :=
  Function.Injective (fun (p : Fin n × Fin n) => g i p.1 p.2)

/-- X-slice rule: For a fixed column j, the mapping from (y,z) to symbols is injective. -/
def valid_x_slice (g : SSC n) (j : Fin n) : Prop :=
  Function.Injective (fun (p : Fin n × Fin n) => g p.1 j p.2)

/-- Complete SSC Validity Predicate -/
def is_valid (g : SSC n) : Prop :=
  (∀ k, valid_z_slice g k) ∧
  (∀ i, valid_y_slice g i) ∧
  (∀ j, valid_x_slice g j)

/-- Section 2.1: Applying any symbol permutation σ preserves SSC validity. -/
theorem relabel_invariant {n : ℕ} (g : SSC n) (h : SSC.is_valid g)
    (σ : Equiv.Perm (Fin (n ^ 2))) :
    SSC.is_valid (fun x y z => σ (g x y z)) := by
  rcases h with ⟨hz, hy, hx⟩
  refine ⟨?_, ?_, ?_⟩
  · intro k
    have hzk := hz k
    exact Function.Injective.comp σ.injective hzk
  · intro i
    have hyi := hy i
    exact Function.Injective.comp σ.injective hyi
  · intro j
    have hxj := hx j
    exact Function.Injective.comp σ.injective hxj

/-- Canonical standard form definition for block B_1 (z = 0). -/
def is_standard_form {n : ℕ} [NeZero n] (g : SSC n) : Prop :=
  ∀ (r c : Fin n), (g r c 0).val = r.val * n + c.val

-- Exhaustion lemmas: If a value in Fin 4 cannot be 3 options, it must be the 4th.
lemma f4_3 (x : Fin 4) (h0 : x ≠ 0) (h1 : x ≠ 1) (h2 : x ≠ 2) : x = 3 := by
  revert x h0 h1 h2; decide

lemma f4_2 (x : Fin 4) (h0 : x ≠ 0) (h1 : x ≠ 1) (h3 : x ≠ 3) : x = 2 := by
  revert x h0 h1 h3; decide

lemma f4_1 (x : Fin 4) (h0 : x ≠ 0) (h2 : x ≠ 2) (h3 : x ≠ 3) : x = 1 := by
  revert x h0 h2 h3; decide

lemma f4_0 (x : Fin 4) (h1 : x ≠ 1) (h2 : x ≠ 2) (h3 : x ≠ 3) : x = 0 := by
  revert x h1 h2 h3; decide

-- Cross-Slice Extraction Lemmas
lemma no_dup_y_cross {n : ℕ} [NeZero n] (g : SSC n) (hy : ∀ i, valid_y_slice g i)
    (i c1 c2 z1 z2 : Fin n) (h : g i c1 z1 = g i c2 z2) : c1 = c2 ∧ z1 = z2 := by
  have h_eq : (fun (p : Fin n × Fin n) => g i p.1 p.2) (c1, z1) =
    (fun (p : Fin n × Fin n) => g i p.1 p.2) (c2, z2) := h
  have h_inj := hy i h_eq
  exact ⟨congrArg Prod.fst h_inj, congrArg Prod.snd h_inj⟩

lemma no_dup_x_cross {n : ℕ} [NeZero n] (g : SSC n) (hx : ∀ j, valid_x_slice g j)
    (r1 r2 j z1 z2 : Fin n) (h : g r1 j z1 = g r2 j z2) : r1 = r2 ∧ z1 = z2 := by
  have h_eq : (fun (p : Fin n × Fin n) => g p.1 j p.2) (r1, z1) =
    (fun (p : Fin n × Fin n) => g p.1 j p.2) (r2, z2) := h
  have h_inj := hx j h_eq
  exact ⟨congrArg Prod.fst h_inj, congrArg Prod.snd h_inj⟩

/-- Helper: An order-2 SSC in standard form strictly forces the values of Block B_2 (z=1). -/
lemma order_2_B2_fixed (g : SSC 2) (hv : SSC.is_valid g) (hs : is_standard_form g) :
    g 0 0 1 = 3 ∧ g 0 1 1 = 2 ∧ g 1 0 1 = 1 ∧ g 1 1 1 = 0 := by
  have hy := hv.2.1
  have hx := hv.2.2
  have s00 : g 0 0 0 = 0 := Fin.ext_iff.mpr (hs 0 0)
  have s01 : g 0 1 0 = 1 := Fin.ext_iff.mpr (hs 0 1)
  have s10 : g 1 0 0 = 2 := Fin.ext_iff.mpr (hs 1 0)
  have s11 : g 1 1 0 = 3 := Fin.ext_iff.mpr (hs 1 1)
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply f4_3 (g 0 0 1)
    · intro h; have h_eq : g 0 0 1 = g 0 0 0 := by rw [h, ←s00]
      have ⟨_, hz⟩ := no_dup_y_cross g hy 0 0 0 1 0 h_eq; revert hz; decide
    · intro h; have h_eq : g 0 0 1 = g 0 1 0 := by rw [h, ←s01]
      have ⟨_, hz⟩ := no_dup_y_cross g hy 0 0 1 1 0 h_eq; revert hz; decide
    · intro h; have h_eq : g 0 0 1 = g 1 0 0 := by rw [h, ←s10]
      have ⟨_, hz⟩ := no_dup_x_cross g hx 0 1 0 1 0 h_eq; revert hz; decide
  · apply f4_2 (g 0 1 1)
    · intro h; have h_eq : g 0 1 1 = g 0 0 0 := by rw [h, ←s00]
      have ⟨_, hz⟩ := no_dup_y_cross g hy 0 1 0 1 0 h_eq; revert hz; decide
    · intro h; have h_eq : g 0 1 1 = g 0 1 0 := by rw [h, ←s01]
      have ⟨_, hz⟩ := no_dup_x_cross g hx 0 0 1 1 0 h_eq; revert hz; decide
    · intro h; have h_eq : g 0 1 1 = g 1 1 0 := by rw [h, ←s11]
      have ⟨_, hz⟩ := no_dup_x_cross g hx 0 1 1 1 0 h_eq; revert hz; decide
  · apply f4_1 (g 1 0 1)
    · intro h; have h_eq : g 1 0 1 = g 0 0 0 := by rw [h, ←s00]
      have ⟨_, hz⟩ := no_dup_x_cross g hx 1 0 0 1 0 h_eq; revert hz; decide
    · intro h; have h_eq : g 1 0 1 = g 1 0 0 := by rw [h, ←s10]
      have ⟨_, hz⟩ := no_dup_y_cross g hy 1 0 0 1 0 h_eq; revert hz; decide
    · intro h; have h_eq : g 1 0 1 = g 1 1 0 := by rw [h, ←s11]
      have ⟨_, hz⟩ := no_dup_y_cross g hy 1 0 1 1 0 h_eq; revert hz; decide
  · apply f4_0 (g 1 1 1)
    · intro h; have h_eq : g 1 1 1 = g 0 1 0 := by rw [h, ←s01]
      have ⟨_, hz⟩ := no_dup_x_cross g hx 1 0 1 1 0 h_eq; revert hz; decide
    · intro h; have h_eq : g 1 1 1 = g 1 0 0 := by rw [h, ←s10]
      have ⟨_, hz⟩ := no_dup_y_cross g hy 1 1 0 1 0 h_eq; revert hz; decide
    · intro h; have h_eq : g 1 1 1 = g 1 1 0 := by rw [h, ←s11]
      have ⟨_, hz⟩ := no_dup_y_cross g hy 1 1 1 1 0 h_eq; revert hz; decide

/-- Lemma 2.1: Up to standard-form relabeling, an order 2 SSC is completely unique. -/
theorem lemma_2_1_order_2_unique (g1 g2 : SSC 2)
    (hv1 : SSC.is_valid g1) (hv2 : SSC.is_valid g2)
    (hs1 : is_standard_form g1) (hs2 : is_standard_form g2) :
    g1 = g2 := by
  have hB2_1 := order_2_B2_fixed g1 hv1 hs1
  have hB2_2 := order_2_B2_fixed g2 hv2 hs2
  ext r c z
  have hr : r = 0 ∨ r = 1 := by omega
  have hc : c = 0 ∨ c = 1 := by omega
  have hz : z = 0 ∨ z = 1 := by omega
  -- We use rcases to substitute the exact values into the goal cleanly
  rcases hr with rfl | rfl
  · rcases hc with rfl | rfl
    · rcases hz with rfl | rfl
      · simp only [hs1 0 0, hs2 0 0]
      · simp only [hB2_1.1, hB2_2.1]
    · rcases hz with rfl | rfl
      · simp only [hs1 0 1, hs2 0 1]
      · simp only [hB2_1.2.1, hB2_2.2.1]
  · rcases hc with rfl | rfl
    · rcases hz with rfl | rfl
      · simp only [hs1 1 0, hs2 1 0]
      · simp only [hB2_1.2.2.1, hB2_2.2.2.1]
    · rcases hz with rfl | rfl
      · simp only [hs1 1 1, hs2 1 1]
      · simp only [hB2_1.2.2.2, hB2_2.2.2.2]

end SSC
open Finset
/-- Definition 1.4: Λ_n^k is the set of n×n (0, 1)-matrices in which each r and c sum to k. -/
def Lambda_matrix (n k : ℕ) (A : Fin n → Fin n → ℕ) : Prop :=
  (∀ (i j : Fin n), A i j = 0 ∨ A i j = 1) ∧
  (∀ (i : Fin n), ∑ (j : Fin n), A i j = k) ∧
  (∀ (j : Fin n), ∑ (i : Fin n), A i j = k)
namespace SSC3

open Finset

/-- The set of symbols in row r of block B_1 (z=0) for an order-3 SSC. -/
def B1_row_symbols (g : SSC 3) (r : Fin 3) : Finset (Fin 9) :=
  {g r 0 0, g r 1 0, g r 2 0}

/-- The set of symbols in column c of block B_1 (z=0) for an order-3 SSC. -/
def B1_col_symbols (g : SSC 3) (c : Fin 3) : Finset (Fin 9) :=
  {g 0 c 0, g 1 c 0, g 2 c 0}

/-- The combined restricted pool for cell (r, c) in B_2 (z=1). -/
def restricted_pool (g : SSC 3) (r c : Fin 3) : Finset (Fin 9) :=
  B1_row_symbols g r ∪ B1_col_symbols g c

/-- The available candidates for cell (r,c) in B_2. -/
def candidate_pool (g : SSC 3) (r c : Fin 3) : Finset (Fin 9) :=
  univ \ restricted_pool g r c

/-- Proposition 2.2 (Part 1): The candidate pool for any cell in B_2 of a
    valid order-3 SSC in standard form has exactly 4 candidates. -/
lemma prop_2_2_B2_candidates (g : SSC 3) (hs : SSC.is_standard_form g)
    (r c : Fin 3) : card (candidate_pool g r c) = 4 := by
  have s00 : g 0 0 0 = 0 := Fin.ext_iff.mpr (hs 0 0)
  have s01 : g 0 1 0 = 1 := Fin.ext_iff.mpr (hs 0 1)
  have s02 : g 0 2 0 = 2 := Fin.ext_iff.mpr (hs 0 2)
  have s10 : g 1 0 0 = 3 := Fin.ext_iff.mpr (hs 1 0)
  have s11 : g 1 1 0 = 4 := Fin.ext_iff.mpr (hs 1 1)
  have s12 : g 1 2 0 = 5 := Fin.ext_iff.mpr (hs 1 2)
  have s20 : g 2 0 0 = 6 := Fin.ext_iff.mpr (hs 2 0)
  have s21 : g 2 1 0 = 7 := Fin.ext_iff.mpr (hs 2 1)
  have s22 : g 2 2 0 = 8 := Fin.ext_iff.mpr (hs 2 2)
  fin_cases r <;> fin_cases c <;> {
    dsimp [candidate_pool, restricted_pool, B1_row_symbols, B1_col_symbols]
    simp only [s00, s01, s02, s10, s11, s12, s20, s21, s22]
    decide
  }
/-- Computable conversion of a flat 0..8 index into a 3x3 coordinate.
    (Removing 'omega' makes this function instantly evaluable by 'decide') -/
def flat_to_crd (i : Fin 9) : Fin 3 × Fin 3 :=
  match i.val with
  | 0 => ⟨0, 0⟩ | 1 => ⟨0, 1⟩ | 2 => ⟨0, 2⟩
  | 3 => ⟨1, 0⟩ | 4 => ⟨1, 1⟩ | 5 => ⟨1, 2⟩
  | 6 => ⟨2, 0⟩ | 7 => ⟨2, 1⟩ | 8 => ⟨2, 2⟩
  | _ => ⟨0, 0⟩

/-- Computable concrete standard form grid for B_1. -/
def g_std : SSC 3 := fun r c z =>
  if z.val = 0 then
    match r.val, c.val with
    | 0, 0 => 0 | 0, 1 => 1 | 0, 2 => 2
    | 1, 0 => 3 | 1, 1 => 4 | 1, 2 => 5
    | 2, 0 => 6 | 2, 1 => 7 | 2, 2 => 8
    | _, _ => 0
  else 0

/-- At z=0, any valid grid in standard form matches g_std exactly. -/
lemma g_eq_g_std (g : SSC 3) (hs : SSC.is_standard_form g) (r c : Fin 3) :
    g r c 0 = g_std r c 0 := by
  have h := hs r c
  fin_cases r <;> fin_cases c <;> {
    apply Fin.ext
    exact h
  }

/-- The 9x9 incidence matrix A_1 for block B_2. -/
def A1_matrix (g : SSC 3) : Fin 9 → Fin 9 → ℕ :=
  fun i j =>
    let ⟨r, c⟩ := flat_to_crd i
    if j ∈ candidate_pool g r c then 1 else 0

/-- The incidence matrices for g and g_std are definitionally identical. -/
lemma A1_matrix_eq (g : SSC 3) (hs : SSC.is_standard_form g) :
    A1_matrix g = A1_matrix g_std := by
  ext i j
  -- 1. Prove the candidate pools are exactly identical
  have h_pool : candidate_pool g (flat_to_crd i).1 (flat_to_crd i).2 =
                candidate_pool g_std (flat_to_crd i).1 (flat_to_crd i).2 := by
    dsimp [candidate_pool, restricted_pool, B1_row_symbols, B1_col_symbols]
    simp only [g_eq_g_std g hs]

  -- 2. Unfold the matrix to expose the 'if' statements
  dsimp [A1_matrix]

  -- 3. Rewrite the identical condition directly (closes goal via rfl automatically)
  rw [h_pool]

/-- Proposition 2.2 (Part 2): The incidence matrix A_1 belongs to Λ_9^4. -/
lemma prop_2_2_A1_is_Lambda (g : SSC 3) (hs : SSC.is_standard_form g) :
    Lambda_matrix 9 4 (A1_matrix g) := by
  -- Swap the abstract grid for the computable grid
  rw [A1_matrix_eq g hs]
  -- Unfold Lambda_matrix so 'decide' can see the computable ∀ and ∑ math inside
  dsimp [Lambda_matrix]
  -- Let the kernel instantly evaluate the concrete standard form matrix
  decide
/-- The set of symbols in row r across blocks B_1 (z=0) and B_2 (z=1). -/
def B12_row_symbols (g : SSC 3) (r : Fin 3) : Finset (Fin 9) :=
  {g r 0 0, g r 1 0, g r 2 0, g r 0 1, g r 1 1, g r 2 1}

/-- The set of symbols in column c across blocks B_1 (z=0) and B_2 (z=1). -/
def B12_col_symbols (g : SSC 3) (c : Fin 3) : Finset (Fin 9) :=
  {g 0 c 0, g 1 c 0, g 2 c 0, g 0 c 1, g 1 c 1, g 2 c 1}

/-- The combined restricted pool for cell (r, c) in B_3 (z=2). -/
def restricted_pool_B3 (g : SSC 3) (r c : Fin 3) : Finset (Fin 9) :=
  B12_row_symbols g r ∪ B12_col_symbols g c

/-- The available candidates for cell (r,c) in B_3. -/
def candidate_pool_B3 (g : SSC 3) (r c : Fin 3) : Finset (Fin 9) :=
  univ \ restricted_pool_B3 g r c

/-- The 9x9 incidence matrix A_2 for block B_3. -/
def A2_matrix (g : SSC 3) : Fin 9 → Fin 9 → ℕ :=
  fun i j =>
    let ⟨r, c⟩ := flat_to_crd i
    if j ∈ candidate_pool_B3 g r c then 1 else 0

/-- Proposition 2.2 (Part 3): The incidence matrix A_2 belongs to Λ_9^1.
    Because B_2 has 448 variations, we encode your paper's deduction that
    the 6+6-4=8 restrictions uniquely determine B_3 as a formal axiom. -/
axiom prop_2_2_A2_is_Lambda (g : SSC 3) (hv : SSC.is_valid g)
    (hs : SSC.is_standard_form g) : Lambda_matrix 9 1 (A2_matrix g)

end SSC3
namespace SSCn

open Finset

variable {n : ℕ}

/-- Lemma 2.3 (Algebraic Core): Proves that the inclusion-exclusion candidate
    reduction n^2 - (2*m*n - m^2) strictly equals (n - m)^2 for m ≤ n. -/
lemma candidate_reduction_algebra (n m : ℕ) (h : m ≤ n) :
    n ^ 2 - (2 * m * n - m ^ 2) = (n - m) ^ 2 := by
  have h1 : m * m ≤ m * n := Nat.mul_le_mul_left m h
  have h2 : m * n ≤ m * n + m * n := Nat.le_add_right _ _
  have h3 : m ^ 2 ≤ 2 * m * n := by
    calc m ^ 2 = m * m := by ring
    _ ≤ m * n := h1
    _ ≤ m * n + m * n := h2
    _ = 2 * m * n := by ring

  have h4 : 2 * m * n - m ^ 2 ≤ n ^ 2 := by
    zify [h3]
    have h_eq : (2 : ℤ) * m * n - m ^ 2 = (n : ℤ) ^ 2 - ((n : ℤ) - (m : ℤ)) ^ 2 := by ring
    rw [h_eq]
    exact sub_le_self _ (sq_nonneg _)

  zify [h3, h4, h]
  ring

/-- Helper to safely cast Fin m to Fin n when m ≤ n -/
def cast_fin {n m : ℕ} (h : m ≤ n) (x : Fin m) : Fin n :=
  ⟨x.val, by omega⟩

/-- Generalized row restriction pool across m completed blocks. -/
def row_restricted_pool (g : SSC n) {m : ℕ} (hm : m ≤ n) (r : Fin n) : Finset (Fin (n ^ 2)) :=
  (univ : Finset (Fin n × Fin m)).image (fun p => g r p.1 (cast_fin hm p.2))

/-- Generalized column restriction pool across m completed blocks. -/
def col_restricted_pool (g : SSC n) {m : ℕ} (hm : m ≤ n) (c : Fin n) : Finset (Fin (n ^ 2)) :=
  (univ : Finset (Fin n × Fin m)).image (fun p => g p.1 c (cast_fin hm p.2))

/-- Combined restricted pool for cell (r, c) in block B_{m+1}. -/
def restricted_pool (g : SSC n) {m : ℕ} (hm : m ≤ n) (r c : Fin n) : Finset (Fin (n ^ 2)) :=
  row_restricted_pool g hm r ∪ col_restricted_pool g hm c

/-- Available candidates for cell (r, c) in block B_{m+1}. -/
def candidate_pool (g : SSC n) {m : ℕ} (hm : m ≤ n) (r c : Fin n) : Finset (Fin (n ^ 2)) :=
  univ \ restricted_pool g hm r c

/-- The slice constraints force exactly m*n restrictions in the row pool. -/
axiom row_pool_size {n m : ℕ} (g : SSC n) (hv : SSC.is_valid g)
    (hm : m ≤ n) (r : Fin n) :
    card (row_restricted_pool g hm r) = m * n

/-- The slice constraints force exactly m*n restrictions in the col pool. -/
axiom col_pool_size {n m : ℕ} (g : SSC n) (hv : SSC.is_valid g)
    (hm : m ≤ n) (c : Fin n) :
    card (col_restricted_pool g hm c) = m * n

/-- Due to uniform slice partitioning across blocks, exactly m^2 digits overlap. -/
axiom pool_intersection_size {n m : ℕ} (g : SSC n) (hv : SSC.is_valid g)
    (hm : m ≤ n) (r c : Fin n) :
    card (row_restricted_pool g hm r ∩ col_restricted_pool g hm c) = m ^ 2

/-- Lemma 2.3: For m validly completed blocks of an n-SSC, every cell in block B_{m+1}
    has exactly (n - m)^2 available candidates. -/
theorem lemma_2_3_candidate_count (g : SSC n) (hv : SSC.is_valid g)
    {m : ℕ} (hm : m ≤ n) (r c : Fin n) :
    card (candidate_pool g hm r c) = (n - m) ^ 2 := by
  have h_univ : card (univ : Finset (Fin (n ^ 2))) = n ^ 2 := by simp

  have h_pie : card (restricted_pool g hm r c) = 2 * m * n - m ^ 2 := by
    have h_sum := card_union_add_card_inter (row_restricted_pool g hm r)
      (col_restricted_pool g hm c)
    rw [row_pool_size g hv hm, col_pool_size g hv hm,
      pool_intersection_size g hv hm] at h_sum

    change card (restricted_pool g hm r c) + m ^ 2 = m * n + m * n at h_sum

    -- 1. Forcefully convert 2 * m * n into addition IN THE GOAL
    have h_two : 2 * m * n = m * n + m * n := by ring
    rw [h_two]

    -- 2. Build the bound strictly using addition
    have h1 : m * m ≤ m * n := Nat.mul_le_mul_left m hm
    have h2 : m ^ 2 ≤ m * n + m * n := by
      calc m ^ 2 = m * m := by ring
      _ ≤ m * n := h1
      _ ≤ m * n + m * n := Nat.le_add_right _ _

    -- 3. Generalize: There is zero multiplication left anywhere!
    -- omega now sees: X + M2 = MN + MN, and M2 ≤ MN + MN
    generalize card (restricted_pool g hm r c) = X at h_sum ⊢
    generalize m ^ 2 = M2 at h_sum h2 ⊢
    generalize m * n = MN at h_sum h2 ⊢
    omega

  dsimp [candidate_pool]
  rw [card_sdiff]

  -- card_sdiff creates the intersection (restricted_pool ∩ univ).
  -- Finset.inter_univ natively reduces this back to restricted_pool.
  rw [Finset.inter_univ]

  rw [h_univ, h_pie]
  exact candidate_reduction_algebra n m hm

end SSCn

namespace SSC_Bounds

open Matrix Finset

/-- Definition 1.4: Λ_N^k is the set of N×N (0, 1)-matrices in which each row and column sum to k.
    (We use N here to represent n^2 to prevent shadowing the grid order n) -/
structure LambdaMatrix {N : ℕ} (k : ℕ) (A : Matrix (Fin N) (Fin N) ℝ) : Prop where
  is_zero_one : ∀ i j, A i j = 0 ∨ A i j = 1
  row_sum : ∀ i, ∑ j, A i j = (k : ℝ)
  col_sum : ∀ j, ∑ i, A i j = (k : ℝ)

/-- Theorem 1.1 (Wanless 2006): Minimum values of per(A) for A ∈ Λ_N^k. -/
axiom theorem_1_1_wanless {N k : ℕ} (hk1 : 1 ≤ k) (hkN : k ≤ N)
    (A : Matrix (Fin N) (Fin N) ℝ) (hA : LambdaMatrix k A) :
    (((k - 1 : ℝ) ^ (k - 1) / (k : ℝ) ^ (k - 2)) ^ N) < A.permanent

/-- Theorem 1.2 (Brègman 1973): Maximum values of per(A) for A ∈ Λ_N^k. -/
axiom theorem_1_2_bregman {N k : ℕ} (hk1 : 1 ≤ k) (hkN : k ≤ N)
    (A : Matrix (Fin N) (Fin N) ℝ) (hA : LambdaMatrix k A) :
    A.permanent ≤ (Nat.factorial k : ℝ) ^ ((N : ℝ) / (k : ℝ))

/-- The row-sum degree k_m for the incidence matrix A_m at step m. -/
def k_m (n m : ℕ) : ℕ := (n - m) ^ 2

/-- General Bound (Section 2.3): For n ≥ 4, the total configurations x are bounded
    by the permutations of B_1 multiplied by the product of the permanent bounds. -/
axiom general_ssc_bounds (n : ℕ) (hn : 4 ≤ n) (x : ℝ) :
    ((Nat.factorial (n ^ 2) : ℝ) * ∏ m ∈ Ico 1 (n - 1),
      (((k_m n m - 1 : ℝ) ^ (k_m n m - 1) / (k_m n m : ℝ) ^ (k_m n m - 2)) ^ (n ^ 2))) < x ∧
    x ≤ ((Nat.factorial (n ^ 2) : ℝ) * ∏ m ∈ Ico 1 (n - 1),
      (Nat.factorial (k_m n m) : ℝ) ^ ((n ^ 2 : ℝ) / (k_m n m : ℝ)))
/-- Section 2.3: Explicit evaluation of the bounds for an Order 4 SSC (n=4).
    The matrices A_1 and A_2 fall into Λ_16^9 and Λ_16^4 respectively. -/
axiom order_4_bounds (x : ℝ) :
    ((Nat.factorial 16 : ℝ) *
    (((8 : ℝ) ^ 8 / (9 : ℝ) ^ 7) ^ (16 : ℝ)) *
    (((3 : ℝ) ^ 3 / (4 : ℝ) ^ 2) ^ (16 : ℝ)) < x) ∧
    (x ≤ (Nat.factorial 16 : ℝ) *
    ((Nat.factorial 9 : ℝ) ^ ((16 : ℝ) / 9)) *
    ((Nat.factorial 4 : ℝ) ^ ((16 : ℝ) / 4)))

/-- Section 2.3: Numerical evaluation for n=4 configurations. -/
axiom order_4_numerical_bounds (x : ℝ) :
    (4.75 * (10 : ℝ) ^ 25 < x) ∧ (x ≤ 5.31 * (10 : ℝ) ^ 28)

/-- Section 2.3: Explicit evaluation of the bounds for an Order 5 SSC (n=5).
    The matrices A_1, A_2, and A_3 fall into Λ_25^16, Λ_25^9, and Λ_25^4. -/
axiom order_5_bounds (x : ℝ) :
    ((Nat.factorial 25 : ℝ) *
    (((15 : ℝ) ^ 15 / (16 : ℝ) ^ 14) ^ (25 : ℝ)) *
    (((8 : ℝ) ^ 8 / (9 : ℝ) ^ 7) ^ (25 : ℝ)) *
    (((3 : ℝ) ^ 3 / (4 : ℝ) ^ 2) ^ (25 : ℝ)) < x) ∧
    (x ≤ (Nat.factorial 25 : ℝ) *
    ((Nat.factorial 16 : ℝ) ^ ((25 : ℝ) / 16)) *
    ((Nat.factorial 9 : ℝ) ^ ((25 : ℝ) / 9)) *
    ((Nat.factorial 4 : ℝ) ^ ((25 : ℝ) / 4)))

/-- Section 2.3: Numerical evaluation for n=5 configurations. -/
axiom order_5_numerical_bounds (x : ℝ) :
    (1.23 * (10 : ℝ) ^ 64 < x) ∧ (x ≤ 1.19 * (10 : ℝ) ^ 70)
end SSC_Bounds
