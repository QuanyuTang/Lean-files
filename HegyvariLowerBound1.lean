/-
# A Lower Bound for Hegyvári's Function f(a,K)

Formalization of Theorem 1 from "A Lower Bound for Hegyvári's Function f(a,K)".

The theorem states that for integers a, K ≥ 1 with a ≥ K, the arithmetic progression
a, a+K, a+2K, ..., a+(k-1)K has distinct consecutive sums, where k = ⌊2√(a/K - 1)⌋.
This yields f(a,K) ≥ a + K(⌊2√(a/K - 1)⌋ - 1).
-/

import Mathlib

open Finset BigOperators

/-! ## Definitions -/

/-- The consecutive sum of `r` terms of sequence `x` starting at index `u`:
    x(u) + x(u+1) + ... + x(u+r-1). -/
def consecSum (x : ℕ → ℕ) (u r : ℕ) : ℕ :=
  ∑ i ∈ Finset.range r, x (u + i)

/-- A sequence of length `n` has **distinct consecutive sums** if whenever two blocks
    of consecutive terms have the same sum, they must be the same block. -/
def DistinctConsecSums (x : ℕ → ℕ) (n : ℕ) : Prop :=
  ∀ u₁ r₁ u₂ r₂ : ℕ,
    0 < r₁ → u₁ + r₁ ≤ n →
    0 < r₂ → u₂ + r₂ ≤ n →
    consecSum x u₁ r₁ = consecSum x u₂ r₂ →
    u₁ = u₂ ∧ r₁ = r₂

/-! ## Auxiliary lemmas about sums of arithmetic progressions -/

/-- The integer-valued consecutive sum for the arithmetic progression `i ↦ a + i * K`. -/
def consecSumAP (a K : ℤ) (u r : ℕ) : ℤ :=
  ∑ i ∈ Finset.range r, (a + (↑u + ↑i) * K)

/-- The ℕ-valued `consecSum` of the AP equals the ℤ-valued `consecSumAP`. -/
lemma consecSum_eq_consecSumAP (a K : ℕ) (u r : ℕ) :
    (consecSum (fun i => a + i * K) u r : ℤ) = consecSumAP (↑a) (↑K) u r := by
  unfold consecSum consecSumAP; norm_num

/-- Closed form: `2 * consecSumAP a K u r = r * (2a + K(2u + r - 1))`. -/
lemma two_mul_consecSumAP (a K : ℤ) (u r : ℕ) :
    2 * consecSumAP a K u r = ↑r * (2 * a + K * (2 * ↑u + ↑r - 1)) := by
  unfold consecSumAP
  induction r
  · norm_num [Finset.sum_range_succ]
  · norm_num [Finset.sum_range_succ] at *; linarith

/-! ## Step 1: Same length implies same start -/

/-- For a positive common difference, equal sums of blocks of the same length
    forces the blocks to start at the same index. -/
lemma same_length_same_start (a K : ℤ) (hK : 0 < K) (u₁ u₂ r : ℕ) (hr : 0 < r)
    (heq : consecSumAP a K u₁ r = consecSumAP a K u₂ r) : u₁ = u₂ := by
  have h_eq : r * (2 * a + K * (2 * u₁ + r - 1)) = r * (2 * a + K * (2 * u₂ + r - 1)) := by
    rw [← two_mul_consecSumAP a K u₁ r, ← two_mul_consecSumAP a K u₂ r, heq]
  simp_all +decide [ne_of_gt]

/-! ## Step 2: Different lengths lead to contradiction -/

/-- Algebraic identity: equal `consecSumAP` implies the doubled closed forms are equal. -/
lemma consecSumAP_eq_iff (a K : ℤ) (u₁ u₂ r₁ r₂ : ℕ)
    (heq : consecSumAP a K u₁ r₁ = consecSumAP a K u₂ r₂) :
    ↑r₁ * (2 * a + K * (2 * ↑u₁ + ↑r₁ - 1)) = ↑r₂ * (2 * a + K * (2 * ↑u₂ + ↑r₂ - 1)) := by
  rw [← two_mul_consecSumAP, ← two_mul_consecSumAP, heq]

/-- AM-GM bound: `4 · r · (k - 1 - r) < k²` for `0 < r` and `r + 1 < k`. -/
lemma mul_bound (r k : ℕ) (hr : 0 < r) (hrk : r + 1 < k) :
    4 * (r * (k - 1 - r)) < k ^ 2 := by
  nlinarith [sq_nonneg (k - 1 - r - r : ℤ),
    Nat.sub_add_cancel (show 1 ≤ k from by linarith),
    Nat.sub_add_cancel (show r ≤ k - 1 from Nat.le_sub_one_of_lt (by linarith))]

/-- Gauss sum identity in ℤ: `2 · ∑_{i<r} (u + i) = r · (2u + r - 1)`. -/
lemma two_mul_sum_range_shift (u r : ℕ) :
    2 * ∑ i ∈ Finset.range r, ((↑u : ℤ) + ↑i) = ↑r * (2 * ↑u + ↑r - 1) := by
  induction r
  · norm_num [Finset.sum_range_succ]
  · norm_num [Finset.sum_range_succ] at *; linarith

/-- Index-sum difference bound: when `r₁ < r₂` and both blocks fit in `[0, k)`,
    the doubled index-sum difference is bounded by `k²`. -/
lemma index_sum_diff_bound (u₁ u₂ r₁ r₂ k : ℕ)
    (_hr₁ : 0 < r₁) (_hr₂ : 0 < r₂)
    (h1 : u₁ + r₁ ≤ k) (_h2 : u₂ + r₂ ≤ k)
    (hlt : r₁ < r₂) :
    ↑r₁ * (2 * (↑u₁ : ℤ) + ↑r₁) - ↑r₂ * (2 * ↑u₂ + ↑r₂)
      < (↑k ^ 2 : ℤ) := by
  nlinarith

/-- Core contradiction: if two blocks of different lengths in an AP of length `k` have the
    same consecutive sum, and `k² · K ≤ 4(a - K)`, we reach a contradiction. This is the
    heart of the proof, combining the upper bound on the index-sum difference with the
    lower bound from the hypothesis on `k`. -/
lemma diff_length_contradiction (a K : ℤ) (hK : 0 < K) (haK : K ≤ a)
    (k u₁ u₂ r₁ r₂ : ℕ)
    (hk : ↑k ^ 2 * K ≤ 4 * (a - K))
    (hr₁ : 0 < r₁) (hr₂ : 0 < r₂)
    (h1 : u₁ + r₁ ≤ k) (h2 : u₂ + r₂ ≤ k)
    (hlt : r₁ ≠ r₂)
    (heq : consecSumAP a K u₁ r₁ = consecSumAP a K u₂ r₂) : False := by
  -- From the equal sums, derive the key algebraic equation relating index sums to `a` and `K`.
  have h_eq : (r₂ - r₁ : ℤ) * a =
      K * (r₁ * u₁ + r₁ * (r₁ - 1) / 2 - r₂ * u₂ - r₂ * (r₂ - 1) / 2) := by
    unfold consecSumAP at heq
    norm_num [Finset.sum_add_distrib, add_mul, Finset.mul_sum _ _ _, Finset.sum_mul] at *
    have hsums : (∑ x ∈ Finset.range r₁, (x : ℤ)) = r₁ * (r₁ - 1) / 2 ∧
        (∑ x ∈ Finset.range r₂, (x : ℤ)) = r₂ * (r₂ - 1) / 2 := by
      exact ⟨by rw [← Nat.cast_sum, Finset.sum_range_id]; cases r₁ <;> norm_num,
             by rw [← Nat.cast_sum, Finset.sum_range_id]; cases r₂ <;> norm_num⟩
    simp_all +decide [← Finset.sum_mul _ _ _]; linarith
  -- WLOG r₁ < r₂.
  wlog h_wlog : (r₁ : ℤ) < r₂ generalizing r₁ r₂ u₁ u₂
  · grind +extAll
  · -- E = T₁ - T₂ is positive (from the equation and a, K > 0).
    have hE_pos :
        (r₁ * u₁ + r₁ * (r₁ - 1) / 2 - r₂ * u₂ - r₂ * (r₂ - 1) / 2 : ℤ) > 0 := by
      nlinarith
    -- Upper bound: E ≤ r₁(k - r₁ - 1) (maximise T₁, minimise T₂ using r₂ ≥ r₁ + 1).
    have hE_bound :
        (r₁ * u₁ + r₁ * (r₁ - 1) / 2 - r₂ * u₂ - r₂ * (r₂ - 1) / 2 : ℤ) ≤
          r₁ * (k - r₁ - 1) := by
      nlinarith only [h1, h2, h_wlog, hE_pos,
        Int.mul_ediv_add_emod (r₁ * (r₁ - 1)) 2,
        Int.emod_nonneg (r₁ * (r₁ - 1)) two_ne_zero,
        Int.emod_lt_of_pos (r₁ * (r₁ - 1)) two_pos,
        Int.mul_ediv_add_emod (r₂ * (r₂ - 1)) 2,
        Int.emod_nonneg (r₂ * (r₂ - 1)) two_ne_zero,
        Int.emod_lt_of_pos (r₂ * (r₂ - 1)) two_pos]
    -- By AM-GM: E ≤ (k-1)²/4.
    have hE_bound' :
        (r₁ * u₁ + r₁ * (r₁ - 1) / 2 - r₂ * u₂ - r₂ * (r₂ - 1) / 2 : ℤ) ≤
          (k - 1) ^ 2 / 4 := by
      exact hE_bound.trans (Int.le_ediv_of_mul_le (by norm_num)
        (by nlinarith only [sq_nonneg (k - 2 * r₁ - 1 : ℤ)]))
    -- Derive contradiction: k² + 4 ≤ 4E ≤ (k-1)² = k² - 2k + 1, impossible.
    rw [Int.le_ediv_iff_mul_le] at * <;> norm_cast at *
    norm_num [Int.subNatNat_eq_coe] at *
    nlinarith [mul_pos hK (by linarith : 0 < (r₂ : ℤ) - r₁)]

/-! ## Main theorem -/

/-- **Theorem 1 (Main Theorem).**
    For positive integers `a`, `K` with `a ≥ K`, the arithmetic progression
    `a, a+K, a+2K, ..., a+(k-1)K` has distinct consecutive sums whenever `k² · K ≤ 4(a - K)`.

    In particular, taking `k = ⌊2√(a/K - 1)⌋` (which satisfies `k² ≤ 4(a/K - 1)`,
    hence `k²K ≤ 4(a - K)`) yields the bound
    `f(a,K) ≥ a + K(⌊2√(a/K - 1)⌋ - 1)`. -/
theorem arith_prog_distinct_consec_sums
    (a K : ℕ) (hK : 0 < K) (haK : K ≤ a)
    (k : ℕ) (hk : k ^ 2 * K ≤ 4 * (a - K)) :
    DistinctConsecSums (fun i => a + i * K) k := by
  intros u₁ r₁ u₂ r₂ hr₁ hr₂ h_eq
  intros hle heq
  have h_diff : r₁ = r₂ := by
    apply Classical.byContradiction
    intro h_neq
    apply diff_length_contradiction (a : ℤ) (K : ℤ) (by positivity) (by linarith)
      k u₁ u₂ r₁ r₂ (by norm_cast) hr₁ h_eq hr₂ hle h_neq (by
      convert heq using 1
      unfold consecSumAP consecSum; norm_cast)
  simp_all +decide [consecSum]
  simp_all +decide [Finset.sum_add_distrib, add_mul]
  aesop

/-! ## Definition of Hegyvári's function f(a, K) -/

/-- A valid sequence for Hegyvári's problem: a finite increasing sequence of length `s`
    starting at `a`, with consecutive gaps bounded by `K`, and all consecutive sums
    pairwise distinct. -/
structure IsValidSeq (a K s : ℕ) (x : ℕ → ℕ) : Prop where
  length_pos : 1 ≤ s
  starts_at : x 0 = a
  strictly_increasing : ∀ i, i + 1 < s → x i < x (i + 1)
  gaps_bounded : ∀ i, i + 1 < s → x (i + 1) - x i ≤ K
  distinct_sums : DistinctConsecSums x s

/-- The set of achievable endpoints: values `n` that can be the last element of a valid
    sequence starting at `a` with gaps bounded by `K`. -/
def AchievableEndpoints (a K : ℕ) : Set ℕ :=
  {n | ∃ (s : ℕ) (x : ℕ → ℕ), IsValidSeq a K s x ∧ x (s - 1) = n}

/-- Hegyvári's function `f(a, K)`: the largest achievable endpoint, i.e., the supremum
    of the set of all `n` such that there exists an increasing sequence from `a` to `n`
    with gaps ≤ `K` and distinct consecutive sums. -/
noncomputable def fHegyv (a K : ℕ) : ℕ := sSup (AchievableEndpoints a K)

/-! ## The arithmetic progression forms a valid sequence -/

/-- The arithmetic progression `a, a+K, …, a+(k−1)K` forms a valid sequence
    for Hegyvári's problem, provided `k ≥ 1` and `k² K ≤ 4(a − K)`. -/
lemma ap_isValidSeq (a K k : ℕ) (hK : 0 < K) (haK : K ≤ a) (hk_pos : 1 ≤ k)
    (hk : k ^ 2 * K ≤ 4 * (a - K)) :
    IsValidSeq a K k (fun i => a + i * K) := by
  refine ⟨hk_pos, by simp, fun i _ => ?_, fun i _ => ?_,
    arith_prog_distinct_consec_sums a K hK haK k hk⟩
  · show a + i * K < a + (i + 1) * K; nlinarith
  · show a + (i + 1) * K - (a + i * K) ≤ K
    have h : a + (i + 1) * K = a + i * K + K := by ring
    omega

/-! ## Bridge lemma: valid sequences give lower bounds for f -/

/-- If `n` is an achievable endpoint and the set of endpoints is bounded above,
    then `f(a,K) ≥ n`. -/
lemma le_fHegyv_of_achievable (a K n : ℕ)
    (hbdd : BddAbove (AchievableEndpoints a K))
    (hn : n ∈ AchievableEndpoints a K) : n ≤ fHegyv a K :=
  le_csSup hbdd hn

/-- The trivial sequence `{a}` gives `a` as an achievable endpoint. -/
lemma trivial_endpoint_achievable (a K : ℕ) : a ∈ AchievableEndpoints a K := by
  refine ⟨1, fun _ => a, ?_, rfl⟩
  exact ⟨le_refl 1, rfl, fun i hi => by omega, fun i hi => by omega,
    fun u₁ r₁ u₂ r₂ hr₁ h1 hr₂ h2 _ => ⟨by omega, by omega⟩⟩

/-- A valid sequence of length `k ≥ 1` based on the AP gives `a + (k−1)·K`
    as an achievable endpoint. -/
lemma ap_endpoint_achievable (a K k : ℕ) (hK : 0 < K) (haK : K ≤ a) (hk_pos : 1 ≤ k)
    (hk : k ^ 2 * K ≤ 4 * (a - K)) :
    a + (k - 1) * K ∈ AchievableEndpoints a K := by
  exact ⟨k, fun i => a + i * K, ap_isValidSeq a K k hK haK hk_pos hk, rfl⟩

/-! ## The floor-sqrt choice satisfies the quadratic inequality -/

/-
The choice `k = ⌊2√(a/K − 1)⌋` satisfies `k² · K ≤ 4 · (a − K)`.
-/
lemma floor_sqrt_bound (a K : ℕ) (hK : 0 < K) (haK : K ≤ a) :
    (Nat.floor (2 * Real.sqrt ((a : ℝ) / K - 1))) ^ 2 * K ≤ 4 * (a - K) := by
  -- By definition of $k$, we know that $k^2 \leq 4 \cdot (a / K - 1)$.
  have hk_sq : (⌊2 * Real.sqrt ((a : ℝ) / K - 1)⌋₊ : ℝ) ^ 2 ≤ 4 * ((a : ℝ) / K - 1) := by
    exact le_trans ( pow_le_pow_left₀ ( by positivity ) ( Nat.floor_le ( by positivity ) ) _ ) ( by nlinarith [ Real.mul_self_sqrt ( show 0 ≤ ( a : ℝ ) / K - 1 by rw [ sub_nonneg, le_div_iff₀ ] <;> norm_cast ; linarith ) ] );
  rw [ ← @Nat.cast_le ℝ ];
  simp +zetaDelta at *;
  rw [ Nat.cast_sub haK ] ; nlinarith [ mul_div_cancel₀ ( a : ℝ ) ( by positivity : ( K : ℝ ) ≠ 0 ) ]

/-! ## Main theorem: f(a, K) ≥ a + K·(⌊2√(a/K − 1)⌋ − 1) -/

/-
**Theorem 1 (Main Theorem).** For positive integers `a`, `K` with `a ≥ K`,
    Hegyvári's function satisfies
    `f(a, K) ≥ a + K · (⌊2√(a/K − 1)⌋ − 1)`,
    provided the set of achievable endpoints is bounded above
    (which Hegyvári proved).
-/
theorem hegyvari_main_bound (a K : ℕ) (hK : 0 < K) (haK : K ≤ a)
    (hbdd : BddAbove (AchievableEndpoints a K)) :
    a + K * (Nat.floor (2 * Real.sqrt ((a : ℝ) / K - 1)) - 1) ≤ fHegyv a K := by
  by_cases h : Nat.floor ( 2 * Real.sqrt ( ( a : ℚ ) / K - 1 ) ) = 0 <;> simp_all +proj [mul_tsub];
  · rw [ Nat.floor_eq_zero.mpr h ] ; simp +arith +decide;
    exact le_csSup hbdd ( trivial_endpoint_achievable a K );
  · convert le_fHegyv_of_achievable _ _ _ _ _ using 1;
    · assumption;
    · convert ap_endpoint_achievable a K ( Nat.floor ( 2 * Real.sqrt ( a / K - 1 ) ) ) hK haK _ _ using 1;
      · rw [ tsub_mul, one_mul, mul_comm ];
      · exact Nat.floor_pos.mpr h;
      · convert floor_sqrt_bound a K hK haK using 1