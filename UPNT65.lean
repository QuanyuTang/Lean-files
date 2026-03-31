import Mathlib

open scoped Pointwise
open Finset ZMod Fintype

noncomputable section

variable {p : ℕ} [hp : Fact (Nat.Prime p)]

private lemma prime : Nat.Prime p := hp.out

/-! ## Proposition 1 -/

theorem sumset_covers (A : Finset (ZMod p)) (hA : p < A.card * 2) :
    ∀ x : ZMod p, ∃ a ∈ A, ∃ b ∈ A, a + b = x := by
  intro x
  by_contra h_contra
  push_neg at h_contra
  set B : Finset (ZMod p) := Finset.image (fun a => x - a) A
  have h_disjoint : Disjoint A B :=
    Finset.disjoint_left.mpr fun a ha hb => by
      obtain ⟨b, hb', rfl⟩ := Finset.mem_image.mp hb
      exact h_contra _ ha _ hb' (by ring)
  have h_union : A.card + B.card ≤ p := by
    rw [← Finset.card_union_of_disjoint h_disjoint]
    exact le_trans (Finset.card_le_univ _) (by norm_num)
  rw [Finset.card_image_of_injective _ sub_right_injective] at h_union
  linarith

theorem sumset_eq_univ (A : Finset (ZMod p)) (hA : p < A.card * 2) :
    A + A = Finset.univ := by
  ext x; simp only [Finset.mem_add, mem_univ, iff_true]
  obtain ⟨a, ha, b, hb, hab⟩ := sumset_covers A hA x
  exact ⟨a, ha, b, hb, hab⟩

/-! ## Theorem 2 -/

def avoidsOne (A : Finset (ZMod p)) : Prop :=
  (∀ a ∈ A, ∀ b ∈ A, a + b ≠ (1 : ZMod p)) ∧
  (∀ a ∈ A, ∀ b ∈ A, a * b ≠ (1 : ZMod p))

/-! ### Group action -/

def s_map (x : ZMod p) : ZMod p := 1 - x
def t_map (x : ZMod p) : ZMod p := x⁻¹
def st_map (x : ZMod p) : ZMod p := 1 - x⁻¹
def ts_map (x : ZMod p) : ZMod p := (1 - x)⁻¹
def sts_map (x : ZMod p) : ZMod p := x * (x - 1)⁻¹

def orb (x : ZMod p) : Finset (ZMod p) :=
  {x, s_map x, t_map x, st_map x, ts_map x, sts_map x}

lemma s_map_involutive : Function.Involutive (s_map (p := p)) :=
  fun x => by unfold s_map; ring

lemma t_map_involutive : Function.Involutive (t_map (p := p)) :=
  fun x => inv_inv x

/-! ### Orbit preservation -/

/-
PROVIDED SOLUTION
Need to show every element of orb (s_map x) is in orb x.
orb (s_map x) = {s_map x, s_map(s_map x), t_map(s_map x), st_map(s_map x), ts_map(s_map x), sts_map(s_map x)}.
Unfolding definitions:
1. s_map x = 1-x: this is the 2nd element of orb x ✓
2. s_map(s_map x) = x: this is the 1st element ✓
3. t_map(s_map x) = (1-x)⁻¹ = ts_map x: 5th element ✓
4. st_map(s_map x) = 1-(1-x)⁻¹: If x ≠ 1, this equals x*(x-1)⁻¹ = sts_map x (6th element). If x = 1, this equals 1 = x (1st element). Either way it's in orb x.
5. ts_map(s_map x) = (1-(1-x))⁻¹ = x⁻¹ = t_map x: 3rd element ✓
6. sts_map(s_map x) = (1-x)*((1-x)-1)⁻¹ = (1-x)*(-x)⁻¹: If x ≠ 0, this equals (x-1)/x = 1-x⁻¹ = st_map x (4th element). If x = 0, this equals 0 = x (1st element). Either way in orb x.

Use intro/simp [orb, s_map, t_map, st_map, ts_map, sts_map] to unfold, then do case analysis on membership in the finset. For each element, show it equals one of the 6 elements of orb x. May need to case split on whether x = 0 or x = 1.
-/
lemma orb_s_subset (x : ZMod p) : orb (s_map x) ⊆ orb x := by
  simp +decide [ orb, s_map, t_map, st_map, ts_map, sts_map ];
  grind +ring

/-
PROVIDED SOLUTION
Need to show every element of orb (t_map x) is in orb x.
orb (t_map x) = {x⁻¹, 1-x⁻¹, (x⁻¹)⁻¹, 1-(x⁻¹)⁻¹, (1-x⁻¹)⁻¹, x⁻¹*(x⁻¹-1)⁻¹}.
1. x⁻¹ = t_map x: 3rd element of orb x ✓
2. 1-x⁻¹ = st_map x: 4th element ✓
3. (x⁻¹)⁻¹ = x: 1st element ✓  (by inv_inv)
4. 1-(x⁻¹)⁻¹ = 1-x = s_map x: 2nd element ✓
5. (1-x⁻¹)⁻¹: If x ≠ 0, = ((x-1)/x)⁻¹ = x/(x-1) = sts_map x (6th element). If x = 0, = (1-0)⁻¹ = 1 = s_map 0 (2nd element of orb 0). Either way in orb x.
6. x⁻¹*(x⁻¹-1)⁻¹: If x ≠ 0 and x ≠ 1, = (1/x)*((1-x)/x)⁻¹ = (1/x)*(x/(1-x)) = 1/(1-x) = ts_map x (5th element). Otherwise need case analysis.

Use intro/simp to unfold, then membership checks. May need by_cases on x = 0.
-/
lemma orb_t_subset (x : ZMod p) : orb (t_map x) ⊆ orb x := by
  grind +locals

lemma orb_eq_of_s_map (x : ZMod p) : orb (s_map x) = orb x := by
  apply Finset.Subset.antisymm (orb_s_subset x)
  have h := orb_s_subset (s_map x)
  rwa [show s_map (s_map x) = x from s_map_involutive x] at h

lemma orb_eq_of_t_map (x : ZMod p) : orb (t_map x) = orb x := by
  apply Finset.Subset.antisymm (orb_t_subset x)
  have h := orb_t_subset (t_map x)
  rwa [show t_map (t_map x) = x from t_map_involutive x] at h

/-
PROVIDED SOLUTION
If y ∈ orb x, then y is one of x, s_map x, t_map x, st_map x, ts_map x, sts_map x. Case split on which one:
- y = x: rfl
- y = s_map x: use orb_eq_of_s_map
- y = t_map x: use orb_eq_of_t_map
- y = st_map x: st_map x = s_map (t_map x), so orb (st_map x) = orb (s_map (t_map x)). Note st_map x is defined as 1 - x⁻¹ = s_map (t_map x). Use orb_eq_of_s_map (t_map x) to get orb (s_map (t_map x)) = orb (t_map x), then orb_eq_of_t_map x to get orb (t_map x) = orb x.
- y = ts_map x: ts_map x = t_map (s_map x). Similarly use orb_eq_of_t_map and orb_eq_of_s_map.
- y = sts_map x: Need to show orb (sts_map x) = orb x. Key: sts_map x = s_map (t_map (s_map x)). But sts_map x = x * (x - 1)⁻¹ and s_map (t_map (s_map x)) = 1 - (1-x)⁻¹. These are NOT always equal (they differ at x = 0). However, sts_map x IS in orb x by definition. So use orb_eq_of_s_map and orb_eq_of_t_map: compute s_map (t_map (s_map x)) = 1 - (1 - x)⁻¹ which may not equal sts_map x. Instead, note that sts_map x ∈ orb x, and we need orb (sts_map x) ⊆ orb x (and vice versa). For ⊆: take any z ∈ orb (sts_map x). z = g(sts_map x) for some group element g. Since sts_map x ∈ orb x, we need g(sts_map x) ∈ orb x. This follows from orb_s_subset and orb_t_subset: applying s or t to any element of orb x keeps it in orb x. Alternatively, use the fact that orb_eq_of_s_map and orb_eq_of_t_map give us that orb is constant on connected components. Since sts_map x ∈ orb x, any element reachable from sts_map x via s and t is also in orb x.
Actually, the simplest approach: show orb (sts_map x) ⊆ orb x by showing all 6 elements of orb(sts_map x) are in orb x. This is what orb_s_subset and orb_t_subset effectively give us, combined with the fact that sts_map x ∈ orb x.
-/
lemma orb_eq_of_mem {x y : ZMod p} (hy : y ∈ orb x) : orb y = orb x := by
  revert hy;
  simp +decide [ orb ];
  simp +decide [ s_map, t_map, st_map, ts_map, sts_map, Finset.ext_iff ];
  rintro ( rfl | rfl | rfl | rfl | rfl | rfl ) a <;> ring_nf <;> norm_num;
  · grind;
  · grind;
  · grind;
  · grind;
  · grind +splitImp

/-! ### Adjacency implies same orbit -/

lemma s_map_mem_orb (x : ZMod p) : s_map x ∈ orb x := by
  simp [orb]

lemma t_map_mem_orb (x : ZMod p) : t_map x ∈ orb x := by
  simp [orb]

/-
PROVIDED SOLUTION
If a + b = 1, then b = 1 - a = s_map a. Since s_map a ∈ orb a (by s_map_mem_orb), we're done. Use: have : b = s_map a := by unfold s_map; linarith (or ring/omega). Then rw this; exact s_map_mem_orb a.
-/
lemma sum_adj_mem_orb {a b : ZMod p} (h : a + b = 1) : b ∈ orb a := by
  convert s_map_mem_orb a using 1;
  exact eq_sub_of_add_eq' h

/-
PROVIDED SOLUTION
If a * b = 1, then b = a⁻¹ = t_map a. To show b = a⁻¹: use mul_left_cancel₀ or the fact that a * b = 1 implies b = a⁻¹ via eq_of_mul_eq_one or inv_eq_of_mul_eq_one_right or mul_right_eq_one₀. Then since t_map a ∈ orb a (by t_map_mem_orb), we're done.
-/
lemma prod_adj_mem_orb {a b : ZMod p} (h : a * b = 1) : b ∈ orb a := by
  by_cases ha : a = 0;
  · aesop;
  · exact Finset.mem_insert_of_mem ( Finset.mem_insert_of_mem ( Finset.mem_insert_self _ _ ) ) |> fun x => by rw [ show b = a⁻¹ by simp [ eq_inv_of_mul_eq_one_left h ] ] ; exact x;

/-! ### Cross-orbit safety -/

lemma cross_orbit_safe {a b : ZMod p}
    (hdisj : Disjoint (orb a) (orb b)) {a' b' : ZMod p}
    (ha : a' ∈ orb a) (hb : b' ∈ orb b) :
    a' + b' ≠ 1 ∧ a' * b' ≠ 1 := by
  constructor
  · intro h
    have hb_orb : b' ∈ orb a' := sum_adj_mem_orb h
    have hb_orb' : b' ∈ orb a := by rwa [orb_eq_of_mem ha] at hb_orb
    exact Finset.disjoint_left.mp hdisj hb_orb' hb
  · intro h
    have hb_orb : b' ∈ orb a' := prod_adj_mem_orb h
    have hb_orb' : b' ∈ orb a := by rwa [orb_eq_of_mem ha] at hb_orb
    exact Finset.disjoint_left.mp hdisj hb_orb' hb

/-! ### Orbit classification -/

/-
PROVIDED SOLUTION
Show {0, 1, -1, (2:ZMod p)⁻¹, 2} has card 5 for p ≥ 5. Use Finset.card_insert_of_not_mem repeatedly. The key distinctness facts for p ≥ 5 prime: 1 ≠ 0 (p ≥ 2), -1 ≠ 0 and -1 ≠ 1 (since 2 ≠ 0, i.e. p ∤ 2), 2⁻¹ ≠ 0, 1, -1 (since 2 ≠ 0, 2 ≠ 1 i.e. p > 1, 2·(-1)=-2≠1 i.e. 3≠0 i.e. p∤3), 2 ≠ 0, 1, -1, 2⁻¹ (since p∤2, p>1, 3≠0, and 2·2=4≠1 i.e. 3≠0). All follow from p ≥ 5 prime implying p ∤ 2 and p ∤ 3.
-/
lemma five_distinct (hp5 : 5 ≤ p) :
    ({0, 1, -1, (2 : ZMod p)⁻¹, 2} : Finset (ZMod p)).card = 5 := by
  rw [ Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_insert_of_notMem ] <;> norm_num;
  · rw [ inv_eq_one_div, div_eq_iff ] <;> norm_num;
    · intro h; rcases p with ( _ | _ | _ | _ | _ | p ) <;> cases h <;> contradiction;
    · erw [ ZMod.natCast_eq_zero_iff ] ; exact Nat.not_dvd_of_pos_of_lt ( by decide ) ( by linarith );
  · rw [ inv_eq_one_div, eq_div_iff ] <;> norm_num;
    · norm_num [ neg_eq_iff_add_eq_zero ];
      erw [ ZMod.natCast_eq_zero_iff ] ; exact Nat.not_dvd_of_pos_of_lt ( by decide ) ( by linarith );
    · erw [ ZMod.natCast_eq_zero_iff ] ; exact Nat.not_dvd_of_pos_of_lt ( by decide ) ( by linarith );
  · norm_num [ eq_neg_iff_add_eq_zero ];
    rcases p with ( _ | _ | _ | _ | _ | p ) <;> norm_cast;
    erw [ ZMod.natCast_eq_zero_iff ];
    exact ⟨ Nat.not_dvd_of_pos_of_lt ( by norm_num ) ( by linarith ), by rintro ⟨ ⟩, by rintro ⟨ ⟩ ⟩;
  · erw [ eq_comm, ZMod.natCast_eq_zero_iff ] ; exact Nat.not_dvd_of_pos_of_lt ( by decide ) ( by linarith )

/-
PROVIDED SOLUTION
Show the 6 elements x, s_map x, t_map x, st_map x, ts_map x, sts_map x are pairwise distinct using the fixed-point analysis. Any equality g₁(x) = g₂(x) with g₁ ≠ g₂ implies a nontrivial group element fixes x. The fixed points are: s fixes 1/2, t fixes ±1, st and ts fix roots of x²-x+1, sts fixes 0 and 2. All excluded by hypothesis.
-/
lemma orbit_card_six (x : ZMod p)
    (hx0 : x ≠ 0) (hx1 : x ≠ 1) (hxn1 : x ≠ -1)
    (hxh : x ≠ (2 : ZMod p)⁻¹) (hx2 : x ≠ 2)
    (hpoly : x ^ 2 - x + 1 ≠ 0) :
    (orb x).card = 6 := by
  unfold orb;
  rw [ Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_insert_of_notMem ] <;> simp +decide [ *, s_map, t_map, st_map, ts_map, sts_map ];
  · grind;
  · grind;
  · grind;
  · grind;
  · grind

/-! ### Per-orbit independence -/

/-
PROVIDED SOLUTION
Need to show for all a, b ∈ {0}: a + b ≠ 1 and a * b ≠ 1. Since a = b = 0: 0 + 0 = 0 ≠ 1 (since p is prime, p ≥ 2, so 1 ≠ 0 in ZMod p) and 0 * 0 = 0 ≠ 1. Use simp [avoidsOne] and then show (0:ZMod p) ≠ 1 using ZMod.val reasoning or Fact.out.
-/
lemma zero_indep : avoidsOne ({0} : Finset (ZMod p)) := by
  constructor <;> simp +decide

/-
PROVIDED SOLUTION
Need: for all a, b ∈ {2}: a + b ≠ 1 and a * b ≠ 1. So 2 + 2 = 4 ≠ 1 and 2 * 2 = 4 ≠ 1 in ZMod p. Since p ≥ 5 and p is prime, 3 ≠ 0 in ZMod p (because p doesn't divide 3). So 4 ≠ 1 (since 4 - 1 = 3 ≠ 0). Use simp [avoidsOne], then show (4:ZMod p) ≠ 1, which follows from (3:ZMod p) ≠ 0, which follows from p ≥ 5 and p prime (so p doesn't divide 3).
-/
lemma two_indep (hp5 : 5 ≤ p) : avoidsOne ({2} : Finset (ZMod p)) := by
  constructor <;> norm_num;
  · rcases p with ( _ | _ | _ | _ | _ | _ | p ) <;> norm_num [ Fin.ext_iff, ZMod ] at *;
    · decide +revert;
    · rintro ⟨ ⟩;
  · rcases p with ( _ | _ | _ | _ | _ | _ | p ) <;> norm_num [ Fin.ext_iff, ZMod ] at *;
    · decide +revert;
    · rintro ⟨ ⟩

/-
PROVIDED SOLUTION
Need: u + u ≠ 1 and u * u ≠ 1 for u with u² - u + 1 = 0 and p ≥ 5.
u + u = 2u. If 2u = 1, then u = (2:ZMod p)⁻¹. Substituting into u² - u + 1 = 0: (2⁻¹)² - 2⁻¹ + 1 = (1 - 2 + 4)/4 = 3/4. Since p ≥ 5, 3 ≠ 0 and 4 ≠ 0, so 3/4 ≠ 0. Contradiction.
u * u = u². From u² - u + 1 = 0, u² = u - 1. If u² = 1, then u - 1 = 1, so u = 2. But 2² - 2 + 1 = 3 ≠ 0 for p ≥ 5 (since p ∤ 3). Contradiction.
-/
lemma root_indep {u : ZMod p} (hu : u ^ 2 - u + 1 = 0) (hp5 : 5 ≤ p) :
    avoidsOne ({u} : Finset (ZMod p)) := by
  constructor <;> intro a b <;> simp_all +decide;
  · intro h;
    grind +suggestions;
  · by_contra h_contra
    have h_u_one : u = 2 := by
      grind
    subst h_u_one
    norm_num at *; (
    rcases p with ( _ | _ | _ | _ | _ | p ) <;> cases hu <;> contradiction;);

/-
PROBLEM
This leads to a contradiction since $p \geq 5$ implies $3 \neq 0$ in $\mathbb{Z}/p\mathbb{Z}$.

PROVIDED SOLUTION
Need to show avoidsOne {x, ts_map x, st_map x} where ts_map x = (1-x)⁻¹ and st_map x = 1-x⁻¹, under the hypotheses x ≠ 0, 1, -1, 2⁻¹, 2 and x²-x+1 ≠ 0, with p ≥ 5.

Sum checks (all pairs a + b ≠ 1):
1. x + x = 2x ≠ 1 because x ≠ (2:ZMod p)⁻¹ (= 1/2)
2. x + (1-x)⁻¹ ≠ 1: If x + (1-x)⁻¹ = 1, then (1-x)⁻¹ = 1-x, so (1-x)² = 1, so 1-x = ±1, so x = 0 or x = 2. Contradiction.
3. x + (1-x⁻¹) ≠ 1: If x + 1 - x⁻¹ = 1, then x = x⁻¹, so x² = 1, so x = ±1. Contradiction.
4. (1-x)⁻¹ + (1-x)⁻¹ = 2(1-x)⁻¹ ≠ 1: If 2(1-x)⁻¹ = 1 then (1-x)⁻¹ = 1/2, so 1-x = 2, so x = -1. Contradiction.
5. (1-x)⁻¹ + (1-x⁻¹) ≠ 1: (1-x)⁻¹ + 1 - x⁻¹ = 1 means (1-x)⁻¹ = x⁻¹, so 1-x = x, so 2x = 1, x = 1/2 = 2⁻¹. Contradiction.
6. (1-x⁻¹) + (1-x⁻¹) = 2(1-x⁻¹) ≠ 1: means 1-x⁻¹ = 1/2, so x⁻¹ = 1/2, x = 2. Contradiction.

Product checks (all pairs a * b ≠ 1):
1. x * x = x² ≠ 1 because x ≠ ±1.
2. x * (1-x)⁻¹ ≠ 1: If x/(1-x) = 1 then x = 1-x, so 2x = 1, x = 2⁻¹. Contradiction.
3. x * (1-x⁻¹) ≠ 1: x(1-x⁻¹) = x - 1. If x - 1 = 1 then x = 2. Contradiction.
4. (1-x)⁻¹ * (1-x)⁻¹ = (1-x)⁻² ≠ 1: means (1-x)² = 1, 1-x = ±1, x = 0 or 2. Contradiction.
5. (1-x)⁻¹ * (1-x⁻¹) ≠ 1: (1-x)⁻¹(1-x⁻¹) = (1-x)⁻¹·(x-1)/x = -(1-x)⁻¹·(1-x)/x = -1/x. If -1/x = 1 then x = -1. Contradiction.
6. (1-x⁻¹) * (1-x⁻¹) = (1-x⁻¹)² ≠ 1: means 1-x⁻¹ = ±1, so x⁻¹ = 0 (impossible for nonzero x) or x⁻¹ = 2, so x = 2⁻¹. Contradiction.

For each check, derive the contradiction from the hypotheses hx0, hx1, hxn1, hxh, hx2.
Unfold avoidsOne, ts_map, st_map, then for each pair, assume the equality and derive a contradiction with the hypotheses using field_simp and the excluded values.
-/
lemma triple_indep {x : ZMod p}
    (hx0 : x ≠ 0) (hx1 : x ≠ 1) (hxn1 : x ≠ -1)
    (hxh : x ≠ (2 : ZMod p)⁻¹) (hx2 : x ≠ 2) :
    avoidsOne ({x, ts_map x, st_map x} : Finset (ZMod p)) := by
  constructor;
  · simp +decide [ ts_map, st_map ];
    grind;
  · simp +zetaDelta at *;
    refine' ⟨ _, _, _ ⟩;
    · grind +locals;
    · unfold ts_map st_map;
      grind;
    · unfold st_map ts_map;
      grind

/-! ### Additional orbit lemmas -/

lemma orb_mem_self (x : ZMod p) : x ∈ orb x := by
  simp [orb]

/-
PROBLEM
Orbits are either equal or disjoint.

PROVIDED SOLUTION
If orb x ∩ orb y is nonempty, take z ∈ orb x ∩ orb y. Then z ∈ orb x and z ∈ orb y. By orb_eq_of_mem: orb z = orb x and orb z = orb y. Therefore orb x = orb y. If orb x ∩ orb y is empty, they are disjoint. Use Finset.eq_empty_or_nonempty on the intersection.
-/
lemma orb_eq_or_disjoint (x y : ZMod p) :
    orb x = orb y ∨ Disjoint (orb x) (orb y) := by
  by_contra! h_inter;
  obtain ⟨z, hzx, hzy⟩ : ∃ z, z ∈ orb x ∧ z ∈ orb y := by
    exact Finset.not_disjoint_iff.mp h_inter.2;
  exact h_inter.1 ( orb_eq_of_mem hzx ▸ orb_eq_of_mem hzy ▸ rfl )

/-
PROBLEM
The triple {x, ts_map x, st_map x} is a subset of orb x.

PROVIDED SOLUTION
Need to show x, ts_map x, st_map x are all in orb x. x ∈ orb x by orb_mem_self. ts_map x = (1-x)⁻¹ is the 5th element of orb x. st_map x = 1-x⁻¹ is the 4th element of orb x. Use simp [orb, ts_map, st_map] or Finset.insert_subset_iff.
-/
lemma triple_subset_orb (x : ZMod p) :
    ({x, ts_map x, st_map x} : Finset (ZMod p)) ⊆ orb x := by
  simp +decide [ Finset.subset_iff, orb ]

/-
PROBLEM
Union of independent sets from disjoint orbits is independent.

PROVIDED SOLUTION
Need: for all a' ∈ A ∪ B, b' ∈ A ∪ B: a' + b' ≠ 1 and a' * b' ≠ 1.
Case split on membership:
- a' ∈ A, b' ∈ A: use hA (avoidsOne A)
- a' ∈ B, b' ∈ B: use hB (avoidsOne B)
- a' ∈ A, b' ∈ B: use cross_orbit_safe with a' ∈ orb a (from hAo) and b' ∈ orb b (from hBo) and hdisj
- a' ∈ B, b' ∈ A: similar, using commutativity of + and *

For cross_orbit_safe: we need Disjoint (orb a) (orb b) which is hdisj, a' ∈ orb a (from hAo ha), b' ∈ orb b (from hBo hb).
-/
lemma avoidsOne_union {A B : Finset (ZMod p)} {a b : ZMod p}
    (hA : avoidsOne A) (hB : avoidsOne B)
    (hAo : A ⊆ orb a) (hBo : B ⊆ orb b)
    (hdisj : Disjoint (orb a) (orb b)) :
    avoidsOne (A ∪ B) := by
  refine ⟨ ?_, ?_ ⟩ <;> intro c hc c' hc';
  · rcases Finset.mem_union.1 hc with ( hc | hc ) <;> rcases Finset.mem_union.1 hc' with ( hc' | hc' ) <;> simp_all +decide [ avoidsOne ];
    · have := cross_orbit_safe hdisj ( hAo hc ) ( hBo hc' ) ; aesop;
    · exact cross_orbit_safe hdisj ( hAo hc' ) ( hBo hc ) |>.1 |> fun h => by rwa [ add_comm ] ;
  · simp +zetaDelta at *;
    rcases hc with ( hc | hc ) <;> rcases hc' with ( hc' | hc' );
    · exact hA.2 _ hc _ hc';
    · exact cross_orbit_safe hdisj ( hAo hc ) ( hBo hc' ) |>.2;
    · -- Since $c \in B$ and $B \subseteq orb b$, we have $c \in orb b$. Similarly, $c' \in A$ and $A \subseteq orb a$, so $c' \in orb a$.
      have hc_orb : c ∈ orb b := hBo hc
      have hc'_orb : c' ∈ orb a := hAo hc';
      -- Since $c \in orb b$ and $c' \in orb a$, and $orb a$ and $orb b$ are disjoint, we have $c * c' \neq 1$ by the cross-orbit safety lemma.
      have := cross_orbit_safe hdisj.symm hc_orb hc'_orb; (
      exact this.2);
    · exact hB.2 _ hc _ hc'

/-! ### Orbit-closed and choose function -/

/-- Each orbit is an orbit of some element. -/
lemma orbit_of_mem_image {O : Finset (ZMod p)}
    (hO : O ∈ (Finset.univ : Finset (ZMod p)).image orb) :
    ∃ x, O = orb x := by
  obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hO
  exact ⟨x, rfl⟩

/-- choose_indep selects an independent subset from an orbit. -/
noncomputable def choose_indep (O : Finset (ZMod p)) : Finset (ZMod p) :=
  if (0 : ZMod p) ∈ O then {0}
  else if (2 : ZMod p) ∈ O then {2}
  else if h : ∃ u ∈ O, u ^ 2 - u + 1 = 0 then {h.choose}
  else
    if hne : O.Nonempty then
      let x := hne.choose
      {x, ts_map x, st_map x}
    else ∅

/-
PROBLEM
choose_indep O ⊆ O when O is an orbit.

PROVIDED SOLUTION
Given O = orb x for some x. Unfold choose_indep and case split on the conditions:
1. If 0 ∈ O: choose_indep = {0}. Need 0 ∈ O, which is the hypothesis.
2. If 2 ∈ O: choose_indep = {2}. Need 2 ∈ O, which is the hypothesis.
3. If ∃ u ∈ O, u²-u+1=0: choose_indep = {h.choose}. h.choose ∈ O by h.choose_spec.1 (or the choose property).
4. If O.Nonempty: let x = hne.choose. choose_indep = {x, ts_map x, st_map x}. Need x ∈ O (by hne.choose_spec), ts_map x ∈ O, st_map x ∈ O. Since x ∈ O = orb y for some y, and orb_eq_of_mem gives orb x = orb y = O. Then ts_map x ∈ orb x = O (by triple_subset_orb). Similarly st_map x ∈ O.
5. If ¬O.Nonempty: choose_indep = ∅ ⊆ O trivially.
-/
lemma choose_indep_subset {O : Finset (ZMod p)} (hO : ∃ x, O = orb x) :
    choose_indep O ⊆ O := by
  unfold choose_indep;
  split_ifs <;> simp_all +decide [ Finset.subset_iff ];
  · exact Exists.choose_spec ‹∃ u ∈ O, u ^ 2 - u + 1 = 0› |>.1;
  · have h_orb : ∀ x ∈ O, ts_map x ∈ O ∧ st_map x ∈ O := by
      obtain ⟨ x, rfl ⟩ := hO;
      intros y hy; exact ⟨ by
        rw [ ← orb_eq_of_mem hy ];
        exact Finset.mem_insert_of_mem ( Finset.mem_insert_of_mem ( Finset.mem_insert_of_mem ( Finset.mem_insert_of_mem ( Finset.mem_insert_self _ _ ) ) ) ), by
        rw [ ← orb_eq_of_mem hy ];
        exact Finset.mem_insert_of_mem ( Finset.mem_insert_of_mem ( Finset.mem_insert_of_mem ( Finset.mem_insert_self _ _ ) ) ) ⟩;
    exact ⟨ Exists.choose_spec ‹_›, h_orb _ ( Exists.choose_spec ‹_› ) ⟩

/-
PROBLEM
choose_indep O is independent when O is an orbit.

PROVIDED SOLUTION
Given O = orb x for some x. Unfold choose_indep and case split:
1. If 0 ∈ O: choose_indep = {0}. Use zero_indep.
2. If 2 ∈ O: choose_indep = {2}. Use two_indep hp5.
3. If ∃ u ∈ O, u²-u+1=0: choose_indep = {h.choose}. Use root_indep (h.choose_spec.2) hp5.
4. If O.Nonempty with x = hne.choose: choose_indep = {x, ts_map x, st_map x}. Use triple_indep hp5. Need to verify x satisfies the generic conditions (x ≠ 0, 1, -1, 2⁻¹, 2, x²-x+1 ≠ 0). Since 0 ∉ O and O = orb y, x = hne.choose ∈ O. If x = 0 then 0 ∈ O, contradicting the first branch. Similarly for 2. For x = 1: 1 ∈ orb y = O, and s_map 1 = 0 ∈ O (since orb is orbit-closed). So 0 ∈ O, contradicting first branch. Similarly for -1 (s_map(-1)=2∈O), 2⁻¹ (t_map(2⁻¹)=2∈O). For x²-x+1=0: then ∃ u ∈ O with u²-u+1=0, contradicting third branch.
5. If ¬O.Nonempty: choose_indep = ∅. avoidsOne ∅ trivially.
-/
set_option maxHeartbeats 400000 in
lemma choose_indep_avoidsOne (hp5 : 5 ≤ p) {O : Finset (ZMod p)} (hO : ∃ x, O = orb x) :
    avoidsOne (choose_indep O) := by
  unfold choose_indep;
  split_ifs;
  · exact zero_indep;
  · exact two_indep hp5;
  · exact root_indep ( Classical.choose_spec ‹∃ u ∈ O, u ^ 2 - u + 1 = 0› |>.2 ) hp5;
  · rename_i h₁ h₂ h₃ h₄;
    convert triple_indep _ _ _ _ _ ;
    all_goals have := h₄.choose_spec; simp_all +decide [ Finset.ext_iff, orb ];
    · exact fun h => h₁ <| h ▸ this;
    · grind +locals;
    · intro h; have := h₃ _ this; simp_all +decide [ s_map, t_map, st_map, ts_map, sts_map ] ;
      grind +splitImp;
    · contrapose! h₂; have := hO.choose_spec ( 2⁻¹ ) ; simp_all +decide [ s_map, t_map, st_map, ts_map, sts_map ] ;
      grind;
    · exact fun h => h₂ <| h ▸ this;
  · exact ⟨ by tauto, by tauto ⟩

/-
PROBLEM
choose_indep O has the right cardinality relative to O.

PROVIDED SOLUTION
Given O = orb x for some x. We show 2 * |choose_indep O| + (if O.card = 3 then 1 else 0) = |O|.

Case split on the branches of choose_indep:

1. If 0 ∈ O: choose_indep = {0}, card = 1. O = orb x and 0 ∈ orb x, so orb x = orb 0. |orb 0| = 2 (orb 0 = {0, 1} which has card 2 for p ≥ 2). So 2*1 + 0 = 2 = |O|. Need to show O.card ≠ 3, which is true since O.card = 2.

2. If 2 ∈ O (and 0 ∉ O): choose_indep = {2}, card = 1. O = orb x and 2 ∈ orb x, so orb x = orb 2. |orb 2| = 3 (for p ≥ 5). So 2*1 + 1 = 3 = |O|. Need O.card = 3.

3. If ∃ u ∈ O, u²-u+1=0 (and 0,2 ∉ O): choose_indep = {h.choose}, card = 1. O = orb x and the root u ∈ orb x. The orbit of a root of x²-x+1 has size 2 (since s_map(u) = 1-u which is the other root, and all other orbit elements collapse to u or 1-u because u⁻¹ = 1-u). So |O| = 2 and 2*1 + 0 = 2 = |O|.

4. O.Nonempty (and 0,2 ∉ O and no root): choose_indep = {x, ts_map x, st_map x}, card = 3 (since the three elements are distinct by orbit_card_six — the full orbit has 6 distinct elements, and these three are among them). |O| = 6 (by orbit_card_six). 2*3 + 0 = 6 = |O|.

5. ¬O.Nonempty: card = 0. |O| = 0. 2*0 + 0 = 0. ✓

Key lemmas needed: orbit sizes for each type. The orbit of 0 has card 2. The orbit of 2 has card 3 (for p ≥ 5). The orbit of a root has card 2. Generic orbits have card 6.
-/
set_option maxHeartbeats 800000 in
lemma choose_indep_card (hp5 : 5 ≤ p) {O : Finset (ZMod p)} (hO : ∃ x, O = orb x) :
    2 * (choose_indep O).card + (if O.card = 3 then 1 else 0) = O.card := by
  cases' hO with x hx;
  by_cases h0 : 0 ∈ orb x <;> by_cases h2 : 2 ∈ orb x;
  · -- Since $0 \in orb x$ and $2 \in orb x$, we have $orb x = orb 0$.
    have h_orb_eq_orb0 : orb x = orb 0 := by
      rw [ ← orb_eq_of_mem h0 ];
    grind +locals;
  · unfold choose_indep;
    split_ifs <;> simp_all +decide;
    unfold orb at *;
    unfold s_map t_map st_map ts_map sts_map at *;
    by_cases hx : x = 0 <;> by_cases hx' : x = 1 <;> simp_all +decide;
    grind;
  · -- If $2 \in orb x$, then $orb x = orb 2$.
    have h_orbit_2 : orb x = orb 2 := by
      rw [ ← orb_eq_of_mem h2 ];
    -- The orbit of 2 is {2, -1, 1/2}.
    have h_orbit_2_elements : orb 2 = {2, -1, (2 : ZMod p)⁻¹} := by
      unfold orb;
      unfold s_map t_map st_map ts_map sts_map;
      grind +revert;
    -- Since $2 \neq -1$ and $2 \neq 2^{-1}$, and $-1 \neq 2^{-1}$, the set $\{2, -1, 2^{-1}\}$ has exactly three elements.
    have h_distinct : (2 : ZMod p) ≠ -1 ∧ (2 : ZMod p) ≠ (2 : ZMod p)⁻¹ ∧ (-1 : ZMod p) ≠ (2 : ZMod p)⁻¹ := by
      refine' ⟨ _, _, _ ⟩;
      · rw [ Ne.eq_def, eq_neg_iff_add_eq_zero ];
        norm_num;
        erw [ ZMod.natCast_eq_zero_iff ] ; exact Nat.not_dvd_of_pos_of_lt ( by decide ) ( by linarith );
      · rw [ Ne.eq_def, inv_eq_one_div, eq_div_iff ] <;> norm_num;
        · intro h; rcases p with ( _ | _ | _ | _ | _ | p ) <;> cases h <;> contradiction;
        · erw [ ZMod.natCast_eq_zero_iff ] ; exact Nat.not_dvd_of_pos_of_lt ( by decide ) ( by linarith );
      · rw [ Ne.eq_def, inv_eq_one_div, eq_div_iff ] <;> norm_num;
        · rw [ neg_eq_iff_add_eq_zero ] ; norm_num;
          erw [ ZMod.natCast_eq_zero_iff ] ; exact Nat.not_dvd_of_pos_of_lt ( by decide ) ( by linarith );
        · erw [ ZMod.natCast_eq_zero_iff ] ; exact Nat.not_dvd_of_pos_of_lt ( by decide ) ( by linarith );
    unfold choose_indep; simp_all +decide ;
  · by_cases hroot : ∃ u ∈ orb x, u ^ 2 - u + 1 = 0;
    · have h_orbit_size : ∀ u : ZMod p, u ∈ orb x → u ^ 2 - u + 1 = 0 → orb u = {u, 1 - u} := by
        grind +locals;
      obtain ⟨ u, hu, hu' ⟩ := hroot;
      have h_orbit_size : orb x = {u, 1 - u} := by
        rw [ ← h_orbit_size u hu hu', orb_eq_of_mem hu ];
      -- Since $u$ is a root of $x^2 - x + 1$, we have $u \neq 1 - u$.
      have h_distinct : u ≠ 1 - u := by
        grind +locals;
      unfold choose_indep; aesop;
    · -- Since O is nonempty and doesn't contain 0, 2, or any roots of x²-x+1, we can choose any element x from O and show that the triple {x, ts_map x, st_map x} is independent and has cardinality 3.
      have h_card_triple : (choose_indep O).card = 3 := by
        unfold choose_indep;
        split_ifs <;> simp_all +decide;
        · grind +revert;
        · rw [ Finset.card_insert_of_notMem, Finset.card_insert_of_notMem ] <;> simp +decide [ * ];
          · unfold ts_map st_map;
            rw [ inv_eq_one_div, div_eq_iff ];
            · grind;
            · have := Exists.choose_spec ( Finset.card_pos.mp ( Finset.card_pos.mpr ‹_› ) );
              simp_all +decide [ sub_eq_iff_eq_add, orb ];
              rcases this with ( h | h | h | h | h | h ) <;> simp_all +decide [ s_map, t_map, st_map, ts_map, sts_map ];
              · grind;
              · grind +ring;
              · aesop;
              · grind;
              · grind;
          · grind +locals;
        · simp_all +decide [ orb ];
      -- Since O is nonempty and doesn't contain 0, 2, or any roots of x²-x+1, we can choose any element x from O and show that the orbit of x has cardinality 6.
      have h_card_orbit : (orb x).card = 6 := by
        apply orbit_card_six x;
        all_goals contrapose! hroot; simp_all +decide [ orb ];
        · simp_all +decide [ s_map, t_map, st_map, ts_map, sts_map ];
        · simp_all +decide [ s_map, t_map, st_map, ts_map, sts_map ];
          norm_num at *;
        · simp_all +decide [ s_map, t_map, st_map, ts_map, sts_map ];
      aesop

/-! ### Main theorem -/

/-
PROVIDED SOLUTION
Construct A = ((Finset.univ : Finset (ZMod p)).image orb).biUnion (choose_indep hp5).

For avoidsOne: Take a, b ∈ A. Then a ∈ choose_indep hp5 Oa and b ∈ choose_indep hp5 Ob for some orbits Oa, Ob in the image. By orbit_of_mem_image, Oa = orb xa and Ob = orb xb.
- If Oa = Ob: a, b ∈ choose_indep hp5 Oa. By choose_indep_avoidsOne, this is independent.
- If Oa ≠ Ob: By orb_eq_or_disjoint, Disjoint Oa Ob. By choose_indep_subset, a ∈ Oa and b ∈ Ob. By cross_orbit_safe, a+b ≠ 1 and a*b ≠ 1.

For card = (p-1)/2: Use Finset.card_biUnion with disjointness. The orbits in the image are pairwise disjoint (by orb_eq_or_disjoint: either equal, and image deduplicates, or disjoint). The choose_indep sets are subsets of their orbits, so also pairwise disjoint.

|A| = ∑_{O ∈ orbits} |choose_indep hp5 O|.

By choose_indep_card: 2 * |choose_indep hp5 O| + (if O.card = 3 then 1 else 0) = O.card.
Sum over all orbits: 2 * |A| + (number of size-3 orbits) = ∑ O.card = p (since orbits partition ZMod p).

There is exactly one size-3 orbit (orb 2 = {2, 2⁻¹, -1}, for p ≥ 5).

So 2 * |A| + 1 = p, giving |A| = (p-1)/2.

To show the orbits partition Finset.univ: every x ∈ Finset.univ is in orb x which is in the image. So Finset.univ ⊆ biUnion. And biUnion ⊆ Finset.univ trivially.

To show exactly one size-3 orbit: orb 2 has card 3. The orbits of 0 have card 2 (orb 0 = {0,1}). Generic orbits have card 6. Root orbits have card 2. Only orb 2 has card 3.
-/
set_option maxHeartbeats 1600000 in
theorem exists_large_avoiding_set (hp5 : 5 ≤ p) :
    ∃ A : Finset (ZMod p), A.card = (p - 1) / 2 ∧ avoidsOne A := by
  refine ⟨ Finset.biUnion ( Finset.image orb ( Finset.univ : Finset ( ZMod p ) ) ) ( choose_indep ), ?_, ?_ ⟩;
  · rw [ Finset.card_biUnion ];
    · -- Let's count the number of orbits of size 3.
      have h_count_orbits : ∑ O ∈ Finset.image orb (Finset.univ : Finset (ZMod p)), (if O.card = 3 then 1 else 0) = 1 := by
        rw [ Finset.sum_eq_single ( orb 2 ) ];
        · simp +decide [ orb ];
          unfold s_map t_map st_map ts_map sts_map;
          rw [ Finset.card_eq_three ];
          refine' ⟨ 2, 1 - 2, 2⁻¹, _, _, _, _ ⟩ <;> norm_num;
          · rw [ eq_neg_iff_add_eq_zero ] ; norm_num;
            erw [ ZMod.natCast_eq_zero_iff ] ; exact Nat.not_dvd_of_pos_of_lt ( by decide ) ( by linarith );
          · rw [ inv_eq_one_div, eq_div_iff ] <;> norm_num;
            · intro h; rcases p with ( _ | _ | _ | _ | _ | p ) <;> cases h <;> contradiction;
            · erw [ ZMod.natCast_eq_zero_iff ] ; exact Nat.not_dvd_of_pos_of_lt ( by decide ) ( by linarith );
          · rw [ inv_eq_one_div, eq_div_iff ] <;> norm_num;
            · rw [ neg_eq_iff_add_eq_zero ] ; norm_num;
              erw [ ZMod.natCast_eq_zero_iff ] ; exact Nat.not_dvd_of_pos_of_lt ( by decide ) ( by linarith );
            · erw [ ZMod.natCast_eq_zero_iff ] ; exact Nat.not_dvd_of_pos_of_lt ( by decide ) ( by linarith );
          · grind +qlia;
        · intro b hb hb'; split_ifs <;> simp_all +decide ;
          obtain ⟨ x, rfl ⟩ := hb;
          -- If $|orb x| = 3$, then $x$ must be one of $0$, $1$, $-1$, $2^{-1}$, $2$, or a root of $x^2 - x + 1 = 0$.
          have h_cases : x = 0 ∨ x = 1 ∨ x = -1 ∨ x = (2 : ZMod p)⁻¹ ∨ x = 2 ∨ x ^ 2 - x + 1 = 0 := by
            contrapose! hb';
            exact absurd ‹#(orb x) = 3› ( by rw [ orbit_card_six x hb'.1 hb'.2.1 hb'.2.2.1 hb'.2.2.2.1 hb'.2.2.2.2.1 hb'.2.2.2.2.2 ] ; decide );
          rcases h_cases with ( rfl | rfl | rfl | rfl | rfl | h_cases ) <;> simp_all +decide [ orb ];
          · simp_all +decide [ s_map, t_map, st_map, ts_map, sts_map ];
          · simp_all +decide [ s_map, t_map, st_map, ts_map, sts_map ];
          · simp_all +decide [ s_map, t_map, st_map, ts_map, sts_map ];
            grind;
          · unfold s_map t_map st_map ts_map sts_map at * ; simp_all +decide;
            grind;
          · grind +locals;
        · exact fun h => False.elim <| h <| Finset.mem_image_of_mem _ <| Finset.mem_univ _;
      have h_sum_card : ∑ O ∈ Finset.image orb (Finset.univ : Finset (ZMod p)), O.card = p := by
        rw [ ← Finset.card_biUnion ];
        · convert Finset.card_univ;
          all_goals try infer_instance;
          · ext x; simp [orb];
          · rw [ ZMod.card ];
        · intros O hO O' hO' hOO';
          obtain ⟨ x, hx, rfl ⟩ := Finset.mem_image.mp hO; obtain ⟨ x', hx', rfl ⟩ := Finset.mem_image.mp hO'; simp_all +decide [ Finset.disjoint_left ] ;
          exact fun y hy hy' => hOO' <| orb_eq_of_mem hy ▸ orb_eq_of_mem hy' ▸ rfl;
      have h_sum_card : ∑ O ∈ Finset.image orb (Finset.univ : Finset (ZMod p)), (2 * (choose_indep O).card + (if O.card = 3 then 1 else 0)) = p := by
        rw [ Finset.sum_congr rfl fun x hx => choose_indep_card hp5 <| orbit_of_mem_image hx, h_sum_card ];
      simp_all +decide [ Finset.sum_add_distrib];
      exact Eq.symm ( Nat.div_eq_of_eq_mul_left zero_lt_two ( Nat.sub_eq_of_eq_add <| by rw [ ← Finset.mul_sum _ _ _ ] at *; linarith ) );
    · intros O hO O' hO' hne;
      obtain ⟨ x, hx, rfl ⟩ := Finset.mem_image.mp hO; obtain ⟨ x', hx', rfl ⟩ := Finset.mem_image.mp hO'; simp +decide [ *, Finset.disjoint_left ] ;
      have := orb_eq_or_disjoint x x'; simp_all +decide [ Finset.disjoint_left ] ;
      exact fun a ha hb => this ( choose_indep_subset ( orbit_of_mem_image ( Finset.mem_image_of_mem _ ( Finset.mem_univ _ ) ) ) ha ) ( choose_indep_subset ( orbit_of_mem_image ( Finset.mem_image_of_mem _ ( Finset.mem_univ _ ) ) ) hb );
  · simp_all +decide [ avoidsOne ];
    constructor <;> intro a x hx b y hy;
    · by_cases hxy : orb x = orb y;
      · have := choose_indep_avoidsOne hp5 ( show ∃ z, orb y = orb z from ⟨ y, rfl ⟩ );
        exact this.1 _ ( hxy ▸ hx ) _ hy;
      · have hdisj : Disjoint (orb x) (orb y) := by
          exact Or.resolve_left ( orb_eq_or_disjoint x y ) hxy;
        exact cross_orbit_safe hdisj ( choose_indep_subset ( orbit_of_mem_image ( Finset.mem_image_of_mem _ ( Finset.mem_univ _ ) ) |> fun h => by aesop ) hx ) ( choose_indep_subset ( orbit_of_mem_image ( Finset.mem_image_of_mem _ ( Finset.mem_univ _ ) ) |> fun h => by aesop ) hy ) |>.1;
    · by_cases h : orb x = orb y;
      · have := choose_indep_avoidsOne hp5 ( show ∃ z, orb y = orb z from ⟨ y, rfl ⟩ );
        exact this.2 a ( by aesop ) b ( by aesop );
      · have h_disjoint : Disjoint (orb x) (orb y) := by
          exact Classical.not_not.1 fun h' => h <| by have := orb_eq_or_disjoint x y; tauto;
        exact cross_orbit_safe h_disjoint ( choose_indep_subset ( ⟨ x, rfl ⟩ ) hx ) ( choose_indep_subset ( ⟨ y, rfl ⟩ ) hy ) |>.2

/-! ## Corollary: Sárközy's Conjecture 65 is false -/

/-
PROBLEM
Upper bound: if `avoidsOne A` holds then `A.card ≤ (p - 1) / 2`.
    This follows from Proposition 1: if `|A| > p/2` then `A + A = F_p`,
    so in particular `1 ∈ A + A`, contradicting `avoidsOne`.

PROVIDED SOLUTION
If A.card * 2 > p then by sumset_covers, A+A = F_p, so 1 ∈ A+A, which means there exist a, b ∈ A with a+b=1, contradicting hA.1. So A.card * 2 ≤ p. Since p is odd prime ≥ 5, p is odd, so A.card ≤ (p-1)/2 follows from A.card * 2 ≤ p and the fact that p is odd (so (p-1)/2 = p/2 in ℕ division, and A.card * 2 ≤ p implies A.card ≤ p/2 = (p-1)/2 since p is odd).
-/
lemma avoidsOne_card_le (hp5 : 5 ≤ p) (A : Finset (ZMod p)) (hA : avoidsOne A) :
    A.card ≤ (p - 1) / 2 := by
      -- By Proposition 1, if $|A| > p/2$, then $A + A = F_p$.
      by_contra h_contra
      have h_sumset : A + A = Finset.univ := by
        apply sumset_eq_univ;
        linarith [ Nat.div_mul_cancel ( show 2 ∣ p - 1 from even_iff_two_dvd.mp ( hp.1.even_sub_one <| by linarith ) ), Nat.sub_add_cancel hp.1.pos ];
      simp_all +decide [ Finset.ext_iff ];
      obtain ⟨ a, b, ha, hb, hab ⟩ := Finset.mem_add.mp ( h_sumset 1 );
      exact hA.1 a b ha hb hab

/-- Remark: the exact extremal value is `(p - 1) / 2`. -/
theorem exact_extremal_value (hp5 : 5 ≤ p) :
    IsGreatest {n | ∃ A : Finset (ZMod p), A.card = n ∧ avoidsOne A} ((p - 1) / 2) := by
  constructor
  · exact exists_large_avoiding_set hp5
  · intro n ⟨A, hAn, hA⟩
    rw [← hAn]
    exact avoidsOne_card_le hp5 A hA

/-
PROBLEM
Corollary: Sárközy's Conjecture 65 is false. For every `c > 0` and `p₀ : ℕ`,
    there exists a prime `p > p₀` and a set `A ⊆ 𝔽_p` with
    `|A| > (1/2 - c) * p` such that `1 ∉ A + A` and `1 ∉ A * A`.

PROVIDED SOLUTION
Given c > 0 and p₀, we need to find a prime p > p₀ with p ≥ 5, and a set A with |A| > (1/2 - c)*p and avoidsOne A.

By Nat.exists_infinite_primes, there exists a prime p > max(p₀, 4). Then p ≥ 5. By exists_large_avoiding_set hp5, there exists A with A.card = (p-1)/2 and avoidsOne A.

We need (A.card : ℚ) > (1/2 - c) * p, i.e., (p-1)/2 > (1/2 - c)*p = p/2 - cp.
This is equivalent to (p-1)/2 > p/2 - cp, i.e., cp > p/2 - (p-1)/2 = 1/2.
Since p > 4, we have p ≥ 5, so cp ≥ 5c. We need cp > 1/2.
Actually we need to be more careful: (p-1)/2 as ℕ division cast to ℚ equals (p-1)/2 as ℚ since p is odd. And (p-1)/2 = p/2 - 1/2.
So the condition becomes p/2 - 1/2 > p/2 - cp, i.e., cp > 1/2, i.e., p > 1/(2c).

So we need p > 1/(2c). Choose p to be a prime larger than max(p₀, 4, ⌈1/(2c)⌉). This is possible by Nat.exists_infinite_primes.

Given c > 0 and p₀, we need to find a prime p > p₀ with p ≥ 5, and a set A with |A| > (1/2 - c)*p and avoidsOne A.

By Nat.exists_infinite_primes, there exists a prime p > max(p₀, 4, ⌈1/(2c)⌉). Then p ≥ 5. By exists_large_avoiding_set, there exists A with A.card = (p-1)/2 and avoidsOne A.

We need (A.card : ℝ) > (1/2 - c) * p, i.e., (p-1)/2 > (1/2 - c)*p = p/2 - cp.
Since p is odd prime, (p-1)/2 cast to ℝ equals (↑p - 1)/2. So the condition becomes (p-1)/2 > p/2 - cp, i.e., cp > 1/2, i.e., p > 1/(2c). This holds by our choice of p.

Key steps:
1. Use Nat.exists_infinite_primes to get prime p large enough (> p₀ + 5 + ⌈1/(2c)⌉₊ + 1).
2. Use exists_large_avoiding_set to get A.
3. For the cardinality bound, use Nat.cast_div to rewrite (↑((p-1)/2)) as (↑(p-1))/2, using that 2 ∣ p-1 (since p is odd prime ≥ 5). Then Nat.cast_sub to get (↑p - 1)/2. Then the inequality cp > 1/2 follows from p > 1/(2c).

For the ceil part with reals: use Nat.lt_of_ceil_lt or just cast ⌈1/(2c)⌉₊ and use Nat.le_ceil.
-/
theorem sarkozy_conjecture_false :
    ∀ (c : ℝ) (_ : 0 < c) (p₀ : ℕ),
    ∃ (p : ℕ) (_ : Fact (Nat.Prime p)),
      p₀ < p ∧
      ∃ A : Finset (ZMod p),
        (A.card : ℝ) > (1/2 - c) * p ∧ avoidsOne A := by
          intro c hc₁;
          -- We'll use that for any prime $p \geq 5$, there exists a set $A \subseteq \mathbb{F}_p$ with $|A| = \frac{p-1}{2}$ such that $1 \notin A + A$ and $1 \notin A * A$.
          have h_exists_A : ∀ (p : ℕ) (_ : Fact (Nat.Prime p)) (hp : 5 ≤ p), ∃ A : Finset (ZMod p), A.card = (p - 1) / 2 ∧ avoidsOne A := by
            intro p x hp; exact exists_large_avoiding_set hp;
          -- Choose a prime $p$ such that $p > \max(p₀, \frac{1}{2c} + 5)$.
          intro p₀
          obtain ⟨p, hp⟩ : ∃ p : ℕ, Fact (Nat.Prime p) ∧ p₀ < p ∧ 5 ≤ p ∧ (p - 1) / 2 > (1 / 2 - c) * p := by
            obtain ⟨ p, hp₁, hp₂ ⟩ := Nat.exists_infinite_primes ( p₀ + 5 + ⌈ ( c ) ⁻¹ * 2⌉₊ + 1 );
            refine' ⟨ p, ⟨ hp₂ ⟩, by linarith, by linarith, _ ⟩;
            nlinarith [ Nat.le_ceil ( c⁻¹ * 2 ), mul_inv_cancel₀ hc₁.ne', show ( p : ℝ ) ≥ p₀ + 5 + ⌈c⁻¹ * 2⌉₊ + 1 by exact_mod_cast hp₁ ];
          obtain ⟨ A, hA₁, hA₂ ⟩ := h_exists_A p hp.1 hp.2.2.1;
          refine' ⟨ p, hp.1, hp.2.1, A, _, hA₂ ⟩;
          rcases Nat.even_or_odd' p with ⟨ k, rfl | rfl ⟩ <;> norm_num at *;
          · exact absurd ( hp.1.1.eq_two_or_odd ) ( by omega );
          · grind

/-- Combined statement: the sharp threshold is exactly `1/2`. -/
theorem sarkozy_threshold_sharp (hp5 : 5 ≤ p) :
    (∀ A : Finset (ZMod p), p < A.card * 2 → A + A = Finset.univ) ∧
    (∃ A : Finset (ZMod p), A.card = (p - 1) / 2 ∧ avoidsOne A) :=
  ⟨sumset_eq_univ, exists_large_avoiding_set hp5⟩

#print axioms sarkozy_threshold_sharp
#print axioms exact_extremal_value
#print axioms sarkozy_conjecture_false

end