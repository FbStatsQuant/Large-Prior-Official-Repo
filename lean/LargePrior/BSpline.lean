import LargePrior.Basis

/-!
# B-splines: nonnegativity, partition of unity, Assumption 1
-/

open MeasureTheory Finset
open scoped Matrix

noncomputable section

namespace LargePrior

/-! ## Knots -/

lemma knot_mono (q K : ℕ) : Monotone (knot q K) := by
  intro i j hij
  have hij' : (i : ℝ) ≤ j := by exact_mod_cast hij
  unfold knot
  apply max_le_max le_rfl
  apply min_le_min le_rfl
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg K)
  linarith

lemma knot_nonneg (q K i : ℕ) : 0 ≤ knot q K i := le_max_left _ _

lemma knot_le_one (q K i : ℕ) : knot q K i ≤ 1 := max_le zero_le_one (min_le_left _ _)

lemma knot_eq_zero {q K i : ℕ} (hi : i + 1 ≤ q) : knot q K i = 0 := by
  have hi' : ((i : ℝ) + 1) ≤ q := by exact_mod_cast hi
  have hv : ((i : ℝ) - ((q : ℝ) - 1)) / K ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (by linarith) (Nat.cast_nonneg K)
  unfold knot
  exact max_eq_left (min_le_of_right_le hv)

private lemma knot_eq_one_iff_aux {q K i : ℕ} :
    knot q K i = 1 ↔ 1 ≤ ((i : ℝ) - ((q : ℝ) - 1)) / K := by
  unfold knot
  constructor
  · intro h
    by_contra h'
    have : max 0 (min 1 (((i : ℝ) - ((q : ℝ) - 1)) / K)) < 1 :=
      max_lt zero_lt_one (min_lt_of_right_lt (not_le.1 h'))
    linarith
  · intro h
    rw [min_eq_left h, max_eq_right zero_le_one]

lemma knot_eq_one_iff {q K i : ℕ} (hK : 1 ≤ K) : knot q K i = 1 ↔ K + q ≤ i + 1 := by
  have hKpos : (0 : ℝ) < K := by exact_mod_cast hK
  rw [knot_eq_one_iff_aux, le_div_iff₀ hKpos, one_mul]
  constructor
  · intro h
    have : ((K + q : ℕ) : ℝ) ≤ ((i + 1 : ℕ) : ℝ) := by push_cast; linarith
    exact_mod_cast this
  · intro h
    have : ((K + q : ℕ) : ℝ) ≤ ((i + 1 : ℕ) : ℝ) := by exact_mod_cast h
    push_cast at this
    linarith

lemma knot_lt_one_iff {q K i : ℕ} (hK : 1 ≤ K) : knot q K i < 1 ↔ i + 1 < K + q := by
  constructor
  · intro h
    by_contra h'
    have := (knot_eq_one_iff hK).2 (not_lt.1 h')
    linarith
  · intro h
    rcases (knot_le_one q K i).lt_or_eq with h1 | h1
    · exact h1
    · have := (knot_eq_one_iff hK).1 h1
      omega

/-! ## Support and nonnegativity -/

private lemma bspl_one (q K i : ℕ) (x : ℝ) :
    bspl q K 1 i x = if (knot q K i ≤ x ∧ x < knot q K (i + 1)) ∨
          (x = 1 ∧ knot q K i < 1 ∧ knot q K (i + 1) = 1) then 1 else 0 := rfl

private lemma bspl_succ_succ (q K k i : ℕ) (x : ℝ) :
    bspl q K (k + 2) i x =
      (x - knot q K i) / (knot q K (i + k + 1) - knot q K i) * bspl q K (k + 1) i x +
        (knot q K (i + k + 2) - x) / (knot q K (i + k + 2) - knot q K (i + 1)) *
          bspl q K (k + 1) (i + 1) x := rfl

private lemma bspl_support_aux (q K : ℕ) (x : ℝ) :
    ∀ n i, bspl q K (n + 1) i x ≠ 0 → knot q K i ≤ x ∧ x ≤ knot q K (i + n + 1) := by
  intro n
  induction n with
  | zero =>
    intro i h
    rw [bspl_one] at h
    split_ifs at h with hc
    · rcases hc with ⟨a, b⟩ | ⟨a, b, c⟩
      · exact ⟨a, b.le⟩
      · refine ⟨by linarith, ?_⟩
        rw [a, add_zero, c]
    · exact absurd rfl h
  | succ n ih =>
    intro i h
    rw [bspl_succ_succ] at h
    by_cases h1 : bspl q K (n + 1) i x = 0
    · have h2 : bspl q K (n + 1) (i + 1) x ≠ 0 := by
        intro h2
        rw [h1, h2] at h
        simp at h
      obtain ⟨a, b⟩ := ih (i + 1) h2
      have e : i + 1 + n + 1 = i + (n + 1) + 1 := by omega
      rw [e] at b
      exact ⟨le_trans (knot_mono q K (Nat.le_succ i)) a, b⟩
    · obtain ⟨a, b⟩ := ih i h1
      exact ⟨a, le_trans b (knot_mono q K (by omega))⟩

lemma bspl_support {q K k i : ℕ} {x : ℝ} (hk : 1 ≤ k) (h : bspl q K k i x ≠ 0) :
    knot q K i ≤ x ∧ x ≤ knot q K (i + k) := by
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
  exact bspl_support_aux q K x n i h

private lemma bspl_eq_zero_aux (q K : ℕ) (x : ℝ) :
    ∀ n i, knot q K i = knot q K (i + n + 1) → bspl q K (n + 1) i x = 0 := by
  intro n
  induction n with
  | zero =>
    intro i h
    rw [bspl_one, ite_eq_right]
    rw [add_zero] at h
    rintro (⟨a, b⟩ | ⟨-, b, c⟩)
    · linarith
    · linarith
  | succ n ih =>
    intro i h
    have m1 := knot_mono q K (show i ≤ i + n + 1 by omega)
    have m2 := knot_mono q K (show i + n + 1 ≤ i + (n + 1) + 1 by omega)
    have m3 := knot_mono q K (show i ≤ i + 1 by omega)
    have m4 := knot_mono q K (show i + 1 ≤ i + 1 + n + 1 by omega)
    have e : i + 1 + n + 1 = i + (n + 1) + 1 := by omega
    rw [e] at m4
    have h1 : bspl q K (n + 1) i x = 0 := ih i (by linarith)
    have h2 : bspl q K (n + 1) (i + 1) x = 0 := ih (i + 1) (by rw [e]; linarith)
    rw [bspl_succ_succ, h1, h2, mul_zero, mul_zero, add_zero]

lemma bspl_eq_zero_of_knot_eq {q K k i : ℕ} (hk : 1 ≤ k) (h : knot q K i = knot q K (i + k))
    (x : ℝ) : bspl q K k i x = 0 := by
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
  exact bspl_eq_zero_aux q K x n i h

lemma bspl_eq_zero_of_le {q K k i : ℕ} (hK : 1 ≤ K) (hk : 1 ≤ k) (hi : K + q ≤ i + 1)
    (x : ℝ) : bspl q K k i x = 0 := by
  apply bspl_eq_zero_of_knot_eq hk _ x
  rw [(knot_eq_one_iff hK).2 hi, (knot_eq_one_iff hK).2 (by omega)]

private lemma bspl_nonneg_aux (q K : ℕ) (x : ℝ) : ∀ n i, 0 ≤ bspl q K (n + 1) i x := by
  intro n
  induction n with
  | zero =>
    intro i
    rw [bspl_one]
    split_ifs <;> norm_num
  | succ n ih =>
    intro i
    rw [bspl_succ_succ]
    apply add_nonneg
    · by_cases h1 : bspl q K (n + 1) i x = 0
      · rw [h1, mul_zero]
      · obtain ⟨a, -⟩ := bspl_support (by omega) h1
        have m := knot_mono q K (show i ≤ i + n + 1 by omega)
        exact mul_nonneg (div_nonneg (by linarith) (by linarith)) (ih i)
    · by_cases h2 : bspl q K (n + 1) (i + 1) x = 0
      · rw [h2, mul_zero]
      · obtain ⟨-, b⟩ := bspl_support (by omega) h2
        have e : i + 1 + (n + 1) = i + n + 2 := by omega
        rw [e] at b
        have m := knot_mono q K (show i + 1 ≤ i + n + 2 by omega)
        exact mul_nonneg (div_nonneg (by linarith) (by linarith)) (ih (i + 1))

lemma bspl_nonneg (q K k i : ℕ) (x : ℝ) : 0 ≤ bspl q K k i x := by
  cases k with
  | zero => exact le_refl _
  | succ n => exact bspl_nonneg_aux q K x n i

/-! ## Partition of unity -/

/-- Order one, `x < 1`: `N₁(i,x) = 1{tᵢ ≤ x} − 1{tᵢ₊₁ ≤ x}`. -/
private lemma bspl_one_eq_sub_of_lt {q K i : ℕ} {x : ℝ} (hx : x < 1) :
    bspl q K 1 i x =
      (if knot q K i ≤ x then 1 else 0) - (if knot q K (i + 1) ≤ x then 1 else 0) := by
  have m := knot_mono q K (Nat.le_succ i)
  rw [bspl_one]
  by_cases ha : knot q K i ≤ x
  · by_cases hb : knot q K (i + 1) ≤ x
    · rw [ite_eq_right, ite_eq_left ha, ite_eq_left hb, sub_self]
      rintro (⟨-, h⟩ | ⟨h, -⟩) <;> linarith
    · rw [ite_eq_left (Or.inl ⟨ha, not_le.1 hb⟩), ite_eq_left ha, ite_eq_right hb, sub_zero]
  · have hb : ¬ knot q K (i + 1) ≤ x := fun hb => ha (le_trans m hb)
    rw [ite_eq_right, ite_eq_right ha, ite_eq_right hb, sub_zero]
    rintro (⟨h, -⟩ | ⟨h, -⟩)
    · exact ha h
    · linarith

/-- Order one, `x = 1`: `N₁(i,1) = 1{tᵢ < 1} − 1{tᵢ₊₁ < 1}`. -/
private lemma bspl_one_eq_sub_at_one {q K i : ℕ} :
    bspl q K 1 i 1 =
      (if knot q K i < 1 then 1 else 0) - (if knot q K (i + 1) < 1 then 1 else 0) := by
  have m := knot_mono q K (Nat.le_succ i)
  have l1 := knot_le_one q K (i + 1)
  rw [bspl_one]
  by_cases hb : knot q K (i + 1) < 1
  · have ha : knot q K i < 1 := lt_of_le_of_lt m hb
    rw [ite_eq_right, ite_eq_left ha, ite_eq_left hb, sub_self]
    rintro (⟨-, h⟩ | ⟨-, -, h⟩) <;> linarith
  · have hb1 : knot q K (i + 1) = 1 := le_antisymm l1 (not_lt.1 hb)
    by_cases ha : knot q K i < 1
    · rw [ite_eq_left (Or.inr ⟨rfl, ha, hb1⟩), ite_eq_left ha, ite_eq_right hb, sub_zero]
    · rw [ite_eq_right, ite_eq_right ha, ite_eq_right hb, sub_zero]
      rintro (⟨-, h⟩ | ⟨-, h, -⟩)
      · linarith
      · exact ha h

/-- Partition of unity at order one (telescoping). -/
private lemma bspl_sum_one {q K : ℕ} (hq : 1 ≤ q) (hK : 1 ≤ K) {x : ℝ}
    (hx : x ∈ Set.Icc (0 : ℝ) 1) : ∑ i ∈ range (K + q - 1), bspl q K 1 i x = 1 := by
  have h0 : knot q K 0 = 0 := knot_eq_zero (by omega)
  have hR : knot q K (K + q - 1) = 1 := (knot_eq_one_iff hK).2 (by omega)
  rcases hx.2.lt_or_eq with hlt | heq
  · rw [Finset.sum_congr rfl (fun i _ => @bspl_one_eq_sub_of_lt q K i x hlt)]
    refine (Finset.sum_range_sub' (fun i => if knot q K i ≤ x then (1 : ℝ) else 0) _).trans ?_
    show (if knot q K 0 ≤ x then (1 : ℝ) else 0) -
      (if knot q K (K + q - 1) ≤ x then 1 else 0) = 1
    rw [h0, hR, ite_eq_left hx.1, ite_eq_right (not_le.2 hlt), sub_zero]
  · subst heq
    rw [Finset.sum_congr rfl (fun i _ => @bspl_one_eq_sub_at_one q K i)]
    refine (Finset.sum_range_sub' (fun i => if knot q K i < 1 then (1 : ℝ) else 0) _).trans ?_
    show (if knot q K 0 < 1 then (1 : ℝ) else 0) -
      (if knot q K (K + q - 1) < 1 then 1 else 0) = 1
    rw [h0, hR, ite_eq_left zero_lt_one, ite_eq_right (lt_irrefl 1), sub_zero]

/-- `(ωᵢ + ω̄ᵢ) Nₖ(i,x) = Nₖ(i,x)`, including degenerate spans. -/
private lemma weight_mul_eq {q K m i : ℕ} (x : ℝ) :
    ((x - knot q K i) / (knot q K (i + m + 1) - knot q K i) +
      (knot q K (i + m + 1) - x) / (knot q K (i + m + 1) - knot q K i)) *
        bspl q K (m + 1) i x = bspl q K (m + 1) i x := by
  by_cases hd : knot q K (i + m + 1) - knot q K i = 0
  · rw [bspl_eq_zero_of_knot_eq (by omega) (by rw [← add_assoc]; linarith) x, mul_zero]
  · rw [← add_div, show x - knot q K i + (knot q K (i + m + 1) - x) =
      knot q K (i + m + 1) - knot q K i by ring, div_self hd, one_mul]

/-- Induction step of the partition of unity: `∑ N_{m+2}(i,x) = ∑ N_{m+1}(i,x)` for
`m + 2 ≤ q`. -/
private lemma bspl_sum_succ {q K m : ℕ} (hK : 1 ≤ K) (hm : m + 2 ≤ q) (x : ℝ) :
    ∑ i ∈ range (K + q - 1), bspl q K (m + 2) i x =
      ∑ i ∈ range (K + q - 1), bspl q K (m + 1) i x := by
  set R := K + q - 1 with hR
  have h0 : bspl q K (m + 1) 0 x = 0 := by
    apply bspl_eq_zero_of_knot_eq (by omega) _ x
    rw [knot_eq_zero (by omega), knot_eq_zero (by omega)]
  have hRz : bspl q K (m + 1) R x = 0 := bspl_eq_zero_of_le hK (by omega) (by omega) x
  have hshift : ∑ i ∈ range R, (knot q K (i + m + 2) - x) /
        (knot q K (i + m + 2) - knot q K (i + 1)) * bspl q K (m + 1) (i + 1) x =
      ∑ i ∈ range R, (knot q K (i + m + 1) - x) / (knot q K (i + m + 1) - knot q K i) *
        bspl q K (m + 1) i x := by
    have h1 := Finset.sum_range_succ' (fun j => (knot q K (j + m + 1) - x) /
      (knot q K (j + m + 1) - knot q K j) * bspl q K (m + 1) j x) R
    have h2 := Finset.sum_range_succ (fun j => (knot q K (j + m + 1) - x) /
      (knot q K (j + m + 1) - knot q K j) * bspl q K (m + 1) j x) R
    have e : ∀ i, i + 1 + m + 1 = i + m + 2 := fun i => by omega
    simp only [h0, hRz, mul_zero, add_zero, e] at h1 h2
    rw [← h1, h2]
  rw [Finset.sum_congr rfl (fun i _ => bspl_succ_succ q K m i x), Finset.sum_add_distrib, hshift,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [← add_mul]
  exact weight_mul_eq x

theorem bspl_sum_eq_one {q K k : ℕ} (hq : 1 ≤ q) (hK : 1 ≤ K) (hk1 : 1 ≤ k) (hkq : k ≤ q)
    {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    ∑ i ∈ range (K + q - 1), bspl q K k i x = 1 := by
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
  clear hk1
  induction n with
  | zero => exact bspl_sum_one hq hK hx
  | succ n ih => exact (bspl_sum_succ hK (by omega) x).trans (ih (by omega))

/-! ## B-splines lie in `[0, 1]` -/

lemma bspline_nonneg (q K i : ℕ) (x : ℝ) : 0 ≤ bspline q K i x := bspl_nonneg q K q i x

lemma bspline_le_one {q K : ℕ} (hq : 1 ≤ q) (hK : 1 ≤ K) (i : ℕ) {x : ℝ}
    (hx : x ∈ Set.Icc (0 : ℝ) 1) : bspline q K i x ≤ 1 := by
  unfold bspline
  by_cases hi : i < K + q - 1
  · rw [← bspl_sum_eq_one hq hK hq le_rfl hx]
    exact Finset.single_le_sum (f := fun j => bspl q K q j x)
      (fun j _ => bspl_nonneg q K q j x) (mem_range.2 hi)
  · rw [bspl_eq_zero_of_le hK hq (by omega) x]
    exact zero_le_one

lemma bsplineTensor_mem_Icc {d : ℕ} {q K : Fin d → ℕ} (hq : ∀ k, 1 ≤ q k) (hK : ∀ k, 1 ≤ K k)
    (i : Fin d → ℕ) {x : Fin d → ℝ} (hx : ∀ k, x k ∈ Set.Icc (0 : ℝ) 1) :
    bsplineTensor q K i x ∈ Set.Icc (0 : ℝ) 1 := by
  unfold bsplineTensor
  exact ⟨Finset.prod_nonneg fun k _ => bspline_nonneg _ _ _ _,
    Finset.prod_le_one₀ (fun k _ => bspline_nonneg _ _ _ _)
      (fun k _ => bspline_le_one (hq k) (hK k) (i k) (hx k))⟩

/-- **Assumption 1 for B-spline dictionaries**. -/
theorem bspline_basis : BSplineBasisStatement := by
  intro n J d q K i x hq hK hx
  apply basisBound_of_abs_le zero_le_one
  intro j m
  have h := bsplineTensor_mem_Icc (hq j) (hK j) (i j) (hx m)
  exact abs_le.2 ⟨by linarith [h.1], h.2⟩

end LargePrior
