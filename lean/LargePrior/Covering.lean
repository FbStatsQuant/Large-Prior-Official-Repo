import LargePrior.Packing

/-!
# Lemma 7: covering of the shells, indexed by coefficient vectors (blueprint `lem:covering`)
-/

open MeasureTheory ProbabilityTheory Filter Finset
open scoped ENNReal NNReal Topology Matrix

noncomputable section

namespace LargePrior

variable {n J : ℕ}

/-- The non-negligible part of `θ`: coordinates with `δ < |θ_j|`, the others set to `0`. -/
private def bigPart (δ : ℝ) (θ : Fin J → ℝ) : Fin J → ℝ := fun j => if δ < |θ j| then θ j else 0

/-- The non-negligible support `S(θ) = {j : δ < |θ_j|}`. -/
private def bigSet (δ : ℝ) (θ : Fin J → ℝ) : Finset (Fin J) := univ.filter (fun j => δ < |θ j|)

private lemma empNorm_eq_norm' (u : Fin n → ℝ) :
    empNorm u = ‖(WithLp.toLp 2 u : EuclideanSpace ℝ (Fin n))‖ / Real.sqrt n := by
  rw [empNorm, EuclideanSpace.norm_eq, Real.sqrt_div' _ (Nat.cast_nonneg n)]
  simp

/-- (i) The negligible part `X(θ − θ⁽¹⁾)` has empirical norm at most `M ε / 16`. -/
private lemma empNorm_small_part {X : Matrix (Fin n) (Fin J) ℝ} {K δ εt ε M : ℝ} (hK : 0 ≤ K)
    (hX : BasisBound X K) (hδ : 0 ≤ δ) (hδεt : δ ≤ εt / J) (hεt : 0 < εt) (hεtε : εt ≤ ε)
    (hMK : 16 * K ≤ M) (hJ : 0 < J) (θ : Fin J → ℝ) :
    empNorm (X *ᵥ θ - X *ᵥ bigPart δ θ) ≤ M * ε / 16 := by
  rw [← Matrix.mulVec_sub]
  refine (empNorm_mulVec_le hX _).trans ?_
  have h1 : ∀ j, |(θ - bigPart δ θ) j| ≤ δ := by
    intro j
    simp only [Pi.sub_apply, bigPart]
    split_ifs with h
    · simp [hδ]
    · simpa using (not_lt.1 h)
  have hJ' : (0 : ℝ) < J := by exact_mod_cast hJ
  have h2 : ∑ j, |(θ - bigPart δ θ) j| ≤ J * δ := by
    calc ∑ j, |(θ - bigPart δ θ) j| ≤ ∑ _j : Fin J, δ := Finset.sum_le_sum fun j _ => h1 j
      _ = J * δ := by simp
  have h3 : (J : ℝ) * δ ≤ εt := by
    rw [le_div_iff₀ hJ'] at hδεt; linarith
  have hε : 0 < ε := lt_of_lt_of_le hεt hεtε
  calc K * ∑ j, |(θ - bigPart δ θ) j| ≤ K * ε := by
        apply mul_le_mul_of_nonneg_left _ hK; linarith
    _ ≤ M * ε / 16 := by nlinarith

/-- (ii) Shell bounds for the non-negligible part. -/
private lemma shell_bigPart {X : Matrix (Fin n) (Fin J) ℝ} {f₀ : Fin n → ℝ} {δ ε M : ℝ}
    (hMε : 0 < M * ε) {ℓ : ℕ} (hℓ : 1 ≤ ℓ) {θ : Fin J → ℝ}
    (hs : empNorm (X *ᵥ θ - X *ᵥ bigPart δ θ) ≤ M * ε / 16)
    (h1 : (ℓ : ℝ) * M * ε < empNorm (X *ᵥ θ - f₀)) (h2 : empNorm (X *ᵥ θ - f₀) ≤ (ℓ + 1) * M * ε) :
    15 / 16 * ℓ * M * ε ≤ empNorm (X *ᵥ bigPart δ θ - f₀) ∧
      empNorm (X *ᵥ bigPart δ θ - f₀) ≤ (ℓ + 2) * M * ε := by
  have hℓ' : (1 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
  have ha := empNorm_sub_le (X *ᵥ θ) (X *ᵥ bigPart δ θ) f₀
  have hb := empNorm_sub_le (X *ᵥ bigPart δ θ) (X *ᵥ θ) f₀
  rw [empNorm_sub_comm (X *ᵥ bigPart δ θ) (X *ᵥ θ)] at hb
  have hℓMε : M * ε ≤ ℓ * (M * ε) := le_mul_of_one_le_left hMε.le hℓ'
  constructor
  · nlinarith
  · nlinarith

/-- The span `V_S` of the columns `X_{·j}`, `j ∈ S`, in `ℝⁿ` with the Euclidean norm. -/
private def colSpan (X : Matrix (Fin n) (Fin J) ℝ) (S : Finset (Fin J)) :
    Submodule ℝ (EuclideanSpace ℝ (Fin n)) :=
  Submodule.span ℝ
    ↑(S.image fun j => (WithLp.toLp 2 (fun i => X i j) : EuclideanSpace ℝ (Fin n)))

private lemma finrank_colSpan_le (X : Matrix (Fin n) (Fin J) ℝ) (S : Finset (Fin J)) :
    Module.finrank ℝ (colSpan X S) ≤ S.card :=
  (finrank_span_finset_le_card _).trans Finset.card_image_le

private lemma mem_colSpan {X : Matrix (Fin n) (Fin J) ℝ} {δ : ℝ} {θ : Fin J → ℝ}
    {S : Finset (Fin J)} (hS : bigSet δ θ ⊆ S) :
    (WithLp.toLp 2 (X *ᵥ bigPart δ θ) : EuclideanSpace ℝ (Fin n)) ∈ colSpan X S := by
  have hXθ : X *ᵥ bigPart δ θ = ∑ j, bigPart δ θ j • (fun i => X i j) := by
    funext i
    simp [Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]
  rw [hXθ, WithLp.toLp_sum]
  refine Submodule.sum_mem _ fun j _ => ?_
  rw [WithLp.toLp_smul]
  by_cases hj : j ∈ S
  · exact Submodule.smul_mem _ _ (Submodule.subset_span (Finset.mem_coe.2
      (Finset.mem_image_of_mem _ hj)))
  · have : bigPart δ θ j = 0 := by
      have hj' : j ∉ bigSet δ θ := fun h => hj (hS h)
      simp only [bigSet, Finset.mem_filter, Finset.mem_univ, true_and] at hj'
      simp [bigPart, hj']
    rw [this, zero_smul]
    exact Submodule.zero_mem _

/-- (iii) The per-support net: the non-negligible parts `Xθ⁽¹⁾ ∈ V_S` of the vectors `θ ∈ A`
lie within `√n (ℓ+2) M ε` of the projection of `f₀` onto `V_S`, so they have an
`√n ℓ M ε / 16`-net of at most `97^{|S|}` of their own points. -/
private lemma exists_support_net (hn : 0 < n) {X : Matrix (Fin n) (Fin J) ℝ} {f₀ : Fin n → ℝ}
    {δ ε M : ℝ} {ℓ : ℕ} (hℓ : 1 ≤ ℓ) (hMε : 0 < M * ε) (A : Set (Fin J → ℝ))
    (hA : ∀ θ ∈ A, empNorm (X *ᵥ bigPart δ θ - f₀) ≤ (ℓ + 2) * M * ε) (S : Finset (Fin J)) :
    ∃ G : Finset (colSpan X S),
      (∀ g ∈ G, ∃ θ ∈ A, (g : EuclideanSpace ℝ (Fin n)) = WithLp.toLp 2 (X *ᵥ bigPart δ θ)) ∧
      (G.card : ℝ) ≤ 97 ^ S.card ∧
      ∀ θ ∈ A, ∀ hθ : (WithLp.toLp 2 (X *ᵥ bigPart δ θ) : EuclideanSpace ℝ (Fin n)) ∈ colSpan X S,
        ∃ g ∈ G, dist (⟨_, hθ⟩ : colSpan X S) g ≤ Real.sqrt n * (ℓ * M * ε / 16) := by
  set V := colSpan X S
  have hsn : 0 < Real.sqrt n := Real.sqrt_pos.2 (by exact_mod_cast hn)
  have hℓ' : (1 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
  set F : Set V := {z | ∃ θ ∈ A, (z : EuclideanSpace ℝ (Fin n)) = WithLp.toLp 2 (X *ᵥ bigPart δ θ)}
  set x : V := V.orthogonalProjectionOnto (WithLp.toLp 2 f₀)
  have hR : 0 < Real.sqrt n * ((ℓ + 2) * M * ε) := by
    have : 0 < ((ℓ : ℝ) + 2) * M * ε := by rw [mul_assoc]; positivity
    positivity
  have hr : 0 < Real.sqrt n * (ℓ * M * ε / 16) := by
    have : 0 < (ℓ : ℝ) * M * ε := by rw [mul_assoc]; positivity
    positivity
  have hF : ∀ z ∈ F, dist z x ≤ Real.sqrt n * ((ℓ + 2) * M * ε) := by
    rintro z ⟨θ, hθA, hz⟩
    have hzP : V.orthogonalProjectionOnto (z : EuclideanSpace ℝ (Fin n)) = z :=
      Submodule.orthogonalProjectionOnto_mem_subspace_eq_self z
    rw [dist_eq_norm, ← hzP, ← map_sub]
    refine (Submodule.norm_orthogonalProjectionOnto_apply_le _ _).trans ?_
    have h := hA θ hθA
    rw [empNorm_eq_norm', div_le_iff₀ hsn, WithLp.toLp_sub, ← hz] at h
    linarith
  obtain ⟨G, hGF, hGcard, hGnet⟩ := exists_net x hR hr F hF
  refine ⟨G, fun g hg => hGF hg, ?_, ?_⟩
  · refine hGcard.trans ?_
    have h96 : 2 * (Real.sqrt n * ((ℓ + 2) * M * ε)) / (Real.sqrt n * (ℓ * M * ε / 16)) ≤ 96 := by
      rw [div_le_iff₀ hr]
      have : 0 < Real.sqrt n * (M * ε) := by positivity
      nlinarith
    have h0 : 0 ≤ 2 * (Real.sqrt n * ((ℓ + 2) * M * ε)) / (Real.sqrt n * (ℓ * M * ε / 16)) := by
      positivity
    calc (1 + 2 * (Real.sqrt n * ((ℓ + 2) * M * ε)) / (Real.sqrt n * (ℓ * M * ε / 16))) ^
          Module.finrank ℝ V ≤ (97 : ℝ) ^ Module.finrank ℝ V :=
          pow_le_pow_left₀ (by linarith) (by linarith) _
      _ ≤ 97 ^ S.card := pow_le_pow_right₀ (by norm_num) (finrank_colSpan_le X S)
  · intro θ hθA hθ
    exact hGnet _ ⟨θ, hθA, rfl⟩

/-- (iv) The number of supports of size at most `m` is at most `(m+1) J^m`. -/
private lemma card_small_supports (hJ : 1 ≤ J) (m : ℕ) :
    ((univ : Finset (Finset (Fin J))).filter (fun S => S.card ≤ m)).card ≤ (m + 1) * J ^ m := by
  have hsub : (univ : Finset (Finset (Fin J))).filter (fun S => S.card ≤ m) ⊆
      (range (m + 1)).biUnion (fun k => powersetCard k (univ : Finset (Fin J))) := by
    intro S hS
    simp only [mem_filter, mem_univ, true_and] at hS
    simp only [mem_biUnion, mem_range, mem_powersetCard]
    exact ⟨S.card, by omega, subset_univ _, rfl⟩
  calc _ ≤ _ := card_le_card hsub
    _ ≤ ∑ k ∈ range (m + 1), (powersetCard k (univ : Finset (Fin J))).card := card_biUnion_le
    _ ≤ ∑ _k ∈ range (m + 1), J ^ m := by
        apply sum_le_sum
        intro k hk
        rw [card_powersetCard, card_univ, Fintype.card_fin]
        exact (Nat.choose_le_pow _ _).trans
          (Nat.pow_le_pow_right hJ (Nat.lt_succ_iff.1 (mem_range.1 hk)))
    _ = (m + 1) * J ^ m := by simp

/-- (iv) `J ≥ 194` under `1 + log 97 ≤ log J`. -/
private lemma le_J_of_log (hJ : 2 ≤ J) (hJ97 : 1 + Real.log 97 ≤ Real.log J) : 194 ≤ J := by
  have hJpos : (0 : ℝ) < J := by exact_mod_cast (by omega : 0 < J)
  have h1 : Real.exp (1 + Real.log 97) ≤ J := by
    rw [← Real.exp_log hJpos]
    exact Real.exp_le_exp.2 hJ97
  rw [Real.exp_add, Real.exp_log (by norm_num)] at h1
  have h2 := Real.exp_one_gt_d9
  have : (194 : ℝ) ≤ J := by nlinarith
  exact_mod_cast this

/-- (iv) Arithmetic: `(m+1) J^m 97^m ≤ J^{2m}` once `J ≥ 194`. -/
private lemma count_le (hJ : 194 ≤ J) (m : ℕ) : (m + 1) * J ^ m * 97 ^ m ≤ J ^ (2 * m) := by
  have h1 : m + 1 ≤ 2 ^ m := Nat.lt_two_pow_self
  have h2 : (m + 1) * 97 ^ m ≤ J ^ m :=
    calc (m + 1) * 97 ^ m ≤ 2 ^ m * 97 ^ m := Nat.mul_le_mul_right _ h1
      _ = 194 ^ m := by rw [← mul_pow]; norm_num
      _ ≤ J ^ m := Nat.pow_le_pow_left hJ m
  calc (m + 1) * J ^ m * 97 ^ m = (m + 1) * 97 ^ m * J ^ m := by ring
    _ ≤ J ^ m * J ^ m := Nat.mul_le_mul_right _ h2
    _ = J ^ (2 * m) := by ring

/-- **Lemma 7**: for the `ℓ`-th shell `ℓ M ε < ‖Xθ − f₀‖_{2,n} ≤ (ℓ+1) M ε` of coefficient vectors
with at most `m` non-negligible coordinates, there are at most `exp(2 m log J)` centres, each at
distance at least `(15/16) ℓ M ε` from `f₀`, such that every such `Xθ` is within `ℓ M ε / 8` of a
centre. -/
theorem covering (hn : 0 < n) (hJ : 2 ≤ J) {X : Matrix (Fin n) (Fin J) ℝ} {f₀ : Fin n → ℝ}
    {K δ εt ε M : ℝ} (m : ℕ) (hK : 0 ≤ K) (hX : BasisBound X K) (hδ : 0 ≤ δ)
    (hδεt : δ ≤ εt / J) (hεt : 0 < εt) (hεtε : εt ≤ ε) (hM : 0 < M) (hMK : 16 * K ≤ M)
    (hJ97 : 1 + Real.log 97 ≤ Real.log J) (hm : 1 ≤ m) (ℓ : ℕ) (hℓ : 1 ≤ ℓ) :
    ∃ G : Finset (Fin n → ℝ), (G.card : ℝ) ≤ Real.exp (2 * m * Real.log J) ∧
      (∀ g ∈ G, 15 / 16 * ℓ * M * ε ≤ empNorm (g - f₀)) ∧
      ∀ θ : Fin J → ℝ, numLarge δ θ ≤ m → (ℓ : ℝ) * M * ε < empNorm (X *ᵥ θ - f₀) →
        empNorm (X *ᵥ θ - f₀) ≤ (ℓ + 1) * M * ε →
          ∃ g ∈ G, empNorm (X *ᵥ θ - g) ≤ ℓ * M * ε / 8 := by
  classical
  -- `hm` (part of the frozen statement) is not needed: the construction works for every `m`.
  have _ := hm
  have hJpos : 0 < J := by omega
  have hε : 0 < ε := lt_of_lt_of_le hεt hεtε
  have hMε : 0 < M * ε := mul_pos hM hε
  have hsn : 0 < Real.sqrt n := Real.sqrt_pos.2 (by exact_mod_cast hn)
  have hℓ' : (1 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
  set A : Set (Fin J → ℝ) := {θ | (ℓ : ℝ) * M * ε < empNorm (X *ᵥ θ - f₀) ∧
    empNorm (X *ᵥ θ - f₀) ≤ (ℓ + 1) * M * ε} with hAdef
  have hsmall := fun θ => empNorm_small_part hK hX hδ hδεt hεt hεtε hMK hJpos θ
  have hshell : ∀ θ ∈ A, 15 / 16 * ℓ * M * ε ≤ empNorm (X *ᵥ bigPart δ θ - f₀) ∧
      empNorm (X *ᵥ bigPart δ θ - f₀) ≤ (ℓ + 2) * M * ε :=
    fun θ hθ => shell_bigPart hMε hℓ (hsmall θ) hθ.1 hθ.2
  have hnet := fun S => exists_support_net hn hℓ hMε A (fun θ hθ => (hshell θ hθ).2) S
  choose Gs hGsA hGscard hGsnet using hnet
  set Sset := (univ : Finset (Finset (Fin J))).filter (fun S => S.card ≤ m) with hSset
  refine ⟨Sset.biUnion (fun S => (Gs S).image
    (fun g : colSpan X S => WithLp.ofLp (g : EuclideanSpace ℝ (Fin n)))), ?_, ?_, ?_⟩
  · -- cardinality
    have hGs' : ∀ S, (Gs S).card ≤ 97 ^ S.card := fun S => by exact_mod_cast hGscard S
    have hcardN : (Sset.biUnion (fun S => (Gs S).image
        (fun g : colSpan X S => WithLp.ofLp (g : EuclideanSpace ℝ (Fin n))))).card ≤
          J ^ (2 * m) := by
      calc _ ≤ ∑ S ∈ Sset, ((Gs S).image
              (fun g : colSpan X S => WithLp.ofLp (g : EuclideanSpace ℝ (Fin n)))).card :=
            card_biUnion_le
        _ ≤ ∑ _S ∈ Sset, 97 ^ m := by
            refine sum_le_sum fun S hS => ?_
            have hS' : S.card ≤ m := (mem_filter.1 hS).2
            exact card_image_le.trans ((hGs' S).trans (Nat.pow_le_pow_right (by norm_num) hS'))
        _ = Sset.card * 97 ^ m := by rw [sum_const, smul_eq_mul]
        _ ≤ (m + 1) * J ^ m * 97 ^ m :=
            Nat.mul_le_mul_right _ (card_small_supports (by omega) m)
        _ ≤ J ^ (2 * m) := count_le (le_J_of_log hJ hJ97) m
    have hexp : Real.exp (2 * m * Real.log J) = (J : ℝ) ^ (2 * m) := by
      rw [show (2 * m * Real.log J : ℝ) = ((2 * m : ℕ) : ℝ) * Real.log J by push_cast; ring,
        Real.exp_nat_mul, Real.exp_log (by exact_mod_cast hJpos)]
    rw [hexp]
    exact_mod_cast hcardN
  · -- centres are far from `f₀`
    intro g hg
    obtain ⟨S, -, hgS⟩ := mem_biUnion.1 hg
    obtain ⟨g', hg', rfl⟩ := mem_image.1 hgS
    obtain ⟨θ, hθA, hθ⟩ := hGsA S g' hg'
    rw [hθ]
    exact (hshell θ hθA).1
  · -- covering
    intro θ hθm h1 h2
    have hθA : θ ∈ A := ⟨h1, h2⟩
    have hmem := mem_colSpan (X := X) (subset_refl (bigSet δ θ))
    obtain ⟨g', hg', hdist⟩ := hGsnet (bigSet δ θ) θ hθA hmem
    refine ⟨WithLp.ofLp (g' : EuclideanSpace ℝ (Fin n)), mem_biUnion.2 ⟨bigSet δ θ, ?_,
      mem_image.2 ⟨g', hg', rfl⟩⟩, ?_⟩
    · exact mem_filter.2 ⟨mem_univ _, hθm⟩
    · have hd : empNorm (X *ᵥ bigPart δ θ - WithLp.ofLp (g' : EuclideanSpace ℝ (Fin n))) =
          dist (⟨_, hmem⟩ : colSpan X (bigSet δ θ)) g' / Real.sqrt n := by
        rw [empNorm_eq_norm', dist_eq_norm, ← Submodule.norm_coe]
        rfl
      have hd' : empNorm (X *ᵥ bigPart δ θ - WithLp.ofLp (g' : EuclideanSpace ℝ (Fin n))) ≤
          ℓ * M * ε / 16 := by
        rw [hd, div_le_iff₀ hsn]
        linarith
      have := empNorm_sub_le (X *ᵥ θ) (X *ᵥ bigPart δ θ)
        (WithLp.ofLp (g' : EuclideanSpace ℝ (Fin n)))
      have hs := hsmall θ
      have hℓMε : M * ε ≤ ℓ * (M * ε) := le_mul_of_one_le_left hMε.le hℓ'
      nlinarith

end LargePrior
